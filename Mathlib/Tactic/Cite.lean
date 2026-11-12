/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public meta import ImportGraph.Lean.Environment  -- shake: keep (Environment.getModuleFor? is used from public meta code), cf. lean#14427
public meta import Lean.Data.Json
public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# Citations

A *source* is a work that declarations cite: a book, an article, or a web database such as the
[OEIS](https://oeis.org/). A *citation* records that a declaration formalizes one of its entries.

* `cite_source` declares a source, with a title, the address of its entries and the
  [Literature Links](https://github.com/mathlib-initiative/literature-links) type of the ends made
  from it:
  ```
  /-- An online database of integer sequences. -/
  cite_source oeis "The On-Line Encyclopedia of Integer Sequences"
    (uri := "https://oeis.org/{id}")
  ```
  A source is declared in Lean, rather than read from a data file, so that Lake knows which
  modules depend on it.
* `@[cite oeis "A000045" (rel := exactMatch) "the Fibonacci numbers"]` records that the
  declaration it tags formalizes the entry `A000045` of that source.

Both are kept in persistent environment extensions, read by `Mathlib.Cite.sources` and
`Mathlib.Cite.citations`. `Mathlib.Cite.Citation.annotation?` turns a citation into a Literature
Links annotation, which `scripts/export_citations.lean` writes out.

This file is independent of the cross-reference databases: `Mathlib/Tactic/CrossRefAttribute.lean`
declares each of them as a source and makes every cross-reference attribute record a citation of
it, so that `@[cite stacks "0BR2"]` and `@[stacks 0BR2]` record the same entry.
-/

public meta section

open Lean Elab Command

namespace Mathlib.Cite

/-! ### Sources -/

/-- The [Literature Links](https://github.com/mathlib-initiative/literature-links) relations that
a citation can state: how the cited entry relates to the declaration citing it. -/
def relations : List String :=
  ["exactMatch", "closeMatch", "broadMatch", "narrowMatch", "relatedMatch", "hasPart", "noMatch"]

/-- The Literature Links types of an end: the kind of document that holds it. -/
def endTypes : List String := ["pdf", "latex", "html", "lean", "generic"]

/-- A work that declarations cite, declared by `cite_source`. -/
structure Source where
  /-- The name that citations use, such as `oeis`. -/
  name : Name
  /-- A readable title, such as `The On-Line Encyclopedia of Integer Sequences`. -/
  title : String
  /-- The addresses of the source's entries: templates keyed by a prefix of the entry's
  identifier, the longest matching key winning, where `""` matches every entry and `{id}` in a
  template stands for the identifier. A template without `{id}` is the source's own address,
  which all of its entries then share. `cite_source` sets the single key `""`; a database whose
  entries live on different pages, such as π-Base, registers one template per kind. -/
  uriTemplates : Array (String × String)
  /-- The Literature Links type of the ends made from the source, one of `endTypes`. -/
  type : String
  /-- The source's docstring, shown on hovering over its name in a citation. -/
  doc : String := ""
  /-- The module that declared the source. -/
  module : Name := .anonymous
  deriving Inhabited, Repr

/-- `template` with every `{id}` replaced by `id`. -/
def fillTemplate (template id : String) : String :=
  id.intercalate (template.splitOn "{id}")

/-- `id` percent-encoded, so that it can stand in a URI: the unreserved characters
`A-Za-z0-9-._~` are kept and every other character becomes `%` followed by the uppercase
hexadecimal of each of its UTF-8 bytes. -/
def percentEncode (id : String) : String :=
  id.foldl (init := "") fun out c =>
    if c.isAlphanum || "-._~".contains c then out.push c
    else c.toString.toUTF8.foldl (init := out) fun out b =>
      let digit n : Char := Char.ofNat <| if n < 10 then '0'.toNat + n else 'A'.toNat + n - 10
      out.push '%' |>.push (digit (b.toNat / 16)) |>.push (digit (b.toNat % 16))

/-- The address of the entry `id` under the templates `uri`, as `Source.uriTemplates` keeps them:
the template of the longest key that is a prefix of `id`, with `{id}` replaced by the
percent-encoded `id`. -/
def entryUri (uri : Array (String × String)) (id : String) : String :=
  let best := uri.foldl (init := none) fun best (prefix', template) =>
    if id.startsWith prefix' && best.all (·.1.length < prefix'.length) then
      some (prefix', template)
    else best
  fillTemplate ((best.map (·.2)).getD "") (percentEncode id)

/-- The address of the entry `id` of the source `s`: see `Mathlib.Cite.entryUri`. -/
def Source.entryUri (s : Source) (id : String) : String :=
  _root_.Mathlib.Cite.entryUri s.uriTemplates id

/-- Markdown describing the source, shown on hovering over its name in a citation. -/
def Source.hover (s : Source) : String :=
  "\n\n".intercalate <| [s!"**{s.title}**"] ++ (if s.doc.isEmpty then [] else [s.doc])

/-- Add the source `s` to a registry of sources by name. -/
def addSourceDecl (registry : NameMap (Array Source)) (s : Source) : NameMap (Array Source) :=
  registry.insert s.name (((registry.find? s.name).getD #[]).push s)

/-- The environment extension storing the declared sources, by name.
Unlike `Mathlib.Cite.citeExt` and `Mathlib.CrossRef.tagExt`, which are read in bulk and only by
the export, this extension is read on every `@[cite]`, so it builds a map at initialization —
cheap, as a source is declared once per database rather than once per declaration. -/
initialize sourceExt : SimplePersistentEnvExtension Source (NameMap (Array Source)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries addSourceDecl {}
    addEntryFn := addSourceDecl
  }

/-- The declarations of the source named `name`: none, one, or several when two modules that do
not import one another declare the same name. -/
def sourceDecls (env : Environment) (name : Name) : Array Source :=
  ((sourceExt.getState env).find? name).getD #[]

/-- Every declared source, those of the imported modules and those of the current one, ordered
by name. -/
def sources (env : Environment) : Array Source :=
  (sourceExt.getState env).toArray.flatMap (·.2) |>.qsort (·.name.lt ·.name)

/-- The source named `name`, declared in the current module or in an imported one, or a message
saying why there is none. -/
def findSource (env : Environment) (name : Name) : Except MessageData Source :=
  match sourceDecls env name with
  | #[s] => .ok s
  | #[] => .error m!"unknown source `{name}`; declare it with `cite_source`"
  | ss => .error m!"the source `{name}` is declared in several modules: \
      {", ".intercalate (ss.toList.map (·.module.toString))}"

/-- Declare `s` as a source of the current module, unless its name is already taken. -/
def addSource {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (s : Source) : m Unit := do
  if let some old := (sourceDecls (← getEnv) s.name)[0]? then
    throwError "the source `{s.name}` is already declared, in module `{old.module}`"
  modifyEnv (sourceExt.addEntry · { s with module := (← getEnv).mainModule })

/-! ### Citations -/

/-- A citation: the declaration `declName` formalizes an entry of a source. -/
structure Citation where
  /-- The declaration that cites the entry. -/
  declName : Name
  /-- The name of the cited source. -/
  source : Name
  /-- The cited entry of the source, such as `A000045`. -/
  id : String
  /-- How the entry relates to the declaration: one of `relations`, or empty when not stated. -/
  rel : String := ""
  /-- A comment supplied with the citation, or empty. -/
  comment : String := ""
  /-- The address of the entry, resolved when the citation was recorded. -/
  url : String := ""
  deriving Inhabited, Repr, BEq

/-- The environment extension storing all citations.
`addImportedFn` is a constant function to avoid a performance overhead during initialization,
as for `Mathlib.CrossRef.tagExt`. -/
initialize citeExt : SimplePersistentEnvExtension Citation (Array (Array Citation)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn citations := citations
    addEntryFn citations _ := citations
  }

/-- Every citation: those of the imported modules, then those of the current one, in the order in
which they were recorded. -/
def citations (env : Environment) : Array Citation :=
  let (currentModule, imported) := PersistentEnvExtension.getState citeExt env
  imported.flatten ++ currentModule.reverse.toArray

/-- Record the citation `c` in the current module. -/
def addCitation {m : Type → Type} [MonadEnv m] (c : Citation) : m Unit :=
  modifyEnv (citeExt.addEntry · c)

/-! ### Literature Links annotations -/

/-- Mathlib's repository, the address of the Lean end of an annotation. -/
def mathlibRepo : String := "https://github.com/leanprover-community/mathlib4"

/-- Can `key` be a key of a Literature Links `identifiers` object? It must be non-empty and avoid
the whitespace, control and invisible characters that the specification's key pattern excludes. -/
def isIdentifiersKey (key : String) : Bool :=
  !key.isEmpty && key.all fun c =>
    let n := c.toNat
    !(n ≤ 0x20 || (0x7f ≤ n && n ≤ 0xa0) || n == 0x61c || n == 0x1680 ||
      (0x2000 ≤ n && n ≤ 0x200f) || (0x2028 ≤ n && n ≤ 0x202f) ||
      (0x205f ≤ n && n ≤ 0x206f) || n == 0x3000 || n == 0xfeff || n == 0xfffe || n == 0xffff)

/-- The [Literature Links](https://github.com/mathlib-initiative/literature-links) annotation for
the citation `c`, at commit `commit` of the repository `repo`: the source's entry is the subject,
the declaration the object. It is `none` when the source of `c` is not declared. -/
def Citation.annotation? (env : Environment) (c : Citation) (commit : String)
    (repo : String := mathlibRepo) : Option Json := do
  let source ← (findSource env c.source).toOption
  let key := source.name.toString (escape := false)
  let subject := Json.mkObj <|
    [("type", toJson source.type), ("uri", toJson c.url),
      ("title", toJson s!"{source.title} {c.id}")] ++
    (if isIdentifiersKey key then [("identifiers", Json.mkObj [(key, toJson c.id)])] else [])
  let declName := (privateToUserName? c.declName).getD c.declName
  let location := Json.mkObj <| [("declaration", toJson declName.toString)] ++
    ((env.getModuleFor? c.declName).map fun m =>
      ("module", toJson (m.toString (escape := false)))).toList
  let object := Json.mkObj
    [("type", toJson "lean"), ("uri", toJson repo), ("version", toJson commit),
      ("location", location)]
  return Json.mkObj <|
    [("id", toJson s!"{key}:{c.id}")] ++
    (if c.comment.isEmpty then [] else [("note", toJson c.comment)]) ++
    (if c.rel.isEmpty then [] else [("relation", toJson c.rel)]) ++
    [("subject", Json.arr #[subject]), ("object", Json.arr #[object])]

/-! ### The `cite_source` command -/

/-- A field of a source: `(uri := "https://oeis.org/{id}")`. -/
syntax citeSourceField := "(" ident " := " str ")"

/-- `cite_source oeis "The On-Line Encyclopedia of Integer Sequences"
(uri := "https://oeis.org/{id}")` declares a source that declarations can cite with `@[cite]`.

The field `uri` is the address of the source's entries: a template in which `{id}` stands for the
entry's identifier, or a fixed address shared by all of them. The field `type` is the Literature
Links type of the ends made from the source, one of `Mathlib.Cite.endTypes`; it defaults to `html`
for a template and to `generic` for a fixed address. A docstring describes the source and is shown
on hovering over its name in a citation.

The name of a source must not be taken by another source already. -/
syntax (name := citeSource) (docComment)? "cite_source " Lean.Parser.rawIdent ppSpace str
  (ppSpace citeSourceField)* : command

/-- Elaborate `cite_source`: read the fields and declare the source. -/
@[command_elab citeSource]
def elabCiteSource : CommandElab
  | `(command| $[$doc]? cite_source $name:ident $title:str $fields*) => do
    let mut uri? : Option String := none
    let mut type? : Option String := none
    for field in fields do
      let `(citeSourceField| ($key:ident := $value:str)) := field | throwUnsupportedSyntax
      match key.getId.eraseMacroScopes.toString with
      | "uri" =>
        if uri?.isSome then throwErrorAt key "the field `uri` is given twice"
        uri? := some value.getString
      | "type" =>
        if type?.isSome then throwErrorAt key "the field `type` is given twice"
        unless endTypes.contains value.getString do
          throwErrorAt value "unknown type `{value.getString}`; \
            the types are {", ".intercalate endTypes}"
        type? := some value.getString
      | other =>
        throwErrorAt key "unknown field `{other}` of `cite_source`; \
          the fields are `uri` and `type`"
    let some uri := uri? | throwError "a source needs an address: `(uri := \"https://…\")`"
    withRef name <| addSource {
      name := name.getId.eraseMacroScopes
      title := title.getString
      uriTemplates := #[("", uri)]
      type := type?.getD (if (uri.splitOn "{id}").length > 1 then "html" else "generic")
      doc := (← doc.mapM getDocStringText).getD "" |>.trimAscii.toString }
  | _ => throwUnsupportedSyntax

/-! ### The `cite` attribute -/

/-- The relation of a citation: `(rel := exactMatch)`. -/
syntax citeRel := "(" &"rel" " := " ident ")"

/-- `@[cite src "id"]` records that the declaration formalizes the entry `id` of the source `src`,
which `cite_source` declared. A relation and a comment may follow the entry:
`@[cite stacks "0BR2" (rel := closeMatch) "up to a choice of base point"]`. The relations are
`exactMatch`, `closeMatch`, `broadMatch`, `narrowMatch`, `relatedMatch`, `hasPart` and `noMatch`,
those of [Literature Links](https://github.com/mathlib-initiative/literature-links).

The source is read as a name even when it is a keyword, as `stacks` is. Unlike the
cross-reference attributes of `Mathlib/Tactic/CrossRefAttribute.lean`, `@[cite]` leaves the
declaration's docstring alone; its links come from `scripts/export_citations.lean`. -/
syntax (name := cite) &"cite" ppSpace Lean.Parser.rawIdent ppSpace str (ppSpace citeRel)?
  (ppSpace str)? : attr

/-- Show `text`, as Markdown, on hovering over `stx`. -/
def addHover {m : Type → Type} [Monad m] [MonadInfoTree m] (stx : Syntax) (text : String) :
    m Unit :=
  pushInfoLeaf <| .ofDelabTermInfo {
    elaborator := .anonymous, stx, lctx := .empty, expectedType? := none, expr := mkStrLit text,
    mkDocString? := some fun _ => pure text }

initialize registerBuiltinAttribute {
  name := `cite
  descr := "Record that a declaration formalizes an entry of a source declared with `cite_source`."
  add decl stx attrKind := do
    unless attrKind == .global do
      throwError "`cite` is a global attribute; it cannot be local or scoped"
    let `(attr| cite $src:ident $id:str $[$rel:citeRel]? $[$comment:str]?) := stx
      | throwUnsupportedSyntax
    let source ← match findSource (← getEnv) src.getId.eraseMacroScopes with
      | .ok source => pure source
      | .error msg => throwErrorAt src msg
    addHover src source.hover
    if id.getString.all Char.isWhitespace then
      throwErrorAt id "the cited entry cannot be empty"
    let rel ← match rel with
      | none => pure ""
      | some rel =>
        let `(citeRel| (rel := $name:ident)) := rel | throwUnsupportedSyntax
        let rel := name.getId.eraseMacroScopes.toString
        unless relations.contains rel do
          throwErrorAt name "unknown relation `{rel}`; \
            the relations are {", ".intercalate relations}"
        pure rel
    addCitation {
      declName := decl, source := source.name, id := id.getString, rel := rel
      comment := (comment.map (·.getString)).getD "", url := source.entryUri id.getString }
}

end Mathlib.Cite
