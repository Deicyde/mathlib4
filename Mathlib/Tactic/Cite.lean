/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# Citations

A *source* is a work that declarations cite: a book, an article, or a web database such as the
[OEIS](https://oeis.org/). A *citation* records that a declaration formalizes one of its entries.

* `cite_source` declares a source, with a title, the address of its entries, any further fields
  that an export may want, and optionally a docstring:
  ```
  cite_source oeis "The On-Line Encyclopedia of Integer Sequences"
    (uri := "https://oeis.org/{id}")
  ```
  A source is declared in Lean, rather than read from a data file, so that Lake knows which
  modules depend on it.
* `@[cite oeis "A000045" (rel := exactMatch) "the Fibonacci numbers"]` records that the
  declaration it tags formalizes the entry `A000045` of that source.

Both are kept in persistent environment extensions, read by `Mathlib.Cite.sources` and
`Mathlib.Cite.citations`, from which an export can write them out in the format it wants.

This file is independent of the cross-reference databases: `Mathlib/Tactic/CrossRefAttribute.lean`
declares each of them as a source and makes every cross-reference attribute record a citation of
it, so that `@[cite stacks "0BR2"]` and `@[stacks 0BR2]` record the same entry.
-/

public meta section

open Lean Elab Command

namespace Mathlib.Cite

/-! ### Sources -/

/-- The relations that a citation can state: how the cited entry relates to the declaration
citing it. They are the mapping relations of
[SKOS](https://www.w3.org/TR/skos-reference/#mapping) — `exactMatch`, `closeMatch`, `broadMatch`,
`narrowMatch` and `relatedMatch` — together with `hasPart`, for a declaration that formalizes a
part of the entry, and `noMatch`. -/
def relations : List String :=
  ["exactMatch", "closeMatch", "broadMatch", "narrowMatch", "relatedMatch", "hasPart", "noMatch"]

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
  /-- The source's other fields, as `cite_source` was given them, such as `("type", "pdf")`:
  free-form data, which the exports read and this file does not interpret. -/
  fields : Array (String × String) := #[]
  /-- The source's docstring, shown on hovering over its name in a citation. -/
  doc : String := ""
  /-- The module that declared the source. -/
  module : Name := .anonymous
  deriving Inhabited, Repr

/-- The value of the source's field `key`, when it has one. -/
def Source.field? (s : Source) (key : String) : Option String :=
  (s.fields.find? (·.1 == key)).map (·.2)

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

/-! ### The `cite_source` command -/

/-- A field of a source: `(uri := "https://oeis.org/{id}")`. -/
syntax citeSourceField := "(" ident " := " str ")"

/-- `cite_source oeis "The On-Line Encyclopedia of Integer Sequences"
(uri := "https://oeis.org/{id}")` declares a source that declarations can cite with `@[cite]`.

The field `uri` is the address of the source's entries: a template in which `{id}` stands for the
entry's identifier, or a fixed address shared by all of them. The other fields are free-form and
kept on the source for the exports to read, such as `(type := "pdf")` for the kind of document
the source is. No field may be given twice. A docstring describes the source and is shown on
hovering over its name in a citation.

The name of a source must not be taken by another source already. -/
syntax (name := citeSource) (docComment)? "cite_source " Lean.Parser.rawIdent ppSpace str
  (ppSpace citeSourceField)* : command

/-- Elaborate `cite_source`: read the fields and declare the source. -/
@[command_elab citeSource]
def elabCiteSource : CommandElab
  | `(command| $[$doc]? cite_source $name:ident $title:str $fields*) => do
    let mut uri? : Option String := none
    let mut rest : Array (String × String) := #[]
    for field in fields do
      let `(citeSourceField| ($key:ident := $value:str)) := field | throwUnsupportedSyntax
      let keyName := key.getId.eraseMacroScopes.toString
      if (keyName == "uri" && uri?.isSome) || rest.any (·.1 == keyName) then
        throwErrorAt key "the field `{keyName}` is given twice"
      if keyName == "uri" then uri? := some value.getString
      else rest := rest.push (keyName, value.getString)
    let some uri := uri? | throwError "a source needs an address: `(uri := \"https://…\")`"
    withRef name <| addSource {
      name := name.getId.eraseMacroScopes
      title := title.getString
      uriTemplates := #[("", uri)]
      fields := rest
      doc := (← doc.mapM getDocStringText).getD "" |>.trimAscii.toString }
  | _ => throwUnsupportedSyntax

/-! ### The `cite` attribute -/

/-- The relation of a citation: `(rel := exactMatch)`. -/
syntax citeRel := "(" &"rel" " := " ident ")"

/-- `@[cite src "id"]` records that the declaration formalizes the entry `id` of the source `src`,
which `cite_source` declared. A relation and a comment may follow the entry:
`@[cite stacks "0BR2" (rel := closeMatch) "up to a choice of base point"]`. The relations are
those of `Mathlib.Cite.relations`: `exactMatch`, `closeMatch`, `broadMatch`, `narrowMatch`,
`relatedMatch`, `hasPart` and `noMatch`.

The source is read as a name even when it is a keyword, as `stacks` is. Unlike the
cross-reference attributes of `Mathlib/Tactic/CrossRefAttribute.lean`, `@[cite]` leaves the
declaration's docstring alone; its links come from the exports. -/
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
