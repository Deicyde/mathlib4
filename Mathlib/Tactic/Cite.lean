/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public meta import Lean.Elab.Command
public meta import Mathlib.Util.VersoRoles
public import Mathlib.Init

/-!
# Citations

A *citation* records that a declaration formalizes a work, or an entry or a part of one. The cited
*source* is of one of two kinds: a source declared in Lean with `cite_source`, such as a web
database whose entries have identifiers and addresses of their own, or an entry of the project's
BibTeX file, named by its key. Sources and citations are kept in environment extensions, read by
`sources` and `citations`, from which an export can write them out.

* `cite_source name "title" (uri := "…{id}…") (key := "value")*` declares a source, optionally
  with a docstring. In the address `uri`, `{id}` stands for the entry's percent-encoded identifier;
  without `{id}`, all entries share the address. The docstring and the other fields, such as
  `(type := "pdf")`, are kept for exports; the fields are free-form, and none may be given twice.
  Sources are declared in Lean, rather than read from a data file, so that Lake knows which modules
  depend on them.
* `@[cite src "id" "comment"?]` cites the entry `id` of the declared source `src`.
* `@[cite "key" "locator"? "comment"?]` cites the entry `key` of the BibTeX file: all of it, or the
  part `locator`, such as `"Theorem 2.3"`. It appends `[key]` to the docstring, which doc-gen4
  links to the bibliography, so a key must be nonempty and contain no whitespace, quotes,
  backslashes, braces, brackets or commas.
* The option `cite.bibFile`, by default `docs/references.bib`, is the BibTeX file, resolved
  against the working directory as by the `{cite}` docstring role. Another project sets it in its
  lakefile, as ``leanOptions := #[⟨`weak.cite.bibFile, "docbuild/docs/references.bib"⟩]``.
  `@[cite "key"]` warns when the file exists and lacks the key. Lake does not track this read, so
  it only affects the warning: nothing recorded depends on the file. The file is read again for
  each citation, as by the `{cite}` role.

`@[cite]` is registered in `Mathlib/Tactic/CrossRefAttribute.lean`, which declares each
cross-reference database as a source. It is full sugar for the cross-reference attributes:
`@[cite stacks "0BR2" "c"]` runs the same code as `@[stacks 0BR2 "c"]`. As for them, no link is
added to a declaration that has a docstring of its own, or by `attribute [cite …]` after it (see
the TODO at `Mathlib.CrossRef.citeEntry`), but the citation is recorded all the same.
-/

public meta section

open Lean Elab Command

namespace Mathlib.Cite

/-! ### Sources -/

/-- A work that declarations cite, declared by `cite_source`. -/
structure Source where
  /-- The name that citations use, such as `oeis`. -/
  name : Name
  /-- A readable title, such as `The On-Line Encyclopedia of Integer Sequences`. -/
  title : String
  /-- The address templates of the entries, keyed by a prefix of the id, the longest one winning. -/
  uriTemplates : Array (String × String)
  /-- The source's other fields, as `cite_source` was given them, such as `("type", "pdf")`. -/
  fields : Array (String × String) := #[]
  /-- The source's docstring, kept for exports. -/
  doc : String := ""
  /-- The module that declared the source. -/
  module : Name := .anonymous
  deriving Inhabited, Repr

/-- The value of the source's field `key`, when it has one. -/
def Source.field? (s : Source) (key : String) : Option String :=
  (s.fields.find? (·.1 == key)).map (·.2)

/-- The address of the entry `id` under the templates `uriTemplates`, with `id` percent-encoded. -/
def entryUri (uriTemplates : Array (String × String)) (id : String) : String :=
  let template? := (uriTemplates.filter (id.startsWith ·.1)).getMax? (·.1.length < ·.1.length)
  ((template?.map (·.2)).getD "").replace "{id}" (System.Uri.escapeUri id)

/-- Add the source `s` to a registry of sources by name. -/
def insertSource (registry : NameMap (Array Source)) (s : Source) : NameMap (Array Source) :=
  registry.insert s.name (((registry.find? s.name).getD #[]).push s)

/-- The environment extension storing the declared sources, by name. -/
initialize sourceExt : SimplePersistentEnvExtension Source (NameMap (Array Source)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries insertSource {}
    addEntryFn := insertSource
  }

/-- The declarations of the source `name`: several when modules not importing each other do. -/
def sourceDecls (env : Environment) (name : Name) : Array Source :=
  ((sourceExt.getState env).find? name).getD #[]

/-- Every declared source, imported or of the current module, ordered by name. -/
def sources (env : Environment) : Array Source :=
  (sourceExt.getState env).toArray.flatMap (·.2) |>.qsort (·.name.lt ·.name)

/-- The source named `name`, or an error unless exactly one module declares it. -/
def findSource {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (name : Name) :
    m Source := do
  match sourceDecls (← getEnv) name with
  | #[s] => return s
  | #[] => throwError "Unknown source `{name}`; declare it with `cite_source`."
  | ss => throwError "The source `{name}` is declared in several modules: \
      {", ".intercalate (ss.toList.map fun s => s!"`{s.module}`")}."

/-- Declare `s` as a source of the current module, or throw if its name is already taken. -/
def addSource {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (s : Source) : m Unit := do
  if let some old := (sourceDecls (← getEnv) s.name)[0]? then
    throwError "The source `{s.name}` is already declared, in module `{old.module}`."
  modifyEnv (sourceExt.addEntry · { s with module := (← getEnv).mainModule })

/-! ### Citations -/

/-- The source of a citation: a source declared with `cite_source`, or a key of the BibTeX file. -/
inductive CitedSource where
  /-- The source declared with `cite_source` under this name. -/
  | source (name : Name)
  /-- The entry of the BibTeX file `cite.bibFile` with this key. -/
  | bib (key : String)
  deriving Inhabited, Repr, BEq

/-- A citation: the declaration `declName` formalizes an entry, or a part, of a source. -/
structure Citation where
  /-- The declaration that cites the entry. -/
  declName : Name
  /-- The cited source. -/
  source : CitedSource
  /-- The entry of a declared source, or the locator in a BibTeX entry, or empty for all of it. -/
  id : String
  /-- A comment supplied with the citation, or empty. -/
  comment : String := ""
  deriving Inhabited, Repr, BEq

/-- The environment extension storing all citations. -/
initialize citeExt : SimplePersistentEnvExtension Citation (Array (Array Citation)) ←
  registerSimplePersistentEnvExtension {
    -- the imported citations are kept as they are, to avoid an overhead at initialization
    addImportedFn citations := citations
    addEntryFn citations _ := citations
  }

/-- Every citation: those of the imported modules, then those of the current one, in order. -/
def citations (env : Environment) : Array Citation :=
  let (currentModule, imported) := PersistentEnvExtension.getState citeExt env
  imported.flatten ++ currentModule.reverse.toArray

/-- Record the citation `c` in the current module. -/
def addCitation {m : Type → Type} [MonadEnv m] (c : Citation) : m Unit :=
  modifyEnv (citeExt.addEntry · c)

/-! ### The BibTeX file -/

/-- The BibTeX file whose keys `@[cite "key"]` cites, relative to the working directory. -/
register_option cite.bibFile : String := {
  defValue := "docs/references.bib"
  descr := "the BibTeX file whose keys `@[cite \"key\"]` cites"
}

/-- Check that `key` is a valid BibTeX key, and warn when `cite.bibFile` exists and lacks it. -/
def checkBibKey (key : String) : CoreM Unit := do
  if key.isEmpty || key.any fun (c : Char) => c.isWhitespace || "\"\\{}[],".contains c then
    throwError "`{key}` is not a valid BibTeX key."
  let path : System.FilePath := ⟨cite.bibFile.get (← getOptions)⟩
  -- a file that cannot be read, such as a missing one, is skipped: it only affects the warning
  let .ok text ← (IO.FS.readFile path).toBaseIO | return
  unless VersoRoles.bibContainsKey text key do
    logWarning m!"No bibliography entry `{key}` in `{path}`."

/-! ### The `cite_source` command -/

/-- A field of a source: `(uri := "https://oeis.org/{id}")`. -/
syntax citeSourceField := "(" ident " := " str ")"

/-- `cite_source name "title" (uri := "…{id}…") (key := "value")*` declares a citable source. -/
syntax (name := citeSource) (docComment)? "cite_source " Lean.Parser.rawIdent ppSpace str
  (ppSpace citeSourceField)* : command

/-- Elaborate `cite_source`: read the fields and declare the source. -/
@[command_elab citeSource]
def elabCiteSource : CommandElab
  | `(command| $[$doc]? cite_source $name:ident $title:str $fields*) => do
    let mut fieldValues := #[]
    for field in fields do
      let `(citeSourceField| ($key:ident := $value:str)) := field | throwUnsupportedSyntax
      let keyName := key.getId.eraseMacroScopes.toString
      if fieldValues.any (·.1 == keyName) then
        throwErrorAt key "The field `{keyName}` is given twice."
      fieldValues := fieldValues.push (keyName, value.getString)
    let some uri := (fieldValues.find? (·.1 == "uri")).map (·.2)
      | throwError "A source needs an address: `(uri := \"https://…\")`."
    withRef name <| addSource {
      name := name.getId.eraseMacroScopes
      title := title.getString
      uriTemplates := #[("", uri)]
      fields := fieldValues.filter (·.1 != "uri")
      doc := (← doc.mapM getDocStringText).getD "" |>.trimAscii.toString }
  | _ => throwUnsupportedSyntax

end Mathlib.Cite
