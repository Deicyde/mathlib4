/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public meta import Mathlib.Tactic.CrossRefAttribute
public meta import Mathlib.Util.VersoRoles

/-!
# Citations of the bibliography

A *citation* records that a declaration formalizes an entry of `docs/references.bib`, or a part of
it. Citations are kept in an environment extension, which an export can read with `citations`.
As for the cross-reference attributes, a declaration with a docstring of its own, or cited by
`attribute [cite …]` after it, gets no link, but its citation is recorded.

* `@[cite "key"]` cites the entry `key`, and `@[cite "key" "locator"]` the part `locator` of it,
  such as `"Theorem 2.3"`. It appends `[key]` to the docstring, which doc-gen4 links to the
  bibliography, so a key must be nonempty and contain no whitespace, quotes, backslashes, braces,
  brackets or commas. It warns when `docs/references.bib` lacks the key. Lake does not track this
  read, so it only affects the warning: nothing recorded depends on the file.
-/

public meta section

open Lean Elab

namespace Mathlib.Cite

/-- A citation: the declaration `declName` formalizes the entry `key`, or a part of it. -/
structure Citation where
  /-- The declaration that cites the entry. -/
  declName : Name
  /-- The key of the entry in `docs/references.bib`. -/
  key : String
  /-- The cited part of the entry, such as `Theorem 2.3`, or empty when all of it is cited. -/
  locator : String

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

/-- Check that `key` can be cited, and warn when `docs/references.bib` lacks it. -/
def checkBibKey (key : String) : CoreM Unit := do
  if key.isEmpty || key.any fun (c : Char) => c.isWhitespace || "\"\\{}[],".contains c then
    throwError "Invalid key {repr key}: it must be nonempty, without whitespace or `\"\\\{}[],`."
  -- under `doc.verso`, the `{cite}` role of the link warns instead
  if doc.verso.get (← getOptions) then return
  -- a file that cannot be read, such as a missing one, is skipped: it only affects the warning
  let .ok bib ← (IO.FS.readFile ("docs" / "references.bib")).toBaseIO | return
  unless VersoRoles.bibContainsKey bib key do
    logWarning m!"No bibliography entry `{key}` in `docs/references.bib`."

/-- `@[cite "key"]` or `@[cite "key" "locator"]` cites an entry of `docs/references.bib`. -/
syntax (name := citeAttr) &"cite" ppSpace str (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `citeAttr
  descr := "Cite an entry of the bibliography `docs/references.bib`."
  add decl stx attrKind := do
    unless attrKind == .global do throwAttrMustBeGlobal `cite attrKind
    let `(attr| cite $key $[$locator]?) := stx | throwUnsupportedSyntax
    let key' := key.getString
    let locator := (locator.map (·.getString)).getD ""
    -- doc-gen4 links a `[key]` of the bibliography, so the key is not escaped; Verso's `{cite}`
    -- role keeps the key in a string, and only the text it renders is escaped.
    let link := if doc.verso.get (← getOptions) then
      s!"\{cite \"{key'}\"}[{CrossRef.escapeFormatting key'}]" else s!"[{key'}]"
    withRef key <| checkBibKey key'
    CrossRef.appendDocString decl <| link ++ if locator.isEmpty then "" else s!", {locator}"
    modifyEnv (citeExt.addEntry · { declName := decl, key := key', locator })
  -- docstrings are immutable once an asynchronous elaboration task has been started
  applicationTime := .beforeElaboration
}

end Mathlib.Cite
