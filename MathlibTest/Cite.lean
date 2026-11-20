module

public import Mathlib.Tactic.Cite

@[expose] public section

open Lean Mathlib.Cite

/-- Log the docstring of `decl`. -/
meta def logDoc (decl : Name) : CoreM Unit := do
  logInfo m!"{← findDocString? (← getEnv) decl}"

namespace Bib

#guard_msgs in
@[cite "Adamek_Rosicky_1994"] theorem whole : True := .intro

#guard_msgs in
@[cite "Adamek_Rosicky_1994" "Theorem 2.3"] theorem part : True := .intro

/-- warning: No bibliography entry `Nobody_2026` in `docs/references.bib`. -/
#guard_msgs in
@[cite "Nobody_2026" "Lemma 1"] theorem missingKey : True := .intro

-- Under `doc.verso`, the warning comes from the `{cite}` role of the link, and only from it.
/-- warning: No bibliography entry `Nobody_2026` in `docs/references.bib`. -/
#guard_msgs in
set_option doc.verso true in
@[cite "Nobody_2026"] theorem missingKeyVerso : True := .intro

set_option doc.verso true in
@[cite "Adamek_Rosicky_1994" "Theorem 2.3"] theorem partVerso : True := .intro

/-- This docstring is kept. -/
@[cite "Adamek_Rosicky_1994"] theorem ownDocstring : True := .intro

end Bib

-- The key is left as it is, for doc-gen4 to link it to the bibliography.
/-- info: some ([Adamek_Rosicky_1994]) -/
#guard_msgs in
run_meta logDoc `Bib.whole

-- The locator is not escaped.
/-- info: some ([Adamek_Rosicky_1994], Theorem 2.3) -/
#guard_msgs in
run_meta logDoc `Bib.part

-- Under `doc.verso`, the link renders as the escaped key. That it is a `{cite}` role is shown by
-- the warning for `missingKeyVerso`.
/-- info: some (Adamek\_Rosicky\_1994, Theorem 2.3) -/
#guard_msgs in
run_meta logDoc `Bib.partVerso

-- Known issue, as for the cross-reference attributes: due to async elaboration, the link is
-- overwritten by the declaration's own docstring. The citation is still recorded, see below.
/-- info: some (This docstring is kept.) -/
#guard_msgs in
run_meta logDoc `Bib.ownDocstring

namespace Errors

/-- error: Invalid key "": it must be nonempty, without whitespace or `"\{}[],`. -/
#guard_msgs in
@[cite ""] theorem emptyKey : True := .intro

/-- error: Invalid key "a]b": it must be nonempty, without whitespace or `"\{}[],`. -/
#guard_msgs in
@[cite "a]b"] theorem bracketKey : True := .intro

/-- error: Invalid key "a b": it must be nonempty, without whitespace or `"\{}[],`. -/
#guard_msgs in
@[cite "a b"] theorem spaceKey : True := .intro

/-- error: Invalid attribute scope: Attribute `[cite]` must be global, not `local` -/
#guard_msgs in
@[local cite "Adamek_Rosicky_1994"] theorem citedLocally : True := .intro

theorem citedScoped : True := .intro

/-- error: Invalid attribute scope: Attribute `[cite]` must be global, not `scoped` -/
#guard_msgs in
attribute [scoped cite "Adamek_Rosicky_1994"] citedScoped

end Errors

/--
info: Bib.whole: "Adamek_Rosicky_1994" ""
Bib.part: "Adamek_Rosicky_1994" "Theorem 2.3"
Bib.missingKey: "Nobody_2026" "Lemma 1"
Bib.missingKeyVerso: "Nobody_2026" ""
Bib.partVerso: "Adamek_Rosicky_1994" "Theorem 2.3"
Bib.ownDocstring: "Adamek_Rosicky_1994" ""
-/
#guard_msgs in
run_cmd logInfo <| "\n".intercalate <|
  (citations (← getEnv)).toList.map fun c => s!"{c.declName}: \"{c.key}\" \"{c.locator}\""
