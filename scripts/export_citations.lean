/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/

import Mathlib
import Mathlib.Tactic.Cite.LiteratureLinks

/-!
# Export citations as Literature Links annotations

Elaborating this file writes one
[Literature Links](https://github.com/mathlib-initiative/literature-links) annotation per line
(JSONL) for every citation recorded by `@[cite ...]`, including those that the cross-reference
attributes `@[stacks ...]`, `@[kerodon ...]`, … record for their databases. Each annotation has
the entry of the cited source as its subject and the Mathlib declaration as its object.

Which kind of document each source is comes from its field `type`, or from the shape of its
address when it has no such field; see `Mathlib/Tactic/Cite/LiteratureLinks.lean`. A source whose
`type` is not one of `Mathlib.Cite.endTypes` stops the export, naming the source.

The citations are read from the ambient environment (like the `#stacks_tags` command), so the
file must be run with the full `Mathlib` import elaborated:

  lake env lean scripts/export_citations.lean

The output path is taken from the `CITATIONS_OUT` environment variable (default
`citations.jsonl`) and the commit that the Lean ends are pinned to from `CITATIONS_COMMIT`
(default `unknown`).
-/

open Lean Mathlib.Cite

namespace ExportCitations

/-- Every citation, by source, then entry, then declaration: a canonical order keeps the
published file stable. -/
def sortedCitations (env : Environment) : Array Citation :=
  citations env |>.qsort fun a b =>
    (compare a.source.toString b.source.toString |>.then (compare a.id b.id)
      |>.then (compare a.declName.toString b.declName.toString)).isLT

end ExportCitations

open ExportCitations in
run_cmd do
  let env ← getEnv
  let commit := (← IO.getEnv "CITATIONS_COMMIT").getD "unknown"
  -- `cite_source` takes any `type`; an end of a type no reader knows is reported here
  let unknown := unknownEndTypes env
  unless unknown.isEmpty do
    throwError "the field `type` of {unknown.size} \
      source{if unknown.size == 1 then "" else "s"} is not one of the end types \
      {", ".intercalate endTypes}: \
      {", ".intercalate (unknown.toList.map fun (name, type) => s!"{name} ({type})")}"
  let mut annotations : Array String := #[]
  let mut skipped : Array Name := #[]
  for citation in sortedCitations env do
    match citation.annotation? env commit with
    | some annotation => annotations := annotations.push (annotation.compress ++ "\n")
    | none => skipped := skipped.push citation.source
  unless skipped.isEmpty do
    throwError "{skipped.size} citation{if skipped.size == 1 then "" else "s"} \
      {if skipped.size == 1 then "names" else "name"} an undeclared source: \
      {skipped.toList.eraseDups}; declare it with `cite_source`"
  let path := (← IO.getEnv "CITATIONS_OUT").getD "citations.jsonl"
  IO.FS.writeFile path (String.join annotations.toList)
  logInfo m!"Wrote {annotations.size} Literature Links annotations to {path}"
