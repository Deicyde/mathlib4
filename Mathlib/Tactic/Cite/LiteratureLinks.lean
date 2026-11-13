/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public meta import ImportGraph.Lean.Environment  -- shake: keep (Environment.getModuleFor? is used from public meta code), cf. lean#14427
public meta import Lean.Data.Json
public meta import Mathlib.Tactic.Cite
public import Mathlib.Init

/-!
# Citations as Literature Links annotations

[Literature Links](https://github.com/mathlib-initiative/literature-links) is a format for
annotations that relate an entry of a work to a formalization of it. This file turns the citations
that `Mathlib/Tactic/Cite.lean` records into such annotations: the entry of the cited source is
the subject, the declaration citing it the object. `scripts/export_citations.lean` writes them
out, one per line.

An annotation says of which kind of document each of its two ends is, one of
`Mathlib.Cite.endTypes`. The Lean end is `lean`; the end made from a source is the source's free
field `type` when it has one, and otherwise `html` for a source whose entries have addresses of
their own and `generic` for one address shared by all of them. A `type` that is not an end type
is reported by the export, which reads `Mathlib.Cite.unknownEndTypes`.
-/

public meta section

open Lean

namespace Mathlib.Cite

/-- The Literature Links types of an end: the kind of document that holds it. -/
def endTypes : List String := ["pdf", "latex", "html", "lean", "generic"]

/-- The Literature Links type of the ends made from the source `s`: its field `type` when it has
one, and otherwise `html` when the address of an entry is a template, as for a web database whose
entries have pages of their own, and `generic` when the entries share the source's own address.
A field `type` is passed on as it is given; `Mathlib.Cite.unknownEndTypes` collects the sources
whose `type` is not one of `endTypes`, for the export to report. -/
def Source.endType (s : Source) : String :=
  match s.field? "type" with
  | some type => type
  | none =>
    let templated := s.uriTemplates.any fun (_, template) => (template.splitOn "{id}").length > 1
    if templated then "html" else "generic"

/-- The declared sources whose field `type` is not one of `endTypes`, each with that value: the
export reports them rather than writing out an end of a type that no reader knows. -/
def unknownEndTypes (env : Environment) : Array (Name × String) :=
  (sources env).filterMap fun s =>
    (s.field? "type").bind fun type =>
      if endTypes.contains type then none else some (s.name, type)

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
    [("type", toJson source.endType), ("uri", toJson c.url),
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

end Mathlib.Cite
