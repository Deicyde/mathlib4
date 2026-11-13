module

public import Mathlib.Tactic.Cite
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open Lean Mathlib.Cite

/-! ### Declaring a source and citing it -/

/-- An online database of integer sequences. -/
cite_source oeisTest "The On-Line Encyclopedia of Integer Sequences"
  (uri := "https://oeis.org/{id}")

/-- A book, cited as a whole: without `{id}`, the address is the source's own. -/
cite_source ladr4e "Linear Algebra Done Right, 4th edition"
  (uri := "https://linear.axler.net/LADR4e.pdf") (type := "pdf")

/-- A source with fields of its own: every field but `uri` is kept as it was given. -/
cite_source nlab "the nLab" (uri := "https://ncatlab.org") (registry := "nlab")

@[cite oeisTest "A000045" (rel := exactMatch) "the Fibonacci numbers"]
theorem fibonacci : True := .intro

theorem rankNullity : True := .intro

attribute [cite ladr4e "3.21"] rankNullity

/-- A one-line description of a citation, for the tests below. -/
meta def describe (c : Citation) : String :=
  s!"{c.declName}: {c.source} {c.id} ({c.rel}) \"{c.comment}\" {c.url}"

/-- A one-line description of a source, for the tests below. -/
meta def describeSource (s : Source) : String :=
  s!"{s.name}: \"{s.title}\" {s.uriTemplates} {s.fields} \"{s.doc}\" {s.module}"

/--
info: ladr4e: "Linear Algebra Done Right, 4th edition" #[(, https://linear.axler.net/LADR4e.pdf)] #[(type, pdf)] "A book, cited as a whole: without `{id}`, the address is the source's own." MathlibTest.Cite
nlab: "the nLab" #[(, https://ncatlab.org)] #[(registry, nlab)] "A source with fields of its own: every field but `uri` is kept as it was given." MathlibTest.Cite
oeisTest: "The On-Line Encyclopedia of Integer Sequences" #[(, https://oeis.org/{id})] #[] "An online database of integer sequences." MathlibTest.Cite
-/
#guard_msgs in
run_cmd
  logInfo <| "\n".intercalate <|
    ((sources (← getEnv)).filter (·.module == `MathlibTest.Cite)).toList.map describeSource

-- a free field is read back from the source with `Source.field?`
/-- info: some "nlab" -/
#guard_msgs in
run_cmd do
  let .ok source := findSource (← getEnv) `nlab | throwError "the source `nlab` is not declared"
  logInfo <| repr (source.field? "registry")

/-! ### Errors -/

/-- error: the source `oeisTest` is already declared, in module `MathlibTest.Cite` -/
#guard_msgs in
cite_source oeisTest "A second encyclopedia" (uri := "https://oeis.org/{id}")

/-- error: a source needs an address: `(uri := "https://…")` -/
#guard_msgs in
cite_source anonymousSource "A source with no address"

/-- error: the field `uri` is given twice -/
#guard_msgs in
cite_source twiceAddressed "A source with two addresses" (uri := "https://a.example")
  (uri := "https://b.example")

/-- error: the field `type` is given twice -/
#guard_msgs in
cite_source twiceTyped "A source with a field given twice" (uri := "https://example.com")
  (type := "pdf") (type := "html")

/-- error: unknown source `undeclared`; declare it with `cite_source` -/
#guard_msgs in
@[cite undeclared "A000045"]
theorem citesNothing : True := .intro

/--
error: unknown relation `exact`; the relations are exactMatch, closeMatch, broadMatch, narrowMatch, relatedMatch, hasPart, noMatch
-/
#guard_msgs in
@[cite oeisTest "A000045" (rel := exact)]
theorem citesBadly : True := .intro

/-- error: the cited entry cannot be empty -/
#guard_msgs in
@[cite oeisTest ""]
theorem citesNoEntry : True := .intro

/-! ### The cross-reference attributes record citations of their databases -/

-- `@[stacks 0BR2]` and `@[cite stacks "0BR2"]` record the same entry at the same address.
@[stacks 0BR2 "a Stacks tag"]
theorem tagged : True := .intro

@[cite stacks "0BR2"]
theorem citedDirectly : True := .intro

-- A π-Base property, whose address comes from the `P` template rather than the default one.
@[pibase topology P000001 "a π-Base property"]
theorem piBaseTagged : True := .intro

@[cite «pibase-topology» "P000001"]
theorem piBaseCitedDirectly : True := .intro

/--
info: fibonacci: oeisTest A000045 (exactMatch) "the Fibonacci numbers" https://oeis.org/A000045
rankNullity: ladr4e 3.21 () "" https://linear.axler.net/LADR4e.pdf
tagged: stacks 0BR2 () "a Stacks tag" https://stacks.math.columbia.edu/tag/0BR2
citedDirectly: stacks 0BR2 () "" https://stacks.math.columbia.edu/tag/0BR2
piBaseTagged: «pibase-topology» P000001 () "a π-Base property" https://topology.pi-base.org/properties/P000001
piBaseCitedDirectly: «pibase-topology» P000001 () "" https://topology.pi-base.org/properties/P000001
-/
#guard_msgs in
run_cmd
  logInfo <| "\n".intercalate <| (citations (← getEnv)).toList.map describe
