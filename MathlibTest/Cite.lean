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

/-- A source with no `type`: a fixed address makes its ends `generic`. -/
cite_source nlab "the nLab" (uri := "https://ncatlab.org")

@[cite oeisTest "A000045" (rel := exactMatch) "the Fibonacci numbers"]
theorem fibonacci : True := .intro

theorem rankNullity : True := .intro

attribute [cite ladr4e "3.21"] rankNullity

/-- A one-line description of a citation, for the tests below. -/
meta def describe (c : Citation) : String :=
  s!"{c.declName}: {c.source} {c.id} ({c.rel}) \"{c.comment}\" {c.url}"

/-- A one-line description of a source, for the tests below. -/
meta def describeSource (s : Source) : String :=
  s!"{s.name}: \"{s.title}\" {s.uriTemplates} {s.type} \"{s.doc}\" {s.module}"

/--
info: ladr4e: "Linear Algebra Done Right, 4th edition" #[(, https://linear.axler.net/LADR4e.pdf)] pdf "A book, cited as a whole: without `{id}`, the address is the source's own." MathlibTest.Cite
nlab: "the nLab" #[(, https://ncatlab.org)] generic "A source with no `type`: a fixed address makes its ends `generic`." MathlibTest.Cite
oeisTest: "The On-Line Encyclopedia of Integer Sequences" #[(, https://oeis.org/{id})] html "An online database of integer sequences." MathlibTest.Cite
-/
#guard_msgs in
run_cmd
  logInfo <| "\n".intercalate <|
    ((sources (← getEnv)).filter (·.module == `MathlibTest.Cite)).toList.map describeSource

/-! ### Errors -/

/-- error: the source `oeisTest` is already declared, in module `MathlibTest.Cite` -/
#guard_msgs in
cite_source oeisTest "A second encyclopedia" (uri := "https://oeis.org/{id}")

/-- error: a source needs an address: `(uri := "https://…")` -/
#guard_msgs in
cite_source anonymousSource "A source with no address"

/--
error: unknown type `webpage`; the types are pdf, latex, html, lean, generic
-/
#guard_msgs in
cite_source misTyped "A source of an unknown type" (uri := "https://example.com")
  (type := "webpage")

/-- error: unknown field `registry` of `cite_source`; the fields are `uri` and `type` -/
#guard_msgs in
cite_source misFielded "A source with an unknown field" (uri := "https://example.com")
  (registry := "wikidata")

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

/-! ### Literature Links annotations -/

/--
info: {"id":"oeisTest:A000045","note":"the Fibonacci numbers","object":[{"location":{"declaration":"fibonacci","module":"MathlibTest.Cite"},"type":"lean","uri":"https://github.com/leanprover-community/mathlib4","version":"0123456789abcdef"}],"relation":"exactMatch","subject":[{"identifiers":{"oeisTest":"A000045"},"title":"The On-Line Encyclopedia of Integer Sequences A000045","type":"html","uri":"https://oeis.org/A000045"}]}
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let some citation := (citations env).find? (·.declName == `fibonacci)
    | throwError "the citation of `fibonacci` was not recorded"
  let some annotation := citation.annotation? env "0123456789abcdef"
    | throwError "the source of the citation is not declared"
  logInfo annotation.compress
