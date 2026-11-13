module

public import Mathlib.Tactic.Cite.LiteratureLinks
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open Lean Mathlib.Cite

/-! ### The end type of a source -/

/-- An online database of integer sequences: its entries have addresses of their own. -/
cite_source oeisLL "The On-Line Encyclopedia of Integer Sequences"
  (uri := "https://oeis.org/{id}")

/-- A book, cited as a whole: its `type` says which kind of document it is. -/
cite_source ladrLL "Linear Algebra Done Right, 4th edition"
  (uri := "https://linear.axler.net/LADR4e.pdf") (type := "pdf")

/-- A source with one address and no `type`: its ends are `generic`. -/
cite_source nlabLL "the nLab" (uri := "https://ncatlab.org")

/-- A source whose `type` is not an end type: `cite_source` takes it, the export reports it. -/
cite_source misTypedLL "A source of an unknown type" (uri := "https://example.com")
  (type := "webpage")

-- the cross-reference databases are web databases, so their ends are `html`
/-- info: html pdf generic webpage html -/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let types ← #[`oeisLL, `ladrLL, `nlabLL, `misTypedLL, `stacks].mapM fun name => do
    let .ok source := findSource env name | throwError "the source `{name}` is not declared"
    return source.endType
  logInfo <| " ".intercalate types.toList

/-- info: #[(misTypedLL, webpage)] -/
#guard_msgs in
run_cmd
  logInfo <| toString (unknownEndTypes (← getEnv))

/-! ### Annotations -/

@[cite oeisLL "A000045" (rel := exactMatch) "the Fibonacci numbers"]
theorem fibonacci : True := .intro

@[cite ladrLL "3.21"]
theorem rankNullity : True := .intro

@[stacks 0BR2]
theorem tagged : True := .intro

/-- The annotation of the one citation of `decl`, as one line of JSON. -/
meta def annotationOf (env : Environment) (decl : Name) : Elab.Command.CommandElabM String := do
  let some citation := (citations env).find? (·.declName == decl)
    | throwError "the citation of `{decl}` was not recorded"
  let some annotation := citation.annotation? env "0123456789abcdef"
    | throwError "the source of the citation is not declared"
  return annotation.compress

/--
info: {"id":"oeisLL:A000045","note":"the Fibonacci numbers","object":[{"location":{"declaration":"fibonacci","module":"MathlibTest.Cite.LiteratureLinks"},"type":"lean","uri":"https://github.com/leanprover-community/mathlib4","version":"0123456789abcdef"}],"relation":"exactMatch","subject":[{"identifiers":{"oeisLL":"A000045"},"title":"The On-Line Encyclopedia of Integer Sequences A000045","type":"html","uri":"https://oeis.org/A000045"}]}
-/
#guard_msgs in
run_cmd do
  logInfo <| ← annotationOf (← getEnv) `fibonacci

-- a book cited as a whole: the entries share the source's address, and the end is a `pdf`
/--
info: {"id":"ladrLL:3.21","object":[{"location":{"declaration":"rankNullity","module":"MathlibTest.Cite.LiteratureLinks"},"type":"lean","uri":"https://github.com/leanprover-community/mathlib4","version":"0123456789abcdef"}],"subject":[{"identifiers":{"ladrLL":"3.21"},"title":"Linear Algebra Done Right, 4th edition 3.21","type":"pdf","uri":"https://linear.axler.net/LADR4e.pdf"}]}
-/
#guard_msgs in
run_cmd do
  logInfo <| ← annotationOf (← getEnv) `rankNullity

-- a cross-reference attribute records a citation like any other, and it is exported the same way
/--
info: {"id":"stacks:0BR2","object":[{"location":{"declaration":"tagged","module":"MathlibTest.Cite.LiteratureLinks"},"type":"lean","uri":"https://github.com/leanprover-community/mathlib4","version":"0123456789abcdef"}],"subject":[{"identifiers":{"stacks":"0BR2"},"title":"Stacks Tag 0BR2","type":"html","uri":"https://stacks.math.columbia.edu/tag/0BR2"}]}
-/
#guard_msgs in
run_cmd do
  logInfo <| ← annotationOf (← getEnv) `tagged
