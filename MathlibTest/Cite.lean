module

public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open Lean Mathlib.Cite Mathlib.CrossRef

/-- Integer sequences. -/
cite_source oeisTest "The OEIS" (uri := "https://oeis.org/{id}")

/-- A book. -/
cite_source ladr4e "LADR" (uri := "https://linear.axler.net/LADR4e.pdf") (type := "pdf")

/-- A wiki. -/
cite_source nlab "the nLab" (uri := "https://ncatlab.org") (registry := "nlab")

-- The title is escaped in the docstring link, and the id is percent-encoded in the address.
cite_source oddTitle "A [weird] *title*" (uri := "https://wiki.example/{id}")

/-- A one-line description of a citation. -/
meta def describe (c : Citation) : String :=
  let source := match c.source with
    | .source name => name.toString
    | .bib key => s!"bib \"{key}\""
  s!"{c.declName}: {source} \"{c.id}\" \"{c.comment}\""

/-- A one-line description of a source. -/
meta def describeSource (s : Source) : String :=
  s!"{s.name}: \"{s.title}\" {s.uriTemplates} {s.fields} \"{s.doc}\""

/-- Log the docstring of `decl`. -/
meta def logDoc (decl : Name) : CoreM Unit := do
  logInfo m!"{← findDocString? (← getEnv) decl}"

/--
info: ladr4e: "LADR" #[(, https://linear.axler.net/LADR4e.pdf)] #[(type, pdf)] "A book."
nlab: "the nLab" #[(, https://ncatlab.org)] #[(registry, nlab)] "A wiki."
oddTitle: "A [weird] *title*" #[(, https://wiki.example/{id})] #[] ""
oeisTest: "The OEIS" #[(, https://oeis.org/{id})] #[] "Integer sequences."
-/
#guard_msgs in
run_cmd
  logInfo <| "\n".intercalate <|
    ((sources (← getEnv)).filter (·.module == `MathlibTest.Cite)).toList.map describeSource

/-- info: some "nlab" -/
#guard_msgs in
run_cmd logInfo <| repr <| (← findSource `nlab).field? "registry"

namespace Declared

@[cite oeisTest "A000045" "the Fibonacci numbers"]
theorem withId : True := .intro

@[cite ladr4e "3.21"]
theorem withoutId : True := .intro

@[cite oddTitle "a b/c"]
theorem oddTitle : True := .intro

theorem late : True := .intro

attribute [cite ladr4e "3.21"] late

end Declared

/-- info: some ([The OEIS A000045](https://oeis.org/A000045) (the Fibonacci numbers)) -/
#guard_msgs in
run_meta logDoc `Declared.withId

/-- info: some ([LADR 3\.21](https://linear.axler.net/LADR4e.pdf)) -/
#guard_msgs in
run_meta logDoc `Declared.withoutId

/-- info: some ([A \[weird\] \*title\* a b\/c](https://wiki.example/a%20b/c)) -/
#guard_msgs in
run_meta logDoc `Declared.oddTitle

-- Known issue, as for the cross-reference attributes: the docstring of a declaration that is
-- already elaborated cannot be changed, so the citation is recorded but no link is added.
/-- info: none -/
#guard_msgs in
run_meta logDoc `Declared.late

namespace Errors

/-- error: The source `oeisTest` is already declared, in module `MathlibTest.Cite`. -/
#guard_msgs in
cite_source oeisTest "Another" (uri := "https://oeis.org/{id}")

/-- error: A source needs an address: `(uri := "https://…")`. -/
#guard_msgs in
cite_source noAddress "No address"

/-- error: The field `uri` is given twice. -/
#guard_msgs in
cite_source twoAddresses "Two addresses" (uri := "https://a.example") (uri := "https://b.example")

/-- error: The field `type` is given twice. -/
#guard_msgs in
cite_source twoTypes "Two types" (uri := "https://a.example") (type := "pdf") (type := "html")

/-- error: Unknown source `undeclared`; declare it with `cite_source`. -/
#guard_msgs in
@[cite undeclared "A000045"] theorem undeclared : True := .intro

/-- error: The cited entry cannot be empty. -/
#guard_msgs in
@[cite oeisTest ""] theorem emptyId : True := .intro

/-- error: The cited entry cannot be empty. -/
#guard_msgs in
@[cite oeisTest] theorem noId : True := .intro

-- `@[cite]` checks the entry of a database as its cross-reference attribute does.
/-- error: Stacks tags must consist only of digits and uppercase letters. -/
#guard_msgs in
@[cite stacks "0br2"] theorem badStacksTag : True := .intro

/-- error: π-Base ids must start with P, S, or T. -/
#guard_msgs in
@[cite «pibase-topology» "Q000001"] theorem badPiBaseId : True := .intro

/-- error: Invalid attribute scope: Attribute `[cite]` must be global, not `local` -/
#guard_msgs in
@[local cite oeisTest "A000045"] theorem citedLocally : True := .intro

theorem citedScoped : True := .intro

/-- error: Invalid attribute scope: Attribute `[cite]` must be global, not `scoped` -/
#guard_msgs in
attribute [scoped cite oeisTest "A000045"] citedScoped

end Errors

-- `@[cite]` on a database is full sugar for its cross-reference attribute.
namespace Sugar

@[stacks 0BR2 "a Stacks tag"]
theorem stacksTagged : True := .intro

@[cite stacks "0BR2" "a Stacks tag"]
theorem stacksCited : True := .intro

-- A π-Base property, whose address comes from the `P` template rather than the default one.
@[pibase topology P000001 "prop"]
theorem piBaseTagged : True := .intro

@[cite «pibase-topology» "P000001" "prop"]
theorem piBaseCited : True := .intro

end Sugar

/-- The docstring, cross-references and citations that `decl` carries, with `decl` erased. -/
meta def recorded (decl : Name) : CoreM (Option String × List Tag × List Citation) := do
  let env ← getEnv
  let tags := (PersistentEnvExtension.getState tagExt env).1.filter (·.declName == decl)
  let cites := (citations env).toList.filter (·.declName == decl)
  return (← findDocString? env decl, tags.map ({ · with declName := .anonymous }),
    cites.map ({ · with declName := .anonymous }))

/-- Check that `a` and `b` carry the same docstring, cross-reference and citation. -/
meta def checkParity (a b : Name) : CoreM Unit := do
  let (docA, tagsA, citesA) ← recorded a
  unless (docA, tagsA, citesA) == (← recorded b) && tagsA.length == 1 && citesA.length == 1 do
    throwError "`{.ofConstName a}` and `{.ofConstName b}` differ"
  logInfo m!"{docA}"

/-- info: some ([Stacks Tag 0BR2](https://stacks.math.columbia.edu/tag/0BR2) (a Stacks tag)) -/
#guard_msgs in
run_meta checkParity `Sugar.stacksTagged `Sugar.stacksCited

/--
info: some ([π-Base (Topology) P000001](https://topology.pi-base.org/properties/P000001) (prop))
-/
#guard_msgs in
run_meta checkParity `Sugar.piBaseTagged `Sugar.piBaseCited

namespace Bib

#guard_msgs in
@[cite "Adamek_Rosicky_1994"] theorem whole : True := .intro

#guard_msgs in
@[cite "Adamek_Rosicky_1994" "Theorem 2.3" "for a small category"] theorem part : True := .intro

/-- warning: No bibliography entry `Nobody_2026` in `docs/references.bib`. -/
#guard_msgs in
@[cite "Nobody_2026" "Lemma 1"] theorem missingKey : True := .intro

-- Without a BibTeX file, there is nothing to check against.
set_option cite.bibFile "nonexistent.bib" in
#guard_msgs in
@[cite "Nobody_2026"] theorem noBibFile : True := .intro

-- Nor with a file that cannot be read, such as a directory.
set_option cite.bibFile "docs" in
#guard_msgs in
@[cite "Nobody_2026"] theorem unreadableBibFile : True := .intro

/-- error: `` is not a valid BibTeX key. -/
#guard_msgs in
@[cite ""] theorem emptyKey : True := .intro

/-- error: `a]b` is not a valid BibTeX key. -/
#guard_msgs in
@[cite "a]b"] theorem badKey : True := .intro

set_option doc.verso true in
@[cite "Adamek_Rosicky_1994" "Theorem 2.3"] theorem partVerso : True := .intro

end Bib

-- The key is left as it is, for doc-gen4 to link it to the bibliography.
/-- info: some ([Adamek_Rosicky_1994]) -/
#guard_msgs in
run_meta logDoc `Bib.whole

/-- info: some ([Adamek_Rosicky_1994], Theorem 2\.3 (for a small category)) -/
#guard_msgs in
run_meta logDoc `Bib.part

-- Under `doc.verso`, the `{cite}` role links the key.
/-- info: some (Adamek\_Rosicky\_1994, Theorem 2.3) -/
#guard_msgs in
run_meta logDoc `Bib.partVerso

/--
info: Declared.withId: oeisTest "A000045" "the Fibonacci numbers"
Declared.withoutId: ladr4e "3.21" ""
Declared.oddTitle: oddTitle "a b/c" ""
Declared.late: ladr4e "3.21" ""
Sugar.stacksTagged: stacks "0BR2" "a Stacks tag"
Sugar.stacksCited: stacks "0BR2" "a Stacks tag"
Sugar.piBaseTagged: «pibase-topology» "P000001" "prop"
Sugar.piBaseCited: «pibase-topology» "P000001" "prop"
Bib.whole: bib "Adamek_Rosicky_1994" "" ""
Bib.part: bib "Adamek_Rosicky_1994" "Theorem 2.3" "for a small category"
Bib.missingKey: bib "Nobody_2026" "Lemma 1" ""
Bib.noBibFile: bib "Nobody_2026" "" ""
Bib.unreadableBibFile: bib "Nobody_2026" "" ""
Bib.partVerso: bib "Adamek_Rosicky_1994" "Theorem 2.3" ""
-/
#guard_msgs in
run_cmd logInfo <| "\n".intercalate <| (citations (← getEnv)).toList.map describe
