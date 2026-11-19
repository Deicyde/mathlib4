/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/

import Mathlib

/-!
# Export citations as Literature Links annotations

Elaborating this file writes one
[Literature Links](https://github.com/mathlib-initiative/literature-links) annotation per line
(JSONL) for every citation recorded by `@[cite ...]`, including those that the cross-reference
attributes `@[stacks ...]`, `@[kerodon ...]`, … record, sorted by `id` and then by declaration.
Each annotation has the cited entry as its subject and the Mathlib declaration as its object.

* The subject of a citation of a source declared with `cite_source` is the entry's address. Its
  `type` is the source's field `type`, which must be one of `endTypes`, and otherwise `html` when
  the entries have addresses of their own and `generic` when they share the source's. A database
  is identified by its short name in `identifiers`, and a source by its field `registry`.
* The subject of a citation of a BibTeX entry carries the entry as a CSL-JSON `citation`, read
  from the BibTeX file `CITATIONS_BIB` (default `docs/references.bib`), and the locator as its
  `title`. Its address is the entry's `url`, its DOI, or its place in Mathlib's bibliography.
  The CSL-JSON fields are the BibTeX ones without their braces: LaTeX in them, such as the accent
  in `Soboci\'nski`, is kept as it is written. A DOI written as a `https://doi.org/` address is
  read as the bare DOI.

The citations are read from the ambient environment (like the `#stacks_tags` command), so the
file must be run with the full `Mathlib` import elaborated:

  CITATIONS_COMMIT=$(git rev-parse HEAD) lake env lean scripts/export_citations.lean

The commit that the Lean ends are pinned to is taken from `CITATIONS_COMMIT`, which is required,
the output path from `CITATIONS_OUT` (default `citations.jsonl`) and the repository from
`CITATIONS_REPO` (default `https://github.com/leanprover-community/mathlib4`).
-/

open Lean Elab Command Json Mathlib.Cite Mathlib.CrossRef
open Std.Internal.Parsec String

namespace ExportCitations

/-- The Literature Links types of an end: the kind of document that holds it. -/
def endTypes : List String := ["pdf", "latex", "html", "lean", "generic"]

/-- Whether `key` is a valid `identifiers` key: nonempty, and without the whitespace, controls,
bidirectional and zero-width marks excluded by *References* in the Literature Links spec. -/
def isIdentifiersKey (key : String) : Bool :=
  !key.isEmpty && key.all fun c =>
    let n := c.toNat
    !(n ≤ 0x20 || (0x7f ≤ n && n ≤ 0xa0) || n == 0x61c || n == 0x1680 ||
      (0x2000 ≤ n && n ≤ 0x200f) || (0x2028 ≤ n && n ≤ 0x202f) ||
      (0x205f ≤ n && n ≤ 0x206f) || n == 0x3000 || n == 0xfeff || n == 0xfffe || n == 0xffff)

/-- `s`, unless it is empty. -/
def nonempty? (s : String) : Option String := if s.isEmpty then none else some s

/-! ### Reading the BibTeX file -/

/-- An entry of a BibTeX file: its type and field names in lowercase, its key, its fields. -/
structure BibEntry where
  /-- The entry type, such as `article`. -/
  type : String
  /-- The key that citations use. -/
  key : String
  /-- The fields, with their values as written but for the outer braces or quotes. -/
  fields : Array (String × String)
  deriving Inhabited

/-- The value of the field `name` of the entry, when it has one. -/
def BibEntry.field? (e : BibEntry) (name : String) : Option String :=
  (e.fields.find? (·.1 == name)).map (·.2)

/-- The characters from the current position on that satisfy `p`. -/
def takeWhile (p : Char → Bool) : Parser String := manyChars (satisfy p)

/-- Move past the character `c`, or fail. -/
def expect (c : Char) : Parser Unit := do
  if (← peek?) == some c then skip else fail s!"expected '{c}'"

/-- The text up to `close`, outside braces, which closes a `{` or a `"` already read. -/
partial def delimited (close : Char) (depth : Nat := 0) (acc : String := "") : Parser String := do
  let opener := if close == '}' then '{' else close
  let some c ← peek? | fail s!"a '{opener}' is never closed"
  if close == '"' && c == '}' && depth == 0 then fail "a '}' inside quotes closes nothing"
  skip
  if c == close && depth == 0 then return acc
  delimited close (if c == '{' then depth + 1 else if c == '}' then depth - 1 else depth)
    (acc.push c)

/-- The month abbreviations that BibTeX defines: the only bare words a value may be. -/
def months : List String :=
  ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]

/-- One piece of a field's value: braced, quoted, a number or a month abbreviation. -/
def piece : Parser String := do
  match ← peek? with
  | some '{' => skip; delimited '}'
  | some '"' => skip; delimited '"'
  | some c =>
    if c.isDigit then takeWhile Char.isDigit
    else if c.isAlpha then
      let word ← takeWhile Char.isAlphanum
      if months.contains word.toLower then pure word.toLower
      else fail s!"the macro `{word}` is not supported"
    else fail s!"expected a value, but found '{c}'"
  | none => fail "expected a value, but the file ends"

/-- A field's value: pieces joined by `#`. -/
def value : Parser String := do
  let mut v ← piece
  ws
  while (← peek?) == some '#' do
    skip; ws
    v := v ++ (← piece)
    ws
  return v

/-- Whether `c` can be part of an entry type or a field name. -/
def isNameChar (c : Char) : Bool := c.isAlphanum || "-_.:+".contains c

/-- One `@type{key, field = value, …}`; `none` for a `@comment`. -/
def entry : Parser (Option BibEntry) := do
  expect '@'; ws
  let type := (← takeWhile Char.isAlpha).toLower
  if type.isEmpty then fail "expected an entry type after '@'"
  ws
  if type == "comment" then
    expect '{'; discard <| delimited '}'
    return none
  if type == "string" || type == "preamble" then fail s!"`@{type}` is not supported"
  expect '{'; ws
  let key ← takeWhile fun c => !c.isWhitespace && !",{}()\"#%'=".contains c
  if key.isEmpty then fail "expected the key of an entry"
  ws; expect ','
  let mut fields := #[]
  repeat
    ws
    if (← peek?) == some '}' then skip; break
    let name := (← takeWhile isNameChar).toLower
    if name.isEmpty then fail s!"expected a field of the entry `{key}`"
    if fields.any (·.1 == name) then fail s!"the field `{name}` of `{key}` is given twice"
    ws; expect '='; ws
    fields := fields.push (name, ← value)
    ws
    match ← peek? with
    | some ',' => skip
    | some '}' => skip; break
    | _ => fail s!"expected ',' or '}' after the field `{name}` of `{key}`"
  return some { type, key, fields }

/-- Every entry of a BibTeX file. As in BibTeX, the text between entries is ignored. -/
def bibFile : Parser (Array BibEntry) := do
  let mut entries := #[]
  repeat
    discard <| takeWhile (· != '@')
    if (← peek?).isNone then break
    if let some e ← entry then
      if entries.any (·.key == e.key) then fail s!"the key `{e.key}` is given twice"
      entries := entries.push e
  return entries

/-- The entries of the BibTeX file whose contents are `text`, or the reason it is malformed. -/
def parseBib (text : String) : Except String (Array BibEntry) :=
  match bibFile ⟨text, text.startPos⟩ with
  | .success _ entries => .ok entries
  | .error ⟨s, pos⟩ err =>
    .error s!"line {((FileMap.ofString s).toPosition pos.offset).line}: {err}"

/-! ### CSL-JSON -/

/-- `s` with each run of whitespace turned into one space, and none at the ends. -/
def squash (s : String) : String :=
  " ".intercalate ((s.splitToList Char.isWhitespace).filter (!·.isEmpty))

/-- `s` without its braces. -/
def unbrace (s : String) : String := (s.replace "{" "").replace "}" ""

/-- The pieces of `s` between the characters satisfying `sep` outside braces. -/
def splitTop (s : String) (sep : Char → Bool) : List String :=
  let (parts, cur, _) := s.foldl (init := (#[], "", 0)) fun (parts, cur, depth) c =>
    if depth == 0 && sep c then (parts.push cur, "", depth)
    else (parts, cur.push c, if c == '{' then depth + 1 else if c == '}' then depth - 1 else depth)
  (parts.push cur).toList

/-- A CSL-JSON name: `family` and `given` from `Last, First` or `First Last`, else `literal`. -/
def cslName (words : List String) : Json :=
  let name := " ".intercalate words
  let literal := json% { literal : $(unbrace name) }
  let person (family given : String) :=
    let family := squash (unbrace family)
    let given := squash (unbrace given)
    if family.isEmpty || given.isEmpty then literal
    else json% { family : $(family), given : $(given) }
  match splitTop name (· == ','), words.dropLast, words.getLast? with
  | [family, given], _, _ => person family given
  | [_], given@(_ :: _), some family => person family (" ".intercalate given)
  | _, _, _ => literal

/-- The CSL-JSON names of a BibTeX name list: names separated by ` and ` outside braces. -/
def cslNames (names : String) : Array Json :=
  let words := (splitTop (squash names) (· == ' ')).filter (!·.isEmpty)
  ((words.splitOn "and").filter (!·.isEmpty)).toArray.map cslName

/-- The CSL-JSON type of a BibTeX entry type. -/
def cslType : String → String
  | "article" => "article-journal"
  | "book" => "book"
  | "incollection" | "inbook" => "chapter"
  | "inproceedings" => "paper-conference"
  | "phdthesis" | "mastersthesis" => "thesis"
  | "techreport" => "report"
  | _ => "document"

/-- The DOI of a BibTeX entry, without the `https://doi.org/` that some entries write before it. -/
def BibEntry.doi? (e : BibEntry) : Option String :=
  (e.field? "doi").map fun d =>
    let d := squash d
    let resolvers := ["https://doi.org/", "http://doi.org/", "https://dx.doi.org/",
      "http://dx.doi.org/"]
    ((resolvers.findSome? (d.dropPrefix? ·)).map (·.toString)).getD d

/-- The CSL-JSON item of a BibTeX entry. -/
def BibEntry.csl (e : BibEntry) : Json :=
  let year := (e.field? "year").map squash |>.filter fun y => !y.isEmpty && y.all Char.isDigit
  (json% { id : $(e.key), type : $(cslType e.type) }).mergeObj <| Json.mkObj <|
    opt "title" ((e.field? "title").map fun t => squash (unbrace t)) ++
    opt "author" ((e.field? "author").map cslNames) ++
    opt "issued" (year.map fun y => json% { "date-parts" : [[$(y.toNat!)]] }) ++
    opt "DOI" e.doi? ++
    opt "URL" ((e.field? "url").map squash)

/-- The address of a BibTeX entry: its `url`, its DOI, or its place in Mathlib's bibliography. -/
def BibEntry.uri (e : BibEntry) : String :=
  match e.field? "url", e.doi? with
  | some url, _ => squash url
  | none, some doi => s!"https://doi.org/{doi}"
  | none, none =>
    "https://leanprover-community.github.io/mathlib4_docs/references.html#ref_" ++ e.key

/-- The entries of the BibTeX file `CITATIONS_BIB`, which must have those that `cites` cite. -/
def readBib (cites : Array Citation) : CoreM (Std.HashMap String BibEntry) := do
  unless cites.any (·.source matches .bib _) do return {}
  let path := (← IO.getEnv "CITATIONS_BIB").getD "docs/references.bib"
  let .ok text ← (IO.FS.readFile path).toBaseIO
    | throwError "cannot read the BibTeX file `{path}`"
  let entries ← match parseBib text with
    | .ok entries => pure entries
    | .error msg => throwError "the BibTeX file `{path}` is malformed: {msg}"
  let bib := Std.HashMap.ofList (entries.toList.map fun e => (e.key, e))
  let missing := cites.filterMap fun c => match c.source with
    | .bib key => if bib.contains key then none else some key
    | .source _ => none
  unless missing.isEmpty do
    throwError "the BibTeX file `{path}` has no entry for the keys cited: \
      {", ".intercalate missing.toList.eraseDups}"
  return bib

/-! ### Annotations -/

/-- The type of the entries of `s`: its field `type`, else `html` or, without `{id}`, `generic`. -/
def endType (s : Source) : String :=
  (s.field? "type").getD <| if s.uriTemplates.any (·.2.contains "{id}") then "html" else "generic"

/-- The Lean end of an annotation: the declaration `decl` of `module`, at `commit` of `repo`. -/
def leanEnd (decl : String) (module : Name) (repo commit : String) : Json :=
  json% { type : "lean", uri : $(repo), version : $(commit),
    location : { declaration : $(decl), module : $(module.toString) } }

/-- The `id` and subject end of the citation `c`, given the BibTeX entries `bib`. -/
def subject (bib : Std.HashMap String BibEntry) (c : Citation) : CoreM (String × Json) := do
  match c.source with
  | .source name =>
    let s ← findSource name
    let type := endType s
    unless endTypes.contains type do
      throwError "the field `type` of the source `{name}` is `{type}`, not one of \
        {", ".intercalate endTypes}"
    -- a database is identified by its short name, and another source by its field `registry`
    let registry? := (Database.ofSourceName? name).map (·.shortName) <|> s.field? "registry"
    if let some key := registry? then
      unless isIdentifiersKey key do
        throwError "the registry `{key}` of the source `{name}` is not a valid identifiers key"
    let subjectEnd := json% { type : $(type), uri : $(entryUri s.uriTemplates c.id),
      title : $(s!"{s.title} {c.id}") }
    return (s!"{name.toString (escape := false)}:{c.id}", subjectEnd.mergeObj <| Json.mkObj <|
      opt "identifiers" (registry?.map fun key => Json.mkObj [(key, toJson c.id)]))
  | .bib key =>
    -- `readBib` has checked that `bib` has every key cited
    let e := bib[key]!
    let uri := e.uri
    let subjectEnd := json% { type : $(if uri.toLower.endsWith ".pdf" then "pdf" else "html"),
      uri : $(uri), citation : $(e.csl) }
    return (if c.id.isEmpty then key else s!"{key}:{c.id}",
      subjectEnd.mergeObj <| Json.mkObj <| opt "title" (nonempty? c.id))

/-- The annotations of the citations `cites`, one JSON line each, sorted by `id`, then by
declaration. -/
def buildAnnotations (cites : Array Citation) (bib : Std.HashMap String BibEntry)
    (repo commit : String) : CoreM (Array String) := do
  let env ← getEnv
  let mut annotations := #[]
  let mut errors := #[]
  for c in cites do
    try
      let (id, subjectEnd) ← subject bib c
      let decl := (privateToUserName c.declName).toString
      let module := (env.getModuleFor? c.declName).getD env.mainModule
      let annotation := json% { id : $(id), subject : [$(subjectEnd)],
        object : [$(leanEnd decl module repo commit)] }
      let annotation := annotation.mergeObj <| Json.mkObj <| opt "note" (nonempty? c.comment)
      annotations := annotations.push (id, decl, annotation.compress)
    catch e => errors := errors.push (← e.toMessageData.toString)
  unless errors.isEmpty do
    throwError "cannot export the citations: {"; ".intercalate errors.toList.eraseDups}"
  -- a canonical order, by `id`, then declaration, keeps the published file stable
  let sorted := annotations.qsort fun a b =>
    (compare a.1 b.1 |>.then (compare a.2.1 b.2.1) |>.then (compare a.2.2 b.2.2)).isLT
  return sorted.map (·.2.2)

end ExportCitations

open ExportCitations in
run_cmd do
  let some commit := (← IO.getEnv "CITATIONS_COMMIT").filter (!·.isEmpty)
    | throwError "set `CITATIONS_COMMIT` to the commit that the Lean ends are pinned to"
  let repo := (← IO.getEnv "CITATIONS_REPO").getD "https://github.com/leanprover-community/mathlib4"
  let cites := citations (← getEnv)
  let annotations ← liftCoreM do buildAnnotations cites (← readBib cites) repo commit
  let path := (← IO.getEnv "CITATIONS_OUT").getD "citations.jsonl"
  IO.FS.writeFile path (String.join (annotations.toList.map (· ++ "\n")))
  logInfo m!"Wrote {annotations.size} Literature Links annotations to {path}"
