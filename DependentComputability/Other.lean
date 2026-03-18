import Lean

declare_syntax_cat myCat

open Lean Parser

def collectTokens (env : Environment) (cat : Name) (table : TokenTable) : TokenTable :=
  let state := parserExtension.getState env
  let cat := state.categories.find! cat
  let table := cat.tables.leadingParsers.foldl (init := table) fun acc (p, _) =>
    (p.info.collectTokens []).foldl (fun acc tk => acc.insert tk tk) acc
  let table := cat.tables.trailingParsers.foldl (init := table) fun acc (p, _) =>
    (p.info.collectTokens []).foldl (fun acc tk => acc.insert tk tk) acc
  let table := cat.tables.leadingTable.foldl (init := table) fun acc _ p =>
    p.foldl (init := acc) fun acc (p, _) =>
      (p.info.collectTokens []).foldl (fun acc tk => acc.insert tk tk) acc
  let table := cat.tables.trailingTable.foldl (init := table) fun acc _ p =>
    p.foldl (init := acc) fun acc (p, _) =>
      (p.info.collectTokens []).foldl (fun acc tk => acc.insert tk tk) acc
  table

def myCatParser : Parser := withFn (p := categoryParser `myCat 0) <| adaptUncacheableContextFn fun ctx =>
  let initTable : TokenTable := ["$", ":", "?", "*", "+", "(", ")", "[", "]", "%"].foldl (fun acc tk => acc.insert tk tk) {}
  let table : TokenTable := collectTokens ctx.env `myCat initTable
  { ctx with tokens := table }

def restoreTermParser : Parser := withFn (p := termParser) <| adaptUncacheableContextFn fun ctx =>
  { ctx with tokens := getTokenTable ctx.env }

elab "#test_me " stx:myCatParser : command => do
  Lean.logInfo stx

syntax "test " ident : myCat

#test_me test Type
#test_me test let
#test_me test def

syntax "abc " term : myCat

syntax "good " restoreTermParser : myCat
--syntax myCat " + " restoreTermParser : myCat

def collectTokens2 (env : Environment) (cat : Name) (table : TokenTable) : MetaM Unit := do
  let state := parserExtension.getState env
  let cat := state.categories.find! cat
  Lean.logInfo m!"{cat.tables.leadingParsers.length}"
  let table ← cat.tables.leadingParsers.foldlM (init := table) fun acc (p, _) => do
    return (p.info.collectTokens []).foldl (fun acc tk => acc.insert tk tk) acc
  let table ← cat.tables.trailingParsers.foldlM (init := table) fun acc (p, _) => do
    return (p.info.collectTokens []).foldl (fun acc tk => acc.insert tk tk) acc
  Lean.logInfo m!"{table.values}"

#eval termParser.info.collectKinds {} |>.toArray
#eval do return (collectTokens (← getEnv) `myCat {}).values

def test2 (stx : TSyntax ``myCatParser) : MacroM Syntax :=
  match stx with
  | `(myCatParser| $a:myCat) => `(myCatParser| $(a) + 5)

#test_me abc let a 5 Type oh no _ stop sorry do by

#test_me good let a := 5; 5
