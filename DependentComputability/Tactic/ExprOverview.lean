import Lean

namespace ExprOverview

open Lean Meta Elab Tactic

structure State where
  exprs : ExprMap Nat
  out : String

abbrev M := StateM State

def printLine (s : String) : M Unit := do
  modify fun state => { state with out := state.out ++ s ++ "\n" }

def visit (e : Expr) : M Unit := do
  if let some val := (← get).exprs[e]? then
    return
  modify fun state => { state with exprs := state.exprs.insert e state.exprs.size }
  e.withApp fun f args => do
    match f with
    | .const nm us => sorry
    | _ => sorry

def dumpMDataEntry (entry : Name × DataValue) (acc : String) : String :=
  acc ++ entry.1.toString

def dumpMData (mdata : MData) (acc : String) : String :=
  match mdata.entries with
  | [] => acc
  | x :: xs => go xs (dumpMDataEntry x acc)
where
  go (entries : List (Name × DataValue)) (acc : String) : String :=
    match entries with
    | [] => acc
    | x :: xs => go xs (dumpMDataEntry x (acc ++ ", "))

def bindParenLeft (bi : BinderInfo) : Char :=
  match bi with
  | .default => '('
  | .implicit => '{'
  | .instImplicit => '['
  | .strictImplicit => '⦃'

def bindParenRight (bi : BinderInfo) : Char :=
  match bi with
  | .default => ')'
  | .implicit => '}'
  | .instImplicit => ']'
  | .strictImplicit => '⦄'

def printWithDepth (e : Expr) (depth : Nat) (acc : String := "") : String :=
  match depth with
  | 0 => acc ++ "_"
  | depth + 1 =>
    match e with
    | .const nm _ => acc ++ nm.toString
    | .proj _ i e => printWithDepth e depth acc ++ "." ++ i.repr
    | .mdata m e => printWithDepth e depth (dumpMData m (acc ++ "mdata{") ++ "} ")
    | .lit (.strVal s) => acc ++ s.quote
    | .lit (.natVal n) => acc ++ n.repr
    | .letE nm t v b nd =>
      let word := if nd then "have " else "let "
      let acc := acc ++ "(" ++ word ++ nm.toString ++ " : "
      let acc := printWithDepth t depth acc
      let acc := acc ++ " := "
      let acc := printWithDepth v depth acc
      let acc := acc ++ "; "
      printWithDepth b depth acc ++ ")"
    | .forallE nm t b bi =>
      let acc := acc ++ "(∀ ".push (bindParenLeft bi) ++ nm.toString ++ " : "
      let acc := printWithDepth t depth acc
      let acc := acc.push (bindParenRight bi) ++ ", "
      printWithDepth b depth acc ++ ")"
    | .lam nm t b bi =>
      let acc := acc ++ "(fun ".push (bindParenLeft bi) ++ nm.toString ++ " : "
      let acc := printWithDepth t depth acc
      let acc := acc.push (bindParenRight bi) ++ " => "
      printWithDepth b depth acc ++ ")"
    | .sort _ => acc ++ "Sort _"
    | .bvar i => acc ++ "#" ++ i.repr
    | .app .. =>
      e.withApp fun f args =>
        let acc := printWithDepth f depth (acc ++ "(")
        let acc := args.foldl (init := acc) fun acc arg =>
          printWithDepth arg depth (acc ++ " ")
        acc ++ ")"
    | .mvar _ => acc ++ "?_"
    | .fvar f => acc ++ f.name.toString

elab "dbg_exprs " depth:num : tactic => do
  let goal ← getMainGoal
  let type ← goal.getType
  Lean.logInfo (printWithDepth type depth.getNat)

end ExprOverview
