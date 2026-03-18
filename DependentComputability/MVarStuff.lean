import Lean

open Lean Elab Term in
elab tk:"show_mvar_by_id " id:num t:term : term => do
  let e ← elabTerm t ‹_›
  let mctx ← getMCtx
  let decl? := mctx.decls.toArray.find? fun (m, decl) => decl.index + 1 == id.getNat
  let some (mvar, decl) := decl? | throwError "could not find ?m.{id.getNat}"
  let opt := pp.instantiateMVars.name
  let withOpt (msg : MessageData) : MetaM MessageData := do
    withOptions (·.setBool opt false) do
      addMessageContext msg
  let kind := match decl.kind with
    | .natural => "Natural"
    | .synthetic => "Synthetic"
    | .syntheticOpaque => "Synthetic-opaque"
  mvar.withContext do
    let mut msg := m!"{kind} Metavariable {← withOpt <| Expr.mvar mvar} \
      (internal name {mvar.name}) at depth {decl.depth}{mvar}"
    if let some assigned ← getExprMVarAssignment? mvar then
      msg := msg ++ m!"Assigned to:{indentExpr assigned}\n"
    if let some assigned ← getDelayedMVarAssignment? mvar then
      msg ← assigned.mvarIdPending.withContext do
      let mvarInfo ← withOpt <| Expr.mvar assigned.mvarIdPending
      let fvars : MessageData := assigned.fvars.foldl (fun msg fvar => m!"{msg} {fvar}") ""
      let val := if assigned.fvars.isEmpty then m!"{mvarInfo}" else m!"fun{fvars} => {mvarInfo}"
      let val ← addMessageContext val
      pure <| msg ++ m!"Delayed assigned to: {val}\n"
    logInfoAt tk msg
    return e
