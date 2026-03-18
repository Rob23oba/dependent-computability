import Lean

open Lean
structure DataEntry where
  decl : LocalDecl
  value : NonScalar

initialize dataExt : Lean.EnvExtension (Array DataEntry) ←
  registerEnvExtension (pure #[])

open Lean Parser Meta Elab Command

unsafe def getNthDataValue {α : Sort u} (data : Array DataEntry) (i : Nat) : α :=
  unsafeCast (data[i]'lcProof).value

elab tk:"#eval_set " nm:ident type:(Term.typeSpec)? " ← " code:term : command => do
  liftTermElabM do
  let dataEntries := dataExt.getState (← getEnv)
  withExistingLocalDecls (dataEntries.map (·.decl)).toList do
  let exTy : Expr ←
    if let some spec := type then
      let `(Term.typeSpec| : $ty) := spec | throwUnsupportedSyntax
      let type : Expr ← Term.elabTermEnsuringType ty (some <| .sort 1)
      pure type
    else
      let mvar ← mkFreshExprMVar (some <| .sort 1)
      pure mvar
  let actType := .app (mkConst ``TermElabM) exTy
  let act ← Term.elabTermEnsuringType code (some actType)
  Term.synthesizeSyntheticMVarsNoPostponing
  let act ← instantiateMVars act
  let actType ← instantiateMVars actType
  let exTy ← instantiateMVars exTy
  if (← Term.logUnassignedUsingErrorInfos (← getMVars act)) then throwAbortTerm
  if (← Term.logUnassignedUsingErrorInfos (← getMVars actType)) then throwAbortTerm
  let fvars := (← getLCtx).getFVars
  let lambda ← mkLambdaFVars fvars act
  let type ← mkForallFVars fvars actType
  let dataType := .app (.const ``Array [0]) (mkConst ``DataEntry)
  withLocalDeclD `data dataType fun data => do
    let mut lambda := lambda
    let mut type := type
    for i in *...fvars.size do
      let .forallE _ t b _ := type | unreachable!
      let u ← getLevel t
      let val := mkApp3 (.const ``getNthDataValue [u]) t data (toExpr i)
      lambda := .app lambda val
      type := b.instantiate1 val
    let name ← mkAuxDeclName `eval_set
    addAndCompile <| .defnDecl {
      name := name
      levelParams := []
      type := ← mkForallFVars #[data] type
      value := ← mkLambdaFVars #[data] lambda
      hints := .opaque
      safety := .unsafe
    }
    let res : Array DataEntry → TermElabM NonScalar ← unsafe evalConst _ name
    let val ← withRef tk <| res dataEntries
    withLocalDeclD nm.getId exTy fun value => do
      let decl ← value.fvarId!.getDecl
      Term.addTermInfo' nm value
      modifyEnv (dataExt.modifyState · fun entries => entries.push ⟨decl, val⟩)
