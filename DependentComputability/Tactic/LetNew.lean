import DependentComputability.SortExtra

open Lean Meta Parser Elab Term Tactic
partial def letNewHelper (goalType : Expr) (val : Expr) (baseMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM (Expr × MVarId) := do
  match val with
  | .letE nm t v b false =>
    let newType ← conversionStepNew.visit t baseMap
    let newValue ← conversionStepNew.visit v baseMap
    withLetDecl (nm.appendAfter "_base") t v fun var_base => do
    withLetDecl nm (mkExtraApp newType var_base) newValue fun var => do
      let (res, mvar) ← letNewHelper goalType (b.instantiate1 var_base)
        (baseMap.insert var_base.fvarId! var)
      return (← mkLetFVars #[var_base, var] res, mvar)
  | .letE nm t v b true =>
    let newType ← conversionStepNew.visit t baseMap
    let newValue ← conversionStepNew.visit v baseMap
    withLocalDeclD (nm.appendAfter "_base") t fun var_base => do
    withLocalDeclD nm (mkExtraApp newType var_base) fun var => do
      let (res, mvar) ← letNewHelper goalType (b.instantiate1 var_base)
        (baseMap.insert var_base.fvarId! var)
      return (mkApp2 (← mkLambdaFVars #[var_base, var] res) v newValue, mvar)
  | .lam nm t b bi =>
    let newType ← conversionStepNew.visit t baseMap
    withLocalDecl (nm.appendAfter "_base") bi t fun var_base => do
    withLocalDecl nm bi (mkExtraApp newType var_base) fun var => do
      let (res, mvar) ← letNewHelper goalType (b.instantiate1 var_base)
        (baseMap.insert var_base.fvarId! var)
      return (← mkLambdaFVars #[var_base, var] res, mvar)
  | .app f a =>
    if f.getAppFn.isMVar then
      let mvar ← Meta.mkFreshExprSyntheticOpaqueMVar goalType
      return (mvar, mvar.mvarId!)
    let (res, mvar) ← letNewHelper goalType f baseMap
    return (mkApp2 res a (← conversionStepNew.visit a baseMap), mvar)
  | .mvar _ =>
    let mvar ← Meta.mkFreshExprSyntheticOpaqueMVar goalType
    return (mvar, mvar.mvarId!)
  | _ => throwError "internal error"

def elabLetNewCore (cfg : TSyntax ``letConfig) (decl : TSyntax ``letDecl)
    (initConfig : LetConfig := {}) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let mvarIdent : Ident ← `(m)
    let goalType ← goal.getType
    let res ← runTermElab do
      let letTerm ← `(let $cfg:letConfig $decl:letDecl; ?$mvarIdent)
      elabLetDeclCore letTerm goalType initConfig
    let res ← instantiateMVars res
    let (result, newGoal) ← (letNewHelper goalType res (← populateBaseMap)).run
    goal.assign result
    replaceMainGoal [newGoal]

elab "let_new" cfg:letConfig decl:letDecl : tactic => elabLetNewCore cfg decl
elab "have_new" cfg:letConfig decl:letDecl : tactic => elabLetNewCore cfg decl { nondep := true }
