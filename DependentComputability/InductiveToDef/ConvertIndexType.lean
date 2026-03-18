import DependentComputability.InductiveToDef.BasicTypes
import Qq

namespace InductiveToDef

open Lean Meta

def mkPSigmaFVars (xs : Array Expr) (e : Expr) : MetaM (Expr × Level) := do
  let lvl ← getLevel e
  let e ← e.abstractM xs
  let lctx ← getLCtx
  xs.size.foldRevM (init := (e, lvl)) fun i _ (e, lvl) => do
    let x := xs[i]
    let handleCDecl (n : Name) (origType : Expr) (bi : BinderInfo) : MetaM (Expr × Level) := do
      let tlvl ← getLevel origType
      let type ← origType.abstractRangeM i xs
      return (mkApp2 (.const ``PSigma [tlvl, lvl]) type (.lam n type e bi), .normalize <| .max levelOne (.max tlvl lvl))
    match lctx.getFVar! x with
    | LocalDecl.cdecl _ _ n type bi _ =>
      handleCDecl n type bi
    | LocalDecl.ldecl _ _ n type value nondep _ =>
      let type  ← type.abstractRangeM i xs
      let value ← value.abstractRangeM i xs
      return (.letE n type value e nondep, lvl)

def instantiatePSigma (psigma : Expr) (xs : Array Expr) (i : Nat) (val : Expr) : Expr :=
  if i ≥ xs.size then val else
  match psigma with
  | .letE _ _ _ b _ => instantiatePSigma b xs (i + 1) val
  | mkApp2 (.const ``PSigma us) α β@(.lam _ _ b _) =>
    let α := α.instantiateRevRange 0 i xs
    let β := β.instantiateRevRange 0 i xs
    mkApp4 (.const ``PSigma.mk us) α β xs[i]! (instantiatePSigma b xs (i + 1) val)
  | _ => unreachable!

partial def mkRecUniv (lparams : List Name) : Name :=
  go `u 1
where
  go (nm : Name) (i : Nat) : Name :=
    if lparams.contains nm then
      go (.num `u i) (i + 1)
    else
      nm

def _root_.Lean.Expr.modifyLambdaBody (f : Expr → Expr) : Expr → Expr
  | .lam nm t b bi => .lam nm t (b.modifyLambdaBody f) bi
  | b => f b

partial def applyPSigmaN (e : Expr) (sigma : Expr) (n : Nat) : Expr :=
  if n = 1 then
    .app e sigma
  else
    applyPSigmaN (.app e (.proj ``PSigma 0 sigma)) (.proj ``PSigma 1 sigma) (n - 1)

/-- Returns `(type, recursor)` -/
partial def createIndexType (lparams : List Name) (params : Array Expr)
    (types : Array Expr) (ctorNames : Array Name) (typeName : Name) (isUnsafe : Bool) : MetaM Unit := do
  let recUniv := mkRecUniv lparams
  assert! types.size > 0
  let rec mkTypeBetween (start stop : Nat) : MetaM (Expr × Level × Array Expr) := do
    if start + 1 = stop then
      let type := types[start]!
      forallTelescope type fun vars _ => do
        if vars.isEmpty then
          return (.const ``Unit [], levelOne, #[mkConst ``Unit.unit])
        let back := vars.back!
        let type ← inferType back
        let (e, lvl) ← mkPSigmaFVars vars.pop type
        let ctor := instantiatePSigma e vars.pop 0 back
        return (e, lvl, #[← mkLambdaFVars vars ctor])
    else
      let mid := (start + stop) / 2
      let (left, llvl, lctors) ← mkTypeBetween start mid
      let (right, rlvl, rctors) ← mkTypeBetween mid stop
      let lctors := lctors.map (Expr.modifyLambdaBody <| mkApp3 (.const ``PSum.inl [llvl, rlvl]) left right)
      let rctors := rctors.map (Expr.modifyLambdaBody <|mkApp3 (.const ``PSum.inr [llvl, rlvl]) left right)
      return (mkApp2 (.const ``PSum [llvl, rlvl]) left right, .max levelOne (.max llvl rlvl), lctors ++ rctors)
  let (tyexpr, tylvl, ctors) ← mkTypeBetween 0 types.size
  let tylvl := tylvl.normalize
  let ty ← mkLambdaFVars params tyexpr
  let tyty ← mkForallFVars params (.sort tylvl)
  addDecl <| .defnDecl {
    name := typeName
    levelParams := lparams
    type := tyty
    value := ty
    hints := .abbrev
    safety := if isUnsafe then .unsafe else .safe
  }
  let ty := mkAppN (.const typeName (lparams.map Level.param)) params
  withNewBinderInfos (params.map (fun x => (x.fvarId!, .implicit))) do
  for type in types, ctor in ctors, nm in ctorNames do
    forallTelescope type fun vars _ => do
      let type ← mkForallFVars (params ++ vars) ty
      addDecl <| .defnDecl {
        name := nm
        levelParams := lparams
        type := type
        value := ← mkLambdaFVars params ctor
        hints := .abbrev
        safety := if isUnsafe then .unsafe else .safe
      }
  withLocalDecl `motive .implicit (.forallE `t ty (.sort (.param recUniv)) .default) fun motive => do
    let mut minors := #[]
    for type in types, nm in ctorNames do
      let minor ← forallTelescope type fun vars _ => do
        let ctorApp := mkAppN (.const nm (lparams.map Level.param)) params
        let ctorApp := mkAppN ctorApp vars
        return (nm.replacePrefix typeName .anonymous, ← mkForallFVars vars (.app motive ctorApp))
      minors := minors.push minor
    withLocalDeclsDND minors fun minors => do
    withLocalDeclD `t ty fun major => do
      let rec computeValue (motiveArg : Expr) (e : Expr) (start stop : Nat) : MetaM Expr := do
        if start + 1 = stop then
          let type := types[start]!
          let minor := minors[start]!
          forallTelescope type fun vars _ => do
            if vars.isEmpty then
              return .lam `t e minor .default
            return .lam `t e (applyPSigmaN minor (.bvar 0) vars.size) .default
        else
          let mid := (start + stop) / 2
          let mkApp2 (.const ``PSum us) left right := e | unreachable!
          let leftCase ← computeValue (mkApp3 (.const ``PSum.inl us) left right motiveArg) left start mid
          let rightCase ← computeValue (mkApp3 (.const ``PSum.inr us) left right motiveArg) right mid stop
          return mkApp5 (.const ``PSum.rec (.param recUniv :: us)) left right (.lam `t e (.app motive motiveArg) .default) leftCase rightCase
      let value ← computeValue (.bvar 0) tyexpr 0 types.size
      addDecl <| .defnDecl {
        name := mkRecName typeName
        levelParams := recUniv :: lparams
        type := ← mkForallFVars (params.push motive ++ minors |>.push major) (.app motive major)
        value := ← mkLambdaFVars (params.push motive ++ minors) value
        hints := .abbrev
        safety := if isUnsafe then .unsafe else .safe
      }

def createIndexTypeAsInduct (lparams : List Name) (params : Array Expr)
    (types : Array Expr) (ctorNames : Array Name) (typeName : Name) (isUnsafe : Bool) : MetaM Unit := do
  let (ctors, level) ← withNewBinderInfos (params.map (fun x => (x.fvarId!, .implicit))) do
    let mut ctors : Array Constructor := #[]
    let mut level := levelOne
    let ty := mkAppN (.const typeName (lparams.map Level.param)) params
    for type in types, name in ctorNames do
      let (type, newLevel) ← forallTelescope type fun vars _body => do
        let lvl ← vars.foldlM (init := level) (fun acc var => return .max acc <| ← getLevel (← inferType var))
        return (← mkForallFVars (params ++ vars) ty, lvl)
      ctors := ctors.push {
        name := name
        type
      }
      level := newLevel
    return (ctors, level)
  let level := level.normalize
  let ind : InductiveType := {
    name := typeName
    type := ← mkForallFVars params (.sort level)
    ctors := ctors.toList
  }
  addDecl <| .inductDecl lparams params.size [ind] isUnsafe

def addDeclIndexTypeWrapper (decl : Declaration) : MetaM Unit := do
  let .inductDecl lparams nparams inducts isUnsafe := decl | unreachable!
  let [induct] := inducts | throwError "Can't generate mutual index type"
  let types := induct.ctors.toArray.map (·.type)
  let ctorNames := induct.ctors.toArray.map (·.name)
  if induct.ctors.isEmpty then
    throwError "Expected at least one constructor"
  forallTelescope induct.type fun params _body => do
    unless nparams == params.size do
      throwError "Invalid nparams, expected {params.size} but found {nparams}"
    createIndexType lparams params (← types.mapM (instantiateForall · params)) ctorNames induct.name isUnsafe

open Lean Elab Command in
elab "index_type_inductive_decl " params:num inducts:rawInductive* : command => do
  liftTermElabM do
    elabRawInductiveDecl params.getNat inducts fun decl => do
      addDeclIndexTypeWrapper decl

syntax "without_modifying_env" (notFollowedBy("end") command)* "end" : command

open Elab Command in
elab_rules : command
  | `(without_modifying_env $[$cs:command]* end) =>
    withoutModifyingEnv do
      cs.forM elabCommand

without_modifying_env

index_type_inductive_decl 1
  raw_inductive MyType : Nat → Type
    | InductiveToDef.MyType.abc : (a : Nat) → (x : Nat) → (y : Fin x) → (z : Fin (x + y)) → MyType a
    | InductiveToDef.MyType.xyz : (a : Nat) → MyType a
    | InductiveToDef.MyType.thing : (a b : Nat) → MyType a

/-- info: InductiveToDef.MyType : Nat → Type -/
#guard_msgs in #check MyType
/--
info: InductiveToDef.MyType.abc {a✝ : Nat} (x : Nat) (y : Fin x) (z : Fin (x + ↑y)) : MyType a✝
-/
#guard_msgs in #check MyType.abc
/-- info: InductiveToDef.MyType.xyz {a✝ : Nat} : MyType a✝ -/
#guard_msgs in #check MyType.xyz
/--
info: InductiveToDef.MyType.rec.{u} {a✝ : Nat} {motive : MyType a✝ → Sort u}
  (abc : (x : Nat) → (y : Fin x) → (z : Fin (x + ↑y)) → motive (MyType.abc x y z)) (xyz : motive MyType.xyz)
  (thing : (b : Nat) → motive (MyType.thing b)) (t : MyType a✝) : motive t
-/
#guard_msgs in #check MyType.rec

end
