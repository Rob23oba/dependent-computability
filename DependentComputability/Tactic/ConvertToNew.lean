import DependentComputability.SortExtra
import DependentComputability.Tactic.Delab

open Lean Meta
@[inline]
def withNonBaseVars (baseVars : Array Expr)
    (step : (expr type : Expr) → (baseMap : FVarIdMap Expr) →
      MonadCacheT ExprStructEq Expr MetaM Expr)
    (k : Array Expr → FVarIdMap Expr → MonadCacheT ExprStructEq Expr MetaM α) : MetaM α := do
  (go 0 {} #[]).run
where
  go (i : Nat) (baseMap : FVarIdMap Expr) (newVars : Array Expr) :
      MonadCacheT ExprStructEq Expr MetaM α := do
    if h : i < baseVars.size then
      let varExpr := baseVars[i]
      let var := varExpr.fvarId!
      let decl ← var.getDecl
      let nm := decl.userName
      let type := decl.type
      let bi := decl.binderInfo
      let lctx ← getLCtx
      let lctx := lctx.setUserName var (nm.appendAfter "_base")
      let lctx := lctx.setBinderInfo var .implicit
      withLCtx' lctx do
        let newType ← step varExpr type baseMap
        withLocalDecl nm bi newType fun newVar => do
          go (i + 1) (baseMap.insert var newVar) (newVars.push newVar)
    else
      k newVars baseMap
  termination_by baseVars.size - i

def Array.interleave (as bs : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (acc : Array α) : Array α :=
    if h : i < as.size ∧ i < bs.size then
      go (i + 1) (acc.push as[i] |>.push bs[i])
    else
      acc
  termination_by as.size - i

def Array.steps (as : Array α) (start step : Nat) : Array α :=
  if h : step = 0 then
    #[]
  else
    go start #[] h
where
  go (i : Nat) (acc : Array α) (h : step ≠ 0) : Array α :=
    if h' : i < as.size then
      go (i + step) (acc.push as[i]) h
    else
      acc
  termination_by as.size - i

def convertTypeSimpleNew (e ty : Expr) (baseMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM Expr := do
  return .app (.proj ``SortExtra 0 (← conversionStepNew.visit ty baseMap)) e

def convertInductType (all : List Name) (e ty : Expr) (baseMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM Expr := do
  if ty.find? (fun | .const nm _ => all.contains nm | _ => false) |>.isSome then
    forallTelescopeReducing (whnfType := true) ty fun baseVars body => do
      withNonBaseVars.go baseVars convertTypeSimpleNew
          (i := 0) (newVars := #[]) (baseMap := baseMap) fun newVars baseMap => do
        body.withApp fun fn args => do
          let .const nm us := fn | throwError "unsupported {fn}"
          unless all.contains nm do
            throwError "unsupported {nm} (2)"
          let newArgs ← args.mapM (fun arg => conversionStepNew.visit arg baseMap)
          let fullArgs := args.interleave newArgs
          let eapp := mkAppN e baseVars
          let body := .app (mkAppN (.const (mkNewInductName nm) us) fullArgs) eapp
          mkForallFVars (baseVars.interleave newVars) body
  else
    convertTypeSimpleNew e ty baseMap

partial def addNewTypeDecl (info : InductiveVal) : MetaM Unit := do
  let ind := info.name
  let lparams' := info.levelParams.map Level.param
  let const := .const ind lparams'
  let newType ← conversionStepNew info.type
  let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
  let newValue ← forallTelescopeReducing info.type fun baseVars _body => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars _baseMap => do
      let allVars := baseVars.interleave newVars
      let indTy := mkAppN const baseVars
      let u ← getLevel indTy
      let extra := mkAppN (.const (mkNewInductName ind) lparams') allVars
      let encoding := mkApp2 (.const ``TrivialEncoding [u]) indTy extra
      let propElim := mkApp2 (.const ``IsPropEncodingTrivial.trivialEncoding [u]) indTy extra
      let constructor := mkApp4 (.const ``SortExtra.mk [u]) indTy extra encoding propElim
      mkLambdaFVars allVars constructor
  addDecl <| .defnDecl {
    name := mkNewName ind
    levelParams := info.levelParams
    type := newType'
    value := newValue
    hints := .abbrev
    safety := .safe
  }

partial def addNewCtorDecls (info : InductiveVal) : MetaM Unit := do
  let ind := info.name
  let lparams' := info.levelParams.map Level.param
  let newName := mkNewInductName ind
  for ctor in info.ctors do
    let newCtorName := newName ++ ctor.replacePrefix ind .anonymous
    let ctor ← getConstInfoCtor ctor
    let const := .const ctor.name lparams'
    let newType ← conversionStepNew ctor.type
    let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
    let newValue : Expr := .const newCtorName lparams'
    addDecl <| .defnDecl {
      name := `New ++ ctor.name
      levelParams := info.levelParams
      type := newType'
      value := newValue
      hints := .abbrev
      safety := .safe
    }

partial def addNewRecursor (ind : Name) (info : RecursorVal) (recNames : Array Name) :
    MetaM Unit := do
  let nparams := info.numParams
  let lparams' := info.levelParams.map Level.param
  let const := .const info.name lparams'
  let newType ← conversionStepNew info.type
  let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
  let newValue ← forallTelescope info.type fun baseVars _ => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars baseMap => do
      let allVars := baseVars.interleave newVars
      let recConst : Expr := .const (mkRecName (mkNewInductName ind)) lparams'
      let params := allVars.extract 0 (nparams * 2)
      let baseMotives := baseVars.extract nparams (nparams + info.numMotives)
      let motives := newVars.extract nparams (nparams + info.numMotives)
      let baseMinors := baseVars.extract (nparams + info.numMotives)
        (nparams + info.numMotives + info.numMinors)
      let minors := newVars.extract (nparams + info.numMotives)
        (nparams + info.numMotives + info.numMinors)
      let recBaseParams := baseVars.extract 0 info.getFirstIndexIdx
      let mut newMotives := #[]
      for motive in motives, recName in recNames do
        let type ← inferType motive
        let newMotive ← forallTelescopeReducing type fun vars _ => do
          let sortExtra := mkAppN motive vars
          let recApp : Expr := mkAppN (.const recName lparams') recBaseParams
          let recApp := mkAppN recApp (vars.steps 0 2)
          let res := .app (.proj ``SortExtra 0 sortExtra) recApp
          mkLambdaFVars vars res
        newMotives := newMotives.push newMotive
      let mut newMinors := #[]
      for baseMinor in baseMinors, minor in minors do
        let type ← inferType baseMinor
        let newMinor ← forallTelescopeReducing type fun vars _ => do
          let nonIHVars ← vars.filterM (fun var =>
            return !baseMotives.contains (← inferType var).getForallBody.getAppFn)
          if nonIHVars.size = vars.size then
            -- non-recursive
            return minor
          withNonBaseVars.go nonIHVars convertTypeSimpleNew
              (i := 0) (baseMap := baseMap) (newVars := #[]) fun newVars baseMap => do
            let allNonIHVars := nonIHVars.interleave newVars
            let res := mkAppN minor allNonIHVars
            let ihVars := vars.drop nonIHVars.size
            let rec mkRecGo (i : Nat) (vars : Array Expr) (res : Expr) :
                MonadCacheT ExprStructEq Expr MetaM Expr := do
              if h : i < ihVars.size then
                let ihVar := ihVars[i].fvarId!
                let decl ← ihVar.getDecl
                let type := decl.type
                let name := decl.userName
                let val ← forallTelescope type fun vars body => do
                  body.withApp fun fn args => do
                    let idx := baseMotives.idxOf fn
                    let recName := recNames[idx]!
                    let recApp := mkAppN (.const recName lparams') recBaseParams
                    let recApp := mkAppN recApp args
                    mkLambdaFVars vars recApp
                let newType ← convertTypeSimpleNew val type baseMap
                withLocalDeclD name newType fun newVar => do
                  mkRecGo (i + 1) (vars.push newVar) (mkApp2 res val newVar)
              else
                mkLambdaFVars vars res
            mkRecGo 0 allNonIHVars res
        newMinors := newMinors.push newMinor
      let majors := allVars.extract
        (nparams * 2 + info.numMotives * 2 + info.numMinors * 2)
      let recArgs := params ++ newMotives ++ newMinors ++ majors
      let value := mkAppN recConst recArgs
      mkLambdaFVars allVars value
  addDecl <| .defnDecl {
    name := mkNewName info.name
    levelParams := info.levelParams
    type := newType'
    value := newValue
    hints := .abbrev
    safety := .safe
  }

def convertStructCtorType (ind : Name) (e : Expr) (ctorType : Expr) (baseMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM Expr := do
  forallTelescope ctorType fun baseVars body => do
    withNonBaseVars.go baseVars convertTypeSimpleNew
        (i := 0) (baseMap := baseMap) (newVars := #[]) fun newVars baseMap => do
      body.withApp fun indConst indArgs => do
        assert! indConst.isConstOf ind
        let newArgs ← indArgs.mapM (fun arg => conversionStepNew.visit arg baseMap)
        let fullArgs := indArgs.interleave newArgs
        let newIndApp := .app (mkAppN
          (.const (mkNewInductName ind) indConst.constLevels!) fullArgs) e
        let res ← mkForallFVars newVars newIndApp
        return res.replaceFVars baseVars (Array.ofFn fun i : Fin baseVars.size => .proj ind i e)

def mkNewStructRecursor (rec : RecursorVal) (ctor : ConstructorVal) : MetaM Unit := do
  let levels := rec.levelParams.map Level.param
  let newRecType := mkExtraApp (← conversionStepNew rec.type) (.const rec.name levels)
  forallTelescope rec.type fun vars _body => do
  withNonBaseVars vars convertTypeSimpleNew fun newVars _baseMap => do
    let params := vars.take rec.numParams
    let newMotive := newVars[rec.numParams]!
    let minor := vars[rec.numParams + 1]!
    let newMinor := newVars[rec.numParams + 1]!
    let major := vars[rec.numParams + 2]!
    let newMajor := newVars[rec.numParams + 2]!
    let recApp := mkAppN (.const rec.name levels) vars
    let newResultType := mkExtraApp (mkApp2 newMotive major newMajor) recApp
    let ourMotive ← mkLambdaFVars #[major] (← mkForallFVars #[newMajor] newResultType)
    let lvl ← getLevel (← inferType major)
    let ourRecApp := .const rec.name (levels.modifyHead lvl.imax)
    let ourRecApp := mkAppN ourRecApp params
    let ourRecApp := ourRecApp.app ourMotive
    let ourMinor ← forallTelescope (← inferType minor) fun fields body => do
      let .app _motive motiveArg := body | throwError "internal error"
      let newMajorType := (← inferType newMajor).replaceFVar major motiveArg
      withLocalDeclD `t newMajorType fun newMajor => do
        let newFields := Array.ofFn fun n : Fin fields.size =>
          .proj (mkNewInductName ctor.induct) n newMajor
        let value := mkAppN newMinor (fields.interleave newFields)
        mkLambdaFVars (fields.push newMajor) value
    let ourRecApp := ourRecApp.app ourMinor
    let vars := (vars.interleave newVars).take ((vars.size - 1) * 2)
    let value ← mkLambdaFVars vars ourRecApp
    addDecl <| .defnDecl {
      name := mkNewName rec.name
      levelParams := rec.levelParams
      type := newRecType
      value := value
      hints := .abbrev
      safety := .safe
    }

mutual

partial def convertStructureType (info : InductiveVal) : MetaM Unit := do
  let ind := info.name
  let lparams' := info.levelParams.map Level.param
  for c in info.type.getUsedConstantsAsSet do
    recConvertToNew c
  let indType ← forallTelescopeReducing info.type fun baseVars body => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars _ => do
      let body := .forallE `t (mkAppN (.const ind lparams') baseVars) body .default
      mkForallFVars (baseVars.interleave newVars) body
  let newName := mkNewInductName info.name
  let ctor := info.ctors[0]!
  let newCtorName := newName ++ ctor.replacePrefix ind .anonymous
  let ctor ← getConstInfoCtor ctor
  for c in ctor.type.getUsedConstantsAsSet do
    if c != ind then
      recConvertToNew c
  let ctorType ← forallTelescopeReducing info.type fun baseVars _ => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars baseMap => do
      let indVarType := mkAppN (.const ind lparams') baseVars
      withLocalDeclD `t indVarType fun indVar => do
        let ctorType ← instantiateForall ctor.type baseVars
        let ctorType ← convertStructCtorType ind indVar ctorType baseMap
        mkForallFVars (baseVars.interleave newVars |>.push indVar) ctorType
  let indType := {
    name := newName
    type := indType
    ctors := [{
      name := newCtorName
      type := ctorType
    }]
  }
  addDecl <| .inductDecl info.levelParams (info.numParams * 2 + 1) [indType] info.isUnsafe
  mkCasesOn newName
  addNewTypeDecl info
  let const := .const ctor.name lparams'
  let newType ← conversionStepNew ctor.type
  let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
  let newValue : Expr ← forallTelescope ctor.type fun baseVars _ => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars _ => do
      let allVars := baseVars.interleave newVars
      let allParams := allVars.take (info.numParams * 2)
      let newFields := newVars.drop info.numParams
      let ctorApp := mkAppN const baseVars
      let res := mkAppN (.app (mkAppN (.const newCtorName lparams') allParams) ctorApp) newFields
      mkLambdaFVars allVars res
  addDecl <| .defnDecl {
    name := `New ++ ctor.name
    levelParams := info.levelParams
    type := newType'
    value := newValue
    hints := .abbrev
    safety := .safe
  }
  let rec ← getConstInfoRec (mkRecName info.name)
  mkNewStructRecursor rec ctor

partial def toNewInductiveType (info : InductiveVal) : MetaM InductiveType := do
  if info.isNested then
    throwError "nested {info.name} not supported"
  let ind := info.name
  let all := info.all
  let lparams' := info.levelParams.map Level.param
  for c in info.type.getUsedConstantsAsSet do
    recConvertToNew c
  let indType ← forallTelescopeReducing info.type fun baseVars body => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars _ => do
      let body := .forallE `t (mkAppN (.const ind lparams') baseVars) body .default
      mkForallFVars (baseVars.interleave newVars) body
  let newName := mkNewInductName info.name
  let mut ctors : Array Constructor := #[]
  for ctor in info.ctors do
    let newCtorName := newName ++ ctor.replacePrefix ind .anonymous
    let ctor ← getConstInfoCtor ctor
    for c in ctor.type.getUsedConstantsAsSet do
      unless all.contains c do
        recConvertToNew c
    let ctorType ← forallTelescopeReducing ctor.type fun baseVars body => do
      withNonBaseVars baseVars (convertInductType all) fun newVars baseMap => do
        let ctorApp := mkAppN (.const ctor.name lparams') baseVars
        let body ← convertInductType all ctorApp body baseMap
        mkForallFVars (baseVars.interleave newVars) body
    let newCtor : Constructor := {
      name := newCtorName
      type := ctorType
    }
    ctors := ctors.push newCtor
  return {
    name := newName
    type := indType
    ctors := ctors.toList
  }

partial def convertInductToNew (val : InductiveVal) : MetaM Unit := do
  if let [_] := val.ctors then
    unless val.isRec do
      if val.numIndices = 0 then
        let recVal ← getConstInfoRec (mkRecName val.name)
        if recVal.levelParams.length > val.levelParams.length then
          convertStructureType val
          return
  let all := val.all
  let lparams := val.levelParams
  let nparams := val.numParams
  let recNames := all.toArray.map mkRecName
  let mut types : Array InductiveType := #[]
  for ind in all do
    types := types.push (← toNewInductiveType (← getConstInfoInduct ind))
  let decl : Declaration := .inductDecl lparams (nparams * 2) types.toList val.isUnsafe
  addDecl decl
  for ind in all do
    mkCasesOn (mkNewInductName ind)
    let info ← getConstInfoInduct ind
    addNewTypeDecl info
  for ind in all do
    let info ← getConstInfoInduct ind
    addNewCtorDecls info
    let info ← getConstInfoRec (mkRecName ind)
    addNewRecursor ind info recNames

partial def recConvertToNew (nm : Name) : CoreM Unit := do
  try
    if (← getEnv).contains (mkNewName nm) then
      return
    let info ← getConstInfo nm
    match info with
    | .defnInfo val =>
      let type := val.type
      let value := val.value
      Meta.MetaM.run' do
        let consts := type.getUsedConstantsAsSet.merge value.getUsedConstantsAsSet
        for c in consts do
          recConvertToNew c
        let newType ← conversionStepNew type
        let newValue ← conversionStepNew value
        let newType' : Expr := .app (.proj ``SortExtra 0 newType)
          (.const val.name (val.levelParams.map Level.param))
        Lean.addDecl <| .defnDecl {
          name := mkNewName nm
          levelParams := val.levelParams
          type := newType'
          value := newValue
          hints := val.hints
          safety := val.safety
        }
    | .thmInfo val =>
      let type := val.type
      for c in type.getUsedConstantsAsSet do
        recConvertToNew c
      Meta.MetaM.run' do
        let newType ← conversionStepNew type
        let const := .const val.name (val.levelParams.map Level.param)
        let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
        -- attempt transfer
        let instType := mkApp2 (.const ``NonemptyExtra [levelZero]) type newType
        let mut newValue := default
        if let some inst ← synthInstance? instType then
          newValue := mkApp4 (.const ``NonemptyExtra.transfer []) type newType inst const
        else
          let value := val.value
          let consts := value.getUsedConstantsAsSet
          for c in consts do
            recConvertToNew c
          newValue ← conversionStepNew value
        Lean.addDecl <| .thmDecl {
          name := mkNewName nm
          levelParams := val.levelParams
          type := newType'
          value := newValue
        }
    | .inductInfo val => (convertInductToNew val).run'
    | .ctorInfo val => recConvertToNew val.induct
    | _ => throwError "unhandled const info {.ofConstName nm}"
  catch ex =>
    let msg := ex.toMessageData ++ m!"\nin {.ofConstName nm}"
    throwError msg

end

elab "convert_to_new " id:ident : command => do
  Lean.Elab.Command.liftCoreM do
    let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    if (← getEnv).contains (mkNewName name) then
      logWarning m!"{name} has already been translated"
    else
      recConvertToNew name

/-!
Essentials
-/

noncomputable opaque uniqueChoice (h : Nonempty α) : Squash α :=
  .mk (Classical.choice h)

namespace New

protected def Nat : new_type% Nat :=
  .mk (fun _ => Unit) (fun {n} _ m => n = m) (IsPropEncodingTrivial.univElim.{0} _)

protected def Nat.zero : new_type% @Nat.zero := ()
protected def Nat.succ : new_type% @Nat.succ := fun _ _ => ()

protected def Nat.rec.{u} : new_type% @Nat.rec.{u} :=
  fun {_} _ {_} zero {_} succ {t_base} _ => t_base.rec zero fun _ ih => succ () ih

protected def PUnit.{u} : new_type% @PUnit.{u} :=
  .mk (fun _ => PUnit.{u}) (TrivialEncoding _) (.trivialEncoding _)

protected def PUnit.unit.{u} : new_type% @PUnit.unit.{u} :=
  @_root_.PUnit.unit.{u}

convert_to_new Iff
convert_to_new Eq

protected theorem propext : new_type% @propext := by
  intro p_base p q_base q h_base h
  dsimp only
  cases propext h_base
  rcases p with ⟨pty, penc, pelim⟩
  rcases q with ⟨qty, qenc, qelim⟩
  cases pelim.eq
  cases qelim.eq
  rcases h with ⟨hmp, hmpr⟩
  have : pty = qty := by
    ext h
    exact ⟨@hmp h, @hmpr h⟩
  cases this
  constructor

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
set_option genInjectivity false in
inductive Quot._base {α_base : Sort u} {α : new_type% α_base}
    {r_base : α_base → α_base → Prop} (r : new_type% r_base) :
    Quot r_base → Sort u where
  | mk {a_base : α_base} (a : α.1 a_base) : _base r (Quot.mk r_base a_base)

inductive Quot._rel {α_base : Sort u} {α : new_type% α_base}
    {r_base : α_base → α_base → Prop} (r : new_type% r_base) :
    (q : Quot r_base) → Quot._base r q → Quot._base r q → Prop where
  | mk {a_base : α_base} (a : α.1 a_base) {b_base : α_base} (b : α.1 b_base)
    {h_base : r_base a_base b_base} (h : (r a b).1 h_base) :
    _rel r (Quot.mk r_base b_base) (Quot.sound h_base ▸ .mk a) (.mk b)

inductive Quot._encoding {α_base : Sort u} {α : new_type% α_base}
    {r_base : α_base → α_base → Prop} (r : new_type% r_base) :
    ⦃q_base : Quot r_base⦄ → (q : Quot (_rel r q_base)) → (n : ℕ) → Prop where
  | mk {a_base : α_base} {a : α.1 a_base} {n : ℕ} (h : α.2 a n) :
    @_encoding α_base α r_base r (Quot.mk r_base a_base) (Quot.mk _ (.mk a)) n

protected def Quot.{u} : new_type% @Quot.{u} := fun α_base α r_base r =>
  .mk (fun q => Quot (Quot._rel r q)) (Quot._encoding r) <| by
    intro hprop a_base a n
    simp only [trivialEncoding_iff]
    constructor
    · rintro ⟨h⟩
      simpa using (α.3 hprop _ _).mp h
    · rintro rfl
      rcases a with ⟨@⟨a_base, a'⟩⟩
      constructor
      exact (α.3 hprop _ _).mpr .zero

protected def Quot.mk.{u} : new_type% @Quot.mk.{u} := fun _ _ _ _ _ a =>
  _root_.Quot.mk _ (.mk a)

protected theorem Quot.ind.{u} : new_type% @Quot.ind.{u} := by
  intro α_base α r_base r motive_base motive mk_base mk t_base t
  rcases t with ⟨@⟨t_base, t⟩⟩
  apply mk

protected def Quot.lift.{u, v} : new_type% @Quot.lift.{u, v} :=
  fun α_base α r_base r β_base β f_base f h_base h q_base q =>
    _root_.Quot.lift (fun x : _base r q_base =>
      haveI : _root_.Quot.lift f_base h_base q_base = f_base x.1 := by
        rcases x with @⟨a_base, a⟩
        rfl
      this ▸ f x.2) ?_ q
where finally
  rintro _ _ @⟨a_base, a, b_base, b, hab_base, hab⟩
  dsimp only
  rw! (castMode := .all) [← Quot.sound hab_base]
  change h_base a_base b_base hab_base ▸ f a = f b
  refine (h a b hab).rec ?_
  rfl

protected theorem Quot.sound.{u} : new_type% @Quot.sound.{u} := by
  intro α_base α r_base r a_base a b_base b h_base h
  dsimp only
  have sound_base := _root_.Quot.sound h_base
  have sound := _root_.Quot.sound (Quot._rel.mk a b h)
  simp only [Quot.mk]
  rw! [← sound, ← sound_base]
  constructor

convert_to_new funext
convert_to_new Quotient.exact'

convert_to_new Nonempty
convert_to_new Squash.mk
convert_to_new instSubsingletonSquash

theorem _root_.subsingletonExtra_of_subsingleton
    {α_base : Sort u} (α : New.Sort.1 α_base)
    {h_base : _root_.Subsingleton α_base} (h : new_type% h_base) :
    SubsingletonExtra α := by
  constructor
  intro x
  constructor
  intro a b
  cases h.1 a b
  rfl

instance {α_base : Sort u} (α : New.Sort.1 α_base) : SubsingletonExtra (Squash α) :=
  subsingletonExtra_of_subsingleton _ (instSubsingletonSquash α)

protected noncomputable def uniqueChoice.{u} : new_type% @uniqueChoice.{u} :=
  fun α_base α h_base h =>
    haveI : _root_.Nonempty ((a : α_base) ×' α.1 a) := by
      obtain @⟨a_base, a⟩ := h
      exact ⟨a_base, a⟩
    (uniqueChoice this).liftOn (fun x =>
        haveI : uniqueChoice h_base = _root_.Squash.mk x.1 := Subsingleton.allEq ..
        this ▸ Squash.mk _ x.2) (by intros; apply Subsingleton.allEq)

end New

instance {α_base : Sort u} (α : new_type% α_base) [SubsingletonExtra α]
    {a_base : α_base} (a : α.1 a_base)
    {b_base : α_base} (b : α.1 b_base) :
    NonemptyExtra (New.Eq α a b) where
  nonempty := by
    rintro rfl
    cases (SubsingletonExtra.subsingleton a_base).allEq a b
    constructor
    constructor

instance : UniqueExtra New.Nat where
  default _ := ()
  subsingleton _ := inferInstanceAs (Subsingleton Unit)

def uniqueNatVal (n : Nat) : new_type% n := ()

inductive New.Subtype._induct {α_base : Sort u} {α : new_type% α_base}
    {p_base : α_base → Prop} (p : new_type% p_base) (t : Subtype p_base) where
  | mk (val : α.1 t.1) (property : (p val).1 t.2)

inductive New.Subtype._encoding {α_base : Sort u} {α : new_type% α_base}
    {p_base : α_base → Prop} (p : new_type% p_base)
    ⦃t_base : Subtype p_base⦄ (t : _induct p t_base) (n : ℕ) : Prop where
  | mk (val_enc : α.2 t.1 n)

def New.Subtype : new_type% @Subtype.{u} := fun _ _ _ p =>
  .mk (Subtype._induct p) (Subtype._encoding p) (.univElim _)

def New.Subtype.mk : new_type% @Subtype.mk.{u} :=
  fun _ _ _ _ _ x _ y => ⟨x, y⟩

def New.Subtype.rec.{v, u} : new_type% @Subtype.rec.{v, u} :=
  fun _ _ _ _ _ _ _ intro _ t => intro t.1 t.2

@[simp]
theorem encoding_subtype_def {α_base : Sort u} {α : new_type% α_base}
    {p_base : α_base → Prop} {p : new_type% p_base}
    {t_base : Subtype p_base} {t : new_type% t_base} {n : ℕ} :
    (new% Subtype p_base).2 t n ↔ α.2 t.1 n := by
  constructor
  · rintro ⟨h⟩
    exact h
  · intro h
    exact ⟨h⟩

inductive New.List._induct {α_base : Type u} (α_extra : α_base → Type u) :
    List α_base → Type u where
  | nil : _induct α_extra []
  | cons {head_base : α_base} (head : α_extra head_base)
    {tail_base : List α_base} (tail : _induct α_extra tail_base) :
    _induct α_extra (head_base :: tail_base)

inductive New.List._encoding {α_base : Type u}
    (α_extra : α_base → Type u) (α_enc : ⦃t_base : α_base⦄ → α_extra t_base → ℕ → Prop) :
    ⦃l_base : List α_base⦄ → _induct α_extra l_base → ℕ → Prop where
  | nil : _encoding α_extra α_enc .nil .zero
  | cons {head_base : α_base} {head : α_extra head_base}
    {head_n : ℕ} (head_enc : α_enc head head_n)
    {tail_base : List α_base} {tail : _induct α_extra tail_base}
    {tail_n : ℕ} (tail_enc : _encoding α_extra α_enc tail tail_n) :
    _encoding α_extra α_enc (.cons head tail) (.succ (Nat.pair head_n tail_n))

def New.List : new_type% @List.{u} :=
  fun _ α => .mk (New.List._induct α.1) (New.List._encoding α.1 α.2)
    (IsPropEncodingTrivial.univElim.{u + 1} _)

def New.List.nil : new_type% @List.nil.{u} :=
  fun _ α => @New.List._induct.nil _ α.1

def New.List.cons : new_type% @List.cons.{u} :=
  fun _ α => @New.List._induct.cons _ α.1

noncomputable def New.List.rec.{u, v} : new_type% @List.rec.{u, v} :=
  fun _ _ _ _ _ nil _ cons _ t => t.rec nil (fun _ _ _ ih => cons _ _ ih)

set_option inductive.autoPromoteIndices false in
inductive New.Array._induct {α_base : Type u} (α_extra : α_base → Type u)
    (t : Array α_base) : Type u where
  | mk (toList : New.List._induct α_extra t.1) : _induct α_extra t

inductive New.Array._encoding {α_base : Type u}
    (α_extra : α_base → Type u) (α_enc : ⦃t_base : α_base⦄ → α_extra t_base → ℕ → Prop)
    ⦃l_base : Array α_base⦄ (l : _induct α_extra l_base) (n : ℕ) : Prop where
  | mk (toList : New.List._encoding α_extra α_enc l.1 n)

def New.Array : new_type% @Array.{u} :=
  fun _ α => .mk (New.Array._induct α.1) (New.Array._encoding α.1 α.2)
    (IsPropEncodingTrivial.univElim.{u + 1} _)

def New.Array.mk : new_type% @Array.mk.{u} :=
  fun _ α _ toList => @New.Array._induct.mk _ α.1 _ toList

def New.Array.rec.{u, v} : new_type% @Array.rec.{u, v} :=
  fun _ _ _ _ _ mk _ t => mk t.1

convert_to_new String

instance {α_base : Type u} {α : new_type% α_base} [SubsingletonExtra α] :
    SubsingletonExtra (New.List α) where
  subsingleton t_base := by
    constructor
    intro t₁ t₂
    induction t₁ with
    | nil => cases t₂; rfl
    | cons head tail ih =>
      rcases t₂ with _ | ⟨head', tail'⟩
      cases Subsingleton.allEq head head'
      cases ih tail'
      rfl

instance {α_base : Type u} {α : new_type% α_base} [UniqueExtra α] : UniqueExtra (New.List α) where
  default t_base := t_base.rec .nil fun head _ ih => .cons (UniqueExtra.default head) ih

instance {α_base : Type u} {α : new_type% α_base} [SubsingletonExtra α] :
    SubsingletonExtra (New.Array α) where
  subsingleton t_base := by
    constructor
    intro t₁ t₂
    refine congrArg New.Array._induct.mk ?_
    apply Subsingleton.allEq (α := new_type% t_base.1)

instance {α_base : Type u} {α : new_type% α_base} [UniqueExtra α] : UniqueExtra (New.Array α) where
  default t_base := t_base.rec fun a => .mk
    (show new_type% a from UniqueExtra.default (α := New.List α) a)

def nonemptyExtraOfDecidable {p_base : Prop} {p : new_type% p_base}
    {h_base : Decidable p_base} (h : new_type% h_base) :
    NonemptyExtra p where
  nonempty t_base := by
    cases h
    · contradiction
    · constructor; assumption

instance {n_base : ℕ} {n : new_type% n_base} {m_base : ℕ} {m : new_type% m_base} :
    NonemptyExtra (@New.Nat.le n_base n m_base m) :=
  nonemptyExtraOfDecidable (new% Nat.decLe n_base m_base)

instance {n_base : ℕ} {n : new_type% n_base} {m_base : ℕ} {m : new_type% m_base} :
    NonemptyExtra (new% n_base ≤ m_base) := instNonemptyExtraLeLe

instance {n_base : ℕ} {n : new_type% n_base} {m_base : ℕ} {m : new_type% m_base} :
    NonemptyExtra (new% n_base < m_base) := instNonemptyExtraLeLe

instance {n_base : ℕ} {n : new_type% n_base} : UniqueExtra (@New.Fin n_base n) where
  subsingleton t_base := by
    constructor
    rintro ⟨⟩ ⟨⟩; rfl
  default t_base :=
    .mk _ _ () (NonemptyExtra.transfer (@New.Nat.le t_base.succ () n_base ()) t_base.2)

instance {n_base : ℕ} {n : new_type% n_base} : UniqueExtra (@New.BitVec n_base n) where
  subsingleton t_base := by
    constructor
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩; rfl
  default t_base := .ofFin _ _ (UniqueExtra.default (α := new% Fin (Nat.pow 2 n_base)) t_base.1)

instance : UniqueExtra New.UInt8 where
  subsingleton t_base := by
    constructor
    rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl
  default t_base := .ofBitVec _ (UniqueExtra.default (α := new% BitVec 8) t_base.1)

instance : UniqueExtra New.UInt32 where
  subsingleton t_base := by
    constructor
    rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl
  default t_base := .ofBitVec _ (UniqueExtra.default (α := new% BitVec 32) t_base.1)

convert_to_new inferInstance
convert_to_new instDecidableOr
convert_to_new instDecidableAnd

instance {n_base : UInt32} (n : new_type% n_base) :
    NonemptyExtra (New.UInt32.isValidChar n) :=
  nonemptyExtraOfDecidable (new% (inferInstance : Decidable (UInt32.isValidChar n_base)))

instance : UniqueExtra New.Char where
  subsingleton t_base := by
    constructor
    rintro ⟨⟨⟨⟨⟩⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl
  default t_base := .mk _ (UniqueExtra.default (α := New.UInt32) t_base.1)
    (NonemptyExtra.transfer (@New.UInt32.isValidChar t_base.1 _) _)

instance : UniqueExtra New.ByteArray where
  subsingleton t_base := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    cases Subsingleton.allEq a b; rfl
  default t_base := t_base.rec fun a => .mk _
    (show new_type% a from UniqueExtra.default (α := New.Array New.UInt8) a)

instance {b_base : ByteArray} (b : new_type% b_base) :
    NonemptyExtra (New.ByteArray.IsValidUTF8 b) where
  nonempty t_base := by
    rcases t_base with ⟨l, hl⟩
    constructor
    refine @New.ByteArray.IsValidUTF8._induct.intro _ _ l ?_ hl ?_
    · with_reducible exact UniqueExtra.default _
    · with_reducible exact NonemptyExtra.transfer _ _

instance : UniqueExtra New.String where
  subsingleton t_base := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    cases Subsingleton.allEq a b; rfl
  default t_base := .ofByteArray _ (UniqueExtra.default (α := New.ByteArray) _)
    (NonemptyExtra.transfer (@New.ByteArray.IsValidUTF8 t_base.1 _) _)

noncomputable def uniqueStrVal (s : String) : new_type% s :=
  UniqueExtra.default (α := new% String) s

convert_to_new SourceInfo
convert_to_new SyntaxNodeKind
convert_to_new Syntax.Preresolved

inductive New.Lean.Syntax._induct : Lean.Syntax → Type where
  | missing : _induct .missing
  | node
    {info_base : _root_.Lean.SourceInfo} (info : new_type% info_base)
    {kind_base : _root_.Lean.SyntaxNodeKind} (kind : new_type% kind_base)
    {args_base : _root_.Array _root_.Lean.Syntax}
    (args : @New.List._induct Lean.Syntax _induct args_base.1) :
    _induct (.node info_base kind_base args_base)
  | atom {info_base : _root_.Lean.SourceInfo} (info : new_type% info_base)
    {val_base : _root_.String} (val : new_type% val_base) : _induct (.atom info_base val_base)
  | ident {info_base : _root_.Lean.SourceInfo} (info : new_type% info_base)
    {rawVal_base : _root_.Substring.Raw} (rawVal : new_type% rawVal_base)
    {val_base : _root_.Lean.Name} (val : new_type% val_base)
    {preresolved_base : _root_.List _root_.Lean.Syntax.Preresolved}
    (preresolved : new_type% preresolved_base) :
    _induct (.ident info_base rawVal_base val_base preresolved_base)

inductive New.Lean.Syntax._encoding : ⦃t_base : Lean.Syntax⦄ → _induct t_base → ℕ → Prop where
  | missing : _encoding .missing 0
  | node
    {info_base : _root_.Lean.SourceInfo} {info : new_type% info_base}
    {info_n : ℕ} (info_enc : New.Lean.SourceInfo.2 info info_n)
    {kind_base : _root_.Lean.SyntaxNodeKind} {kind : new_type% kind_base}
    {kind_n : ℕ} (kind_enc : New.Lean.SyntaxNodeKind.2 kind kind_n)
    {args_base : _root_.Array _root_.Lean.Syntax}
    {args : @New.List._induct Lean.Syntax _induct args_base.1}
    {args_n : ℕ} (args_enc : New.List._encoding _induct _encoding args args_n) :
    _encoding (.node info kind args) (Nat.pair info_n (Nat.pair kind_n args_n) * 3 + 1)
  | atom {info_base : _root_.Lean.SourceInfo} {info : new_type% info_base}
    {info_n : ℕ} (info_enc : New.Lean.SourceInfo.2 info info_n)
    {val_base : _root_.String} {val : new_type% val_base}
    {val_n : ℕ} (val_enc : New.String.2 val val_n) :
    _encoding (.atom info val) (Nat.pair info_n val_n * 3 + 2)
  | ident  {info_base : _root_.Lean.SourceInfo} {info : new_type% info_base}
    {info_n : ℕ} (info_enc : New.Lean.SourceInfo.2 info info_n)
    {rawVal_base : _root_.Substring.Raw} {rawVal : new_type% rawVal_base}
    {rawVal_n : ℕ} (rawVal_enc : New.Substring.Raw.2 rawVal rawVal_n)
    {val_base : _root_.Lean.Name} (val : new_type% val_base)
    {val_n : ℕ} (val_enc : New.Lean.Name.2 val val_n)
    {preresolved_base : _root_.List _root_.Lean.Syntax.Preresolved}
    (preresolved : new_type% preresolved_base)
    {preresolved_n : ℕ}
    (preresolved_enc : (List Syntax.Preresolved).2 preresolved preresolved_n) :
    _encoding (.ident info rawVal val preresolved)
      (Nat.pair info_n (Nat.pair rawVal_n (Nat.pair val_n preresolved_n)) * 3 + 3)

def New.Lean.Syntax : new_type% Lean.Syntax :=
  .mk Syntax._induct Syntax._encoding (IsPropEncodingTrivial.univElim.{1} _)

def New.Lean.Syntax.missing : new_type% Lean.Syntax.missing := @_induct.missing
def New.Lean.Syntax.atom : new_type% Lean.Syntax.atom := @_induct.atom
def New.Lean.Syntax.ident : new_type% Lean.Syntax.ident := @_induct.ident
def New.Lean.Syntax.node : new_type% Lean.Syntax.node :=
  fun _ info _ kind _ args => _induct.node info kind args.1

noncomputable def New.Lean.Syntax.rec : new_type% @Lean.Syntax.rec.{u} :=
  fun motive_1_base motive_1 motive_2_base _ motive_3_base motive_3
      missing_base missing node_base node atom_base atom ident_base ident
      mk_base mk nil_base nil cons_base cons t_base t =>
    @Syntax._induct.rec (fun t_base t => (motive_1 t).1
        (@_root_.Lean.Syntax.rec motive_1_base motive_2_base motive_3_base
          missing_base node_base atom_base ident_base mk_base nil_base cons_base t_base))
      (fun t_base t => (motive_3 t).1
        (@_root_.Lean.Syntax.rec_2 motive_1_base motive_2_base motive_3_base
          missing_base node_base atom_base ident_base mk_base nil_base cons_base t_base))
      missing
      (fun _ _ _ _ _ ih => node _ _ _ (mk _ ih))
      @atom @ident @nil
      (fun _ _ _ head_ih tail_ih => cons _ _ head_ih tail_ih)
      t_base t

convert_to_new Prod

instance {α_base : Type u} (α : new_type% α_base)
    {β_base : Type v} (β : new_type% β_base)
    [SubsingletonExtra α] [SubsingletonExtra β] :
    SubsingletonExtra (New.Prod α β) where
  subsingleton t_base := by
    constructor
    rintro ⟨a, b⟩ ⟨a', b'⟩
    cases Subsingleton.allEq a a'
    cases Subsingleton.allEq b b'
    rfl

convert_to_new Nat.mul_add_lt_mul_of_lt_of_lt
convert_to_new List.attach
convert_to_new Array.attach
convert_to_new List.mapM
convert_to_new List.zip_eq_zip_take_min
convert_to_new not_exists
convert_to_new List.cons.injEq
convert_to_new eq_comm
convert_to_new eq_false
convert_to_new Part

inductive Middle : Prop where
  | intro

instance : Decidable Middle := .isTrue .intro

def New.Middle : new_type% _root_.Middle :=
  .mk (fun _ => _root_.False) (TrivialEncoding _) (.trivialEncoding _)

theorem almostEm (p : Prop) : p ∨ (p ↔ Middle) ∨ ¬p := by
  obtain h | h := Classical.em p
  · exact .inl h
  · exact .inr (.inr h)

theorem New.almostEm : new_type% almostEm := by
  intro p_base p
  by_cases h : p_base
  · by_cases h' : p.1 h
    · exact .inl h'
    · have iff := iff_of_true h Middle.intro
      refine @New.Or._induct.inr _ _ _ _ (.inl iff) ?_
      refine @New.Or._induct.inl _ _ _ _ iff ?_
      constructor
      · intro _ _; contradiction
      · intro _ _; contradiction
  · refine @New.Or._induct.inr _ _ _ _ (.inr h) ?_
    refine @New.Or._induct.inr _ _ _ _ h ?_
    intro h'
    contradiction

theorem not_em : ¬ new_type% Classical.em := by
  intro h
  cases @h Middle New.Middle
  · contradiction
  · contradiction

theorem not_em' : ¬ ∃ h : type_of% Classical.em, new_type% h := by
  intro ⟨_, h⟩
  cases @h Middle New.Middle
  · contradiction
  · contradiction

theorem not_not_em' : ¬ ∃ h : ¬(type_of% Classical.em), new_type% h := by
  intro ⟨h, _⟩
  simp at h

def splitLeft (p : ℕ → Prop) : ℕ → Prop :=
  fun n => ∃ k, n = k * 2 ∧ p k

def splitRight (p : ℕ → Prop) : ℕ → Prop :=
  fun n => ∃ k, n = k * 2 + 1 ∧ p k

def split (p : ℕ → ℕ → Prop) : ℕ → Prop :=
  Nat.unpaired p

inductive New.Prod._encodes {α_base : Type u} {α : new_type% α_base}
    {β_base : Type v} {β : new_type% β_base} :
    {x_base : α_base × β_base} → (x : New.Prod._induct α β x_base) → Nat → Prop where
  | mk {fst_base : α_base} {fst : α.1 fst_base} {fst_num : ℕ} (fst_encodes : α.2 fst fst_num)
       {snd_base : β_base} {snd : β.1 snd_base} {snd_num : ℕ} (snd_encodes : β.2 snd snd_num) :
       _encodes (New.Prod.mk α β fst snd) (Nat.pair fst_num snd_num)

convert_to_new LinearOrder
convert_to_new LinearOrder.toPartialOrder
convert_to_new PFun
convert_to_new Part.instMembership
convert_to_new Nat.lt_trichotomy

lemma Nat.rfindX._proof_1_alt : type_of% @Nat.rfindX._proof_1 := by
  intro p H m al
  rcases H with ⟨n, h₁, h₂⟩
  rcases Nat.lt_trichotomy m n with (h₃ | h₃ | h₃)
  · exact h₂ _ h₃
  · rw [h₃]
    exact h₁.fst
  · injection Part.mem_unique h₁ (al _ h₃)

convert_to_new Nat.rfindX._proof_1_alt

lemma New.Nat.rfindX._proof_1 : new_type% @Nat.rfindX._proof_1 :=
  @New.Nat.rfindX._proof_1_alt

convert_to_new New.Sort
convert_to_new New.Forall
convert_to_new Quot.rec
convert_to_new New.Nat
convert_to_new New.Nat.add
