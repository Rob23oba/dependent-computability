import DependentComputability.SortExtra

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

partial def toNewInductiveType (info : InductiveVal) : MetaM InductiveType := do
  if info.isNested then
    throwError "nested not supported"
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
  if (← getEnv).contains (`New ++ nm) then
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
        name := `New ++ nm
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
        name := `New ++ nm
        levelParams := val.levelParams
        type := newType'
        value := newValue
      }
  | .inductInfo val => (convertInductToNew val).run'
  | .ctorInfo val => recConvertToNew val.induct
  | _ => throwError "unhandled const info {.ofConstName nm}"

end

elab "convert_to_new " id:ident : command => do
  Lean.Elab.Command.liftCoreM do
    let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    recConvertToNew name

convert_to_new List
convert_to_new Option
convert_to_new PProd

noncomputable opaque uniqueChoice (h : Nonempty α) : Squash α :=
  .mk (Classical.choice h)

namespace New

protected def Nat : convert_to_new_type% Nat :=
  .mk (fun _ => Unit) (fun {n} _ m => n = m) (IsPropEncodingTrivial.univElim.{0} _)

protected def Nat.zero : convert_to_new_type% @Nat.zero := ()
protected def Nat.succ : convert_to_new_type% @Nat.succ := fun _ _ => ()

protected def Nat.rec.{u} : convert_to_new_type% @Nat.rec.{u} :=
  fun {_} _ {_} zero {_} succ {t_base} _ => t_base.rec zero fun _ ih => succ () ih

protected def PUnit.{u} : convert_to_new_type% @PUnit.{u} :=
  .mk (fun _ => PUnit.{u}) (TrivialEncoding _) (.trivialEncoding _)

protected def PUnit.unit.{u} : convert_to_new_type% @PUnit.unit.{u} :=
  @_root_.PUnit.unit.{u}

convert_to_new Iff
convert_to_new Eq

protected theorem propext : convert_to_new_type% @propext := by
  intro p_base p q_base q h_base h
  dsimp only
  cases propext h_base
  rcases p with ⟨pty, penc, pelim⟩
  rcases q with ⟨qty, qenc, qelim⟩
  cases pelim.eq
  cases qelim.eq
  rcases h with ⟨hmp, hmpr⟩
  by_cases hbase : p_base
  · cases eq_true hbase
    have : pty = qty := by
      ext h
      exact ⟨@hmp trivial, @hmpr trivial⟩
    subst this
    constructor
  · cases eq_false hbase
    have : pty = qty := by
      ext h
      exact h.elim
    subst this
    constructor

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
set_option genInjectivity false in
inductive Quot._base {α_base : Sort u} {α : convert_to_new_type% α_base}
    {r_base : α_base → α_base → Prop} (r : convert_to_new_type% r_base) :
    Quot r_base → Sort u where
  | mk {a_base : α_base} (a : α.1 a_base) : _base r (Quot.mk r_base a_base)

inductive Quot._rel {α_base : Sort u} {α : convert_to_new_type% α_base}
    {r_base : α_base → α_base → Prop} (r : convert_to_new_type% r_base) :
    (q : Quot r_base) → Quot._base r q → Quot._base r q → Prop where
  | mk {a_base : α_base} (a : α.1 a_base) {b_base : α_base} (b : α.1 b_base)
    {h_base : r_base a_base b_base} (h : (r a b).1 h_base) :
    _rel r (Quot.mk r_base b_base) (Quot.sound h_base ▸ .mk a) (.mk b)

inductive Quot._encoding {α_base : Sort u} {α : convert_to_new_type% α_base}
    {r_base : α_base → α_base → Prop} (r : convert_to_new_type% r_base) :
    ⦃q_base : Quot r_base⦄ → (q : Quot (_rel r q_base)) → (n : ℕ) → Prop where
  | mk {a_base : α_base} {a : α.1 a_base} {n : ℕ} (h : α.2 a n) :
    @_encoding α_base α r_base r (Quot.mk r_base a_base) (Quot.mk _ (.mk a)) n

protected def Quot.{u} : convert_to_new_type% @Quot.{u} := fun α_base α r_base r =>
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

protected def Quot.mk.{u} : convert_to_new_type% @Quot.mk.{u} := fun _ _ _ _ _ a =>
  _root_.Quot.mk _ (.mk a)

protected theorem Quot.ind.{u} : convert_to_new_type% @Quot.ind.{u} := by
  intro α_base α r_base r motive_base motive mk_base mk t_base t
  rcases t with ⟨@⟨t_base, t⟩⟩
  apply mk

protected def Quot.lift.{u, v} : convert_to_new_type% @Quot.lift.{u, v} :=
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

protected theorem Quot.sound.{u} : convert_to_new_type% @Quot.sound.{u} := by
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
    {h_base : _root_.Subsingleton α_base} (h : convert_to_new_type% h_base) :
    SubsingletonExtra α := by
  constructor
  intro x
  constructor
  intro a b
  cases h.1 a b
  rfl

instance {α_base : Sort u} (α : New.Sort.1 α_base) : SubsingletonExtra (Squash α) :=
  subsingletonExtra_of_subsingleton _ (instSubsingletonSquash α)

protected noncomputable def uniqueChoice.{u} : convert_to_new_type% @uniqueChoice.{u} :=
  fun α_base α h_base h =>
    haveI : _root_.Nonempty ((a : α_base) ×' α.1 a) := by
      obtain @⟨a_base, a⟩ := h
      exact ⟨a_base, a⟩
    (uniqueChoice this).liftOn (fun x =>
        haveI : uniqueChoice h_base = _root_.Squash.mk x.1 := Subsingleton.allEq ..
        this ▸ Squash.mk _ x.2) (by intros; apply Subsingleton.allEq)

end New

instance {α_base : Sort u} (α : convert_to_new_type% α_base) [SubsingletonExtra α]
    {a_base : α_base} (a : α.1 a_base)
    {b_base : α_base} (b : α.1 b_base) :
    NonemptyExtra (New.Eq α a b) where
  nonempty := by
    rintro rfl
    cases (SubsingletonExtra.subsingleton a_base).allEq a b
    constructor
    constructor

instance {α_base : Sort u} (α : New.Sort.1 α_base) {β_base : α_base → Sort v}
    (β : ⦃a_base : α_base⦄ → α.1 a_base → New.Sort.1 (β_base a_base))
    [∀ a_base a, NonemptyExtra (@β a_base a)] :
    NonemptyExtra (New.Forall α β) where
  nonempty f := by
    constructor
    intro a_base a
    exact Classical.choice (NonemptyExtra.nonempty (f a_base))

instance {α_base : Sort u} (α : New.Sort.1 α_base) {β_base : α_base → Sort v}
    (β : ⦃a_base : α_base⦄ → α.1 a_base → New.Sort.1 (β_base a_base))
    [∀ a_base a, SubsingletonExtra (@β a_base a)] :
    SubsingletonExtra (New.Forall α β) where
  subsingleton f := by
    constructor
    intro a_base a
    funext x_base x
    apply Subsingleton.allEq

instance {α_base : Type u} (α : New.Sort.1 α_base) {β_base : α_base → Type v}
    (β : ⦃a_base : α_base⦄ → α.1 a_base → New.Sort.1 (β_base a_base))
    [∀ a_base a, UniqueExtra (@β a_base a)] :
    UniqueExtra (New.Forall α β) where
  default f_base := fun {a_base} _ => UniqueExtra.default (f_base a_base)

instance : UniqueExtra New.Nat where
  default _ := ()
  subsingleton _ := inferInstanceAs (Subsingleton Unit)

convert_to_new Nat.add
convert_to_new Nat.sub
convert_to_new Nat.mul
convert_to_new HEq
convert_to_new eq_of_heq
convert_to_new And

def New.And.rec.{u} : convert_to_new_type% @And.rec.{u} := by
  intro p_base p q_base q motive_base motive intro_base intro t_base t
  exact t_base.rec fun _ _ => intro t.1 t.2

convert_to_new Nat.mod
convert_to_new Nat.div
convert_to_new Nat.mul_add_lt_mul_of_lt_of_lt
convert_to_new List.attach
convert_to_new List.mapM
convert_to_new List.zip_eq_zip_take_min
convert_to_new not_exists
convert_to_new List.cons.injEq
convert_to_new And
convert_to_new congrArg
convert_to_new congrFun
convert_to_new congr
convert_to_new Eq.trans
convert_to_new Eq.symm
convert_to_new eq_comm
convert_to_new eq_true
convert_to_new eq_false
convert_to_new Or
convert_to_new Part

def New.Middle : convert_to_new_type% _root_.True :=
  .mk (fun _ => _root_.False) (TrivialEncoding _) (.trivialEncoding _)

theorem not_em : ¬ convert_to_new_type% Classical.em := by
  intro h
  cases @h True New.Middle
  · contradiction
  · contradiction

theorem not_em' : ¬ ∃ h : type_of% Classical.em, convert_to_new_type% h := by
  intro ⟨_, h⟩
  cases @h True New.Middle
  · contradiction
  · contradiction

theorem not_not_em' : ¬ ∃ h : ¬(type_of% Classical.em), convert_to_new_type% h := by
  intro ⟨h, _⟩
  simp at h

def splitLeft (p : ℕ → Prop) : ℕ → Prop :=
  fun n => ∃ k, n = k * 2 ∧ p k

def splitRight (p : ℕ → Prop) : ℕ → Prop :=
  fun n => ∃ k, n = k * 2 + 1 ∧ p k

def split (p : ℕ → ℕ → Prop) : ℕ → Prop :=
  Nat.unpaired p

inductive New.Prod._encodes {α_base : Type u} {α : convert_to_new_type% α_base}
    {β_base : Type v} {β : convert_to_new_type% β_base} :
    {x_base : α_base × β_base} → (x : New.Prod._induct α β x_base) → Nat → Prop where
  | mk {fst_base : α_base} {fst : α.1 fst_base} {fst_num : ℕ} (fst_encodes : α.2 fst fst_num)
       {snd_base : β_base} {snd : β.1 snd_base} {snd_num : ℕ} (snd_encodes : β.2 snd snd_num) :
       _encodes (New.Prod.mk α β fst snd) (Nat.pair fst_num snd_num)
