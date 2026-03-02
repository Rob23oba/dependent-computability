import Mathlib.Computability.PartrecCode

@[pp_with_univ]
def IsProp.{u} := ∀ α : Sort u, ∀ a b : α, a = b

theorem isProp_prop : IsProp.{0} := by
  intro h a b
  rfl

theorem not_isProp : ¬ IsProp.{max u 1} := by
  intro h
  specialize h (PULift.{u} Bool) ⟨false⟩ ⟨true⟩
  simp at h

theorem isProp_of_isProp_imax.{u, v} (h : IsProp.{imax u v}) : IsProp.{v} := by
  intro α a b
  specialize h (PUnit.{u} → α) (fun _ => a) (fun _ => b)
  exact congrArg (· ⟨⟩) h

@[mk_iff]
inductive TrivialEncoding {α : Sort u} (Extra : α → Sort u) :
    ⦃a : α⦄ → (a : Extra a) → (n : ℕ) → Prop where
  | zero {a} {a_extra : Extra a} : TrivialEncoding Extra a_extra 0

attribute [simp] trivialEncoding_iff

def IsPropEncodingTrivial {α : Sort u} {Extra : α → Sort u}
    (Encoding : ∀ ⦃a : α⦄, Extra a → ℕ → Prop) : Prop :=
  IsProp.{u} → ∀ {a} a_extra n, @Encoding a a_extra n ↔ TrivialEncoding Extra a_extra n

theorem IsPropEncodingTrivial.trivialEncoding {α : Sort u} (Extra : α → Sort u) :
    IsPropEncodingTrivial (TrivialEncoding Extra) := by
  intro; simp

theorem IsPropEncodingTrivial.eq_of_isProp {α : Sort u} {Extra : α → Sort u}
    {Encoding : ∀ ⦃a : α⦄, Extra a → ℕ → Prop}
    (h : IsPropEncodingTrivial Encoding) (hprop : IsProp.{u}) :
    Encoding = TrivialEncoding Extra := by
  ext a a n
  apply h hprop

theorem IsPropEncodingTrivial.eq {α : Prop} {Extra : α → Prop}
    {Encoding : ∀ ⦃a : α⦄, Extra a → ℕ → Prop}
    (h : IsPropEncodingTrivial Encoding) :
    Encoding = TrivialEncoding Extra := h.eq_of_isProp isProp_prop

theorem IsPropEncodingTrivial.univElim {α : Sort (max 1 u)} {Extra : α → Sort (max 1 u)}
    (Encoding : ∀ ⦃a : α⦄, Extra a → ℕ → Prop) :
    @IsPropEncodingTrivial α Extra Encoding := by
  intro h
  exact absurd h not_isProp.{u}

inductive SortExtra (α : Sort u) where
  | mk (Extra : α → Sort u) (Encoding : ∀ ⦃a : α⦄, Extra a → ℕ → Prop)
    (propElim : IsPropEncodingTrivial Encoding)

theorem IsProp.encoding_eq {x : SortExtra.{u} α} (hprop : IsProp.{u}) :
    x.2 = TrivialEncoding x.1 := x.3.eq_of_isProp hprop

@[pp_with_univ]
def New.«Sort».{u} : SortExtra (Sort u) :=
  .mk SortExtra (@TrivialEncoding (Sort u) SortExtra)
    (IsPropEncodingTrivial.trivialEncoding SortExtra)

inductive ForallEncoding
    {α : Sort u} (α_extra : New.Sort.{u}.1 α) {β : α → Sort v}
    (β_extra : ∀ ⦃a : α⦄, ∀ _ : α_extra.1 a, New.Sort.{v}.1 (β a))
    ⦃f : (a : α) → β a⦄
    (f_extra : ∀ ⦃a : α⦄ (a_extra : α_extra.1 a), (β_extra a_extra).1 (f a)) :
    ℕ → Prop where
  | zero (hprop : IsProp.{imax u v}) : ForallEncoding α_extra β_extra f_extra 0
  | encode (hprop : ¬IsProp.{imax u v}) (code : Nat.Partrec.Code)
    (hcode : ∀ ⦃a a_extra n⦄, @α_extra.2 a a_extra n →
      ∃ m ∈ code.eval n, (β_extra a_extra).2 (f_extra a_extra) m) :
    ForallEncoding α_extra β_extra f_extra (Encodable.encode code)

theorem IsPropEncodingTrivial.forallEncoding
    {α : Sort u} (α_extra : New.Sort.{u}.1 α) {β : α → Sort v}
    (β_extra : ∀ ⦃a : α⦄, ∀ _ : α_extra.1 a, New.Sort.{v}.1 (β a)) :
    IsPropEncodingTrivial (ForallEncoding α_extra β_extra) := by
  intro hprop a a n
  constructor
  · rintro (⟨⟩ | ⟨h⟩)
    · constructor
    · contradiction
  · rintro ⟨⟩
    constructor
    assumption

def New.«Forall».{u, v}
    {α : Sort u} (α_extra : New.Sort.{u}.1 α) {β : α → Sort v}
    (β_extra : ∀ ⦃a : α⦄, ∀ _ : α_extra.1 a, New.Sort.{v}.1 (β a)) :
    New.Sort.{imax u v}.1 ((a : α) → β a) :=
  .mk (Extra := fun f => ∀ ⦃a : α⦄, ∀ a_extra : α_extra.1 a, (β_extra a_extra).1 (f a))
    (Encoding := ForallEncoding α_extra β_extra) (propElim := .forallEncoding α_extra β_extra)

def mkNewName (nm : Lean.Name) : Lean.Name :=
  match nm with
  | .anonymous => `New
  | .str pre s => .str (mkNewName pre) s
  | .num pre n => .num (mkNewName pre) n

def mkNewInductName (nm : Lean.Name) : Lean.Name :=
  .str (mkNewName nm) "_induct"

open Lean in
@[match_pattern]
abbrev mkExtraApp (ty e : Expr) : Expr :=
  .app (.proj ``SortExtra 0 ty) e

open Lean Qq in
@[inline]
def mkExtraAppQ {α : Q(Sort u)} (α_extra : Q(New.Sort.{u}.1 $α))
    (x : Q($α)) : Q(Sort u) :=
  q($α_extra.1 $x)

open Lean in
initialize declConverterRef : IO.Ref (Name → CoreM Unit) ← IO.mkRef fun _ => pure ()

open Lean Meta in
def projToRec (nm : Name) (idx : Nat) (struct : Expr) : MetaM Expr := do
  let ind ← getConstInfoInduct nm
  let [ctorName] := ind.ctors | throwError "invalid projection"
  let ctor ← getConstVal ctorName
  let casesOn ← getConstInfoDefn (mkCasesOnName nm)
  let type ← inferType struct
  let type ← withTransparency .all (whnf type)
  let propRecursor := casesOn.levelParams.length == ind.levelParams.length
  type.withApp fun fn paramsAndIndices => do
    unless fn.isConstOf nm do
      throwError "invalid projection {Expr.proj nm idx struct}"
    let params := paramsAndIndices.extract 0 ind.numParams
    let indices := paramsAndIndices.extract ind.numParams
    let ctorType ← instantiateForall ctor.type params
    let indType ← instantiateForall ind.type params
    forallTelescope indType fun indexVars _ => do
    withLocalDeclD `x (mkAppN (mkAppN fn params) indexVars) fun structVar => do
      let indexVars := indexVars.push structVar
      let rec mkCtorNth (type : Expr) (i n : Nat) : Expr :=
        match type with
        | .forallE nm t b bi => .lam nm t (mkCtorNth b i (n + 1)) bi
        | _ => .bvar (n - i - 1)
      let rec mkCasesOnApp (motive : Expr) (i : Nat) (indicesAndStruct : Array Expr) :
          MetaM Expr := do
        let level ← getLevel motive
        if propRecursor && !level.isAlwaysZero then
          throwError "Invalid projection {Expr.proj nm idx struct}, \
            {.ofConstName casesOn.name} only eliminates to {Expr.sort 0}"
        let levels ← if propRecursor then pure fn.constLevels!
          else pure (level :: fn.constLevels!)
        let args := params.push (← mkLambdaFVars indexVars motive) ++ indicesAndStruct
          |>.push (mkCtorNth ctorType i 0)
        return (casesOn.value.instantiateLevelParams casesOn.levelParams levels).beta args
      let rec traverseCtor (type : Expr) (i : Nat) : MetaM Expr := do
        let .forallE nm t b bi := type |
          throwError "invalid projection {Expr.proj nm idx struct}"
        if i < idx then
          if b.hasLooseBVars then
            traverseCtor (b.instantiate1 (← mkCasesOnApp t i indexVars)) (i + 1)
          else
            traverseCtor (b.lowerLooseBVars 0 1) (i + 1)
        else
          mkCasesOnApp t i (indices.push struct)
      termination_by idx - i
      traverseCtor ctorType 0

open Lean in
def isStructureLikeWithLargeElim (nm : Name) : CoreM Bool := do
  let { ctors := [_], numIndices := 0, isRec := false, levelParams, .. } ← getConstInfoInduct nm |
    return false
  let recVal ← getConstInfoRec (mkRecName nm)
  return levelParams.length < recVal.levelParams.length

open Lean Meta in
partial def conversionStepNew (e : Expr) : MetaM Expr := do
  let rec visit (e : Expr) (extraMap : FVarIdMap Expr) : MonadCacheT ExprStructEq Expr MetaM Expr :=
    withTraceNode `debug (fun err => return m!"{exceptEmoji err} Transforming {e}") do
    checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
      match e with
      | .lit (.natVal _) => return .app (.const `uniqueNatVal []) e
      | .lit (.strVal _) => return .app (.const `uniqueStrVal []) e
      | .fvar f =>
        let some val := extraMap.get? f |
          throwError "invalid variable: {e} in\n{(← mkFreshExprMVar none).mvarId!}"
        return val
      | .mvar _ => throwError "unexpected metavariable"
      | .bvar _ => throwError "unexpected bound variable"
      | .mdata m e => return .mdata m (← visit e extraMap)
      | .proj t i e =>
        if ← isStructureLikeWithLargeElim t then
          return .proj (mkNewInductName t) i (← visit e extraMap)
        else
          conversionStepNew (← projToRec t i e)
      | .app f a => return mkApp2 (← visit f extraMap) a (← visit a extraMap)
      | .letE nm t v b nd =>
        withLetDecl nm t v (nondep := false) fun baseVar => do
          let newT ← visit t extraMap
          let newT' := mkExtraApp newT (.bvar 0)
          let newV ← visit v extraMap
          let extraName := nm.appendAfter "_extra"
          withLetDecl extraName newT' newV (nondep := nd) fun var => do
            let newB ← visit (b.instantiate1 baseVar) (extraMap.insert baseVar.fvarId! var)
            let newB := newB.abstract #[baseVar, var]
            return .letE nm t v (.letE extraName newT' newV newB nd) false
      | .sort u => return .const ``New.Sort [u]
      | .const nm us => return .const (mkNewName nm) us
      | .forallE nm t b bi =>
        let u ← getLevel t
        let v ← withLocalDecl nm bi t fun a => getLevel (b.instantiate1 a)
        withLocalDecl nm bi t fun var => do
          let newT ← visit t extraMap
          let newT' := mkExtraApp newT (.bvar 0)
          let extraName := nm.appendAfter "_extra"
          withLocalDecl extraName bi newT fun extraVar => do
            let newB ← visit (b.instantiate1 var) (extraMap.insert var.fvarId! extraVar)
            let newB := newB.abstract #[var, extraVar]
            return mkApp4 (.const ``New.Forall [u, v]) t newT
              (.lam nm t b bi) (.lam nm t (.lam extraName newT' newB bi)
                (if bi.isImplicit then .implicit else .strictImplicit))
      | .lam nm t b bi =>
        withLocalDecl nm bi t fun var => do
          let newT ← visit t extraMap
          let newT' := mkExtraApp newT (.bvar 0)
          let extraName := nm.appendAfter "_extra"
          withLocalDecl extraName bi newT fun extraVar => do
            let newB ← visit (b.instantiate1 var) (extraMap.insert var.fvarId! extraVar)
            let newB := newB.abstract #[var, extraVar]
            return .lam nm t (.lam extraName newT' newB bi)
              (if bi.isImplicit then .implicit else .strictImplicit)
  (visit e {}).run

open Lean Meta in
def populateBaseMap : MetaM (FVarIdMap Expr) := do
  let lctx ← getLCtx
  let mut extraMap : FVarIdMap Expr := {}
  for decl in lctx do
    let type := decl.type
    let type ← instantiateMVars type
    let mkExtraApp _ty (.fvar baseVar) := type | continue
    extraMap := extraMap.insert baseVar decl.toExpr
  return extraMap

open Lean Elab Term in
elab tk:"new% " t:term : term => do
  let expectedType? : Option Expr := ‹_›
  let mut eTy : Option Expr := none
  if let some expTy := expectedType? then
    let expTy ← instantiateMVars expTy
    if let mkExtraApp ty val := expTy then
      eTy ← Meta.inferType val
  let expr ← elabTerm t eTy
  synthesizeSyntheticMVarsNoPostponing
  let expr ← instantiateMVars expr
  let extraMap ← populateBaseMap
  if expr.hasAnyFVar (not ∘ extraMap.contains) then
    let some a := expr.find? (fun | .fvar f => !extraMap.contains f | _ => false) |
      throwErrorAt tk "expression has free variables"
    throwErrorAt tk "Invalid unresolved free variable {a} in{indentExpr expr}"
  if expr.hasMVar then
    throwErrorAt tk "expression has metavariables:{indentExpr expr}"
  for const in expr.getUsedConstantsAsSet do
    unless (← getEnv).contains (mkNewName const) do
      let converter ← declConverterRef.get
      converter const
  let res ← (conversionStepNew.visit expr extraMap).run
  if let some expTy := expectedType? then
    let expTy ← instantiateMVars expTy
    let mkExtraApp ty val := expTy | return res
    let type ← Meta.inferType expr
    let typeRes ← (conversionStepNew.visit type extraMap).run
    discard <| Meta.isDefEq ty typeRes
    discard <| Meta.isDefEq val expr
  return res

open Lean Elab Term in
elab tk:"new_type% " t:term : term => do
  let expr ← elabTerm t none
  let type ← Meta.inferType expr
  let type ← instantiateMVars type
  let extraMap ← populateBaseMap
  if type.hasAnyFVar (not ∘ extraMap.contains) then
    let some a := type.find? (fun | .fvar f => !extraMap.contains f | _ => false) |
      throwErrorAt tk "expression has free variables"
    throwErrorAt tk "Invalid unresolved free variable {a} in{indentExpr type}"
  if type.hasMVar then
    throwErrorAt tk "expression has metavariables:{indentExpr expr}"
  for const in type.getUsedConstantsAsSet do
    unless (← getEnv).contains (mkNewName const) do
      let converter ← declConverterRef.get
      converter const
  let newExpr ← (conversionStepNew.visit type extraMap).run
  return mkExtraApp newExpr expr

class InhabitedExtra {α : Sort u} (α_extra : new_type% α) where
  default : ∀ a, α_extra.1 a

class SubsingletonExtra {α : Sort u} (α_extra : new_type% α) where
  subsingleton : ∀ a, Subsingleton (α_extra.1 a)

instance {α α_extra} [@InhabitedExtra α α_extra] (a : α) : Nonempty (new_type% a) :=
  ⟨InhabitedExtra.default a⟩

attribute [instance] SubsingletonExtra.subsingleton

instance : InhabitedExtra New.Sort.{u} where
  default _ := ⟨fun _ => PUnit.{u}, TrivialEncoding _, .trivialEncoding _⟩

instance {α : Sort u} (α_extra : new_type% α) {β : α → Sort v}
    (β_extra : ⦃a : α⦄ → α_extra.1 a → New.Sort.1 (β a))
    [∀ a a_extra, InhabitedExtra (@β_extra a a_extra)] :
    InhabitedExtra (New.Forall α_extra β_extra) where
  default f a _ := InhabitedExtra.default (f a)

instance {α : Sort u} (α_extra : new_type% α) {β : α → Sort v}
    (β_extra : ⦃a : α⦄ → α_extra.1 a → New.Sort.1 (β a))
    [∀ a a_extra, SubsingletonExtra (@β_extra a a_extra)] :
    SubsingletonExtra (New.Forall α_extra β_extra) where
  subsingleton f := by
    constructor
    intro a a_extra
    funext x x_extra
    apply Subsingleton.allEq

instance (priority := low) {p : Prop} {p_extra : new_type% p} : SubsingletonExtra p_extra where
  subsingleton := inferInstance

def IsRepresentable {α : Sort u} {α_extra : new_type% α}
    {x : α} (x_extra : new_type% x) : Prop :=
  ∃ n, α_extra.2 x_extra n

inductive DComputable {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {f : (a : α) → β a} (f_extra : new_type% f) : Prop where
  | intro (g : ℕ →. ℕ) (hg : Nat.Partrec g)
    (hg' : ∀ ⦃a a_extra n⦄, @α_extra.2 a a_extra n →
      ∃ m ∈ g n, (β_extra a_extra).2 (f_extra a_extra) m)

inductive DPrimrec {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {f : (a : α) → β a} (f_extra : new_type% f) : Prop where
  | intro (g : ℕ → ℕ) (hg : Nat.Primrec g)
    (hg' : ∀ ⦃a a_extra n⦄, @α_extra.2 a a_extra n → (β_extra a_extra).2 (f_extra a_extra) (g n))

class FullyRepresentable {α : Sort u} (α_extra : new_type% α)
    extends InhabitedExtra α_extra, SubsingletonExtra α_extra where
  isRepresentable : ∀ {x : α} (x : α_extra.1 x), IsRepresentable x

class CompatibleEncodingRelation {α : Type u} (α_extra : new_type% α)
    [Encodable α] extends FullyRepresentable α_extra where
  encode : ℕ → ℕ := id
  decode : ℕ → ℕ := id
  decode_encode (n : ℕ) : decode (encode n) = n := by intro; rfl
  encode_primrec : Nat.Primrec encode := by exact .id
  decode_primrec : Nat.Primrec decode := by exact .id
  encode_eq {x : α} {x_extra : α_extra.1 x} {n : ℕ}
      (hx : α_extra.2 x_extra n) : encode n = Encodable.encode x

attribute [simp] CompatibleEncodingRelation.decode_encode

theorem encoding_pi_def {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    (h : ¬ IsProp.{imax u v})
    {f : (a : α) → β a} (f_extra : new_type% f) (n : ℕ) :
    (new% ∀ a, β a).2 f_extra n ↔ ∀ ⦃a a_extra n₁⦄, @α_extra.2 a a_extra n₁ →
      ∃ n₂ ∈ (Denumerable.ofNat Nat.Partrec.Code n).eval n₁,
        (β_extra a_extra).2 (f_extra a_extra) n₂ := by
  constructor
  · rintro (⟨⟩ | ⟨_, code, hcode⟩)
    · contradiction
    · simpa
  · intro h
    rw [← Denumerable.encode_ofNat (α := Nat.Partrec.Code) n]
    exact .encode ‹_› _ h

theorem isRepresentable_function_iff {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {f : (a : α) → β a} (f_extra : new_type% f) :
    IsRepresentable (new% f) ↔ DComputable f_extra := by
  by_cases hprop : IsProp.{imax u v}
  · simp only [IsRepresentable, hprop.encoding_eq, trivialEncoding_iff,
      exists_eq, true_iff]
    refine ⟨_, Nat.Partrec.zero, ?_⟩
    simp [pure, PFun.pure, (isProp_of_isProp_imax.{u, v} hprop).encoding_eq]
  simp only [IsRepresentable, encoding_pi_def.{u, v} hprop]
  constructor
  · rintro ⟨n, hn⟩
    let c := Denumerable.ofNat Nat.Partrec.Code n
    exact ⟨c.eval, Partrec.nat_iff.mp (Nat.Partrec.Code.eval_part.comp (.const c) .id), hn⟩
  · rintro ⟨g, hg, hg'⟩
    obtain ⟨c, rfl⟩ := Nat.Partrec.Code.exists_code.mp hg
    use Encodable.encode c
    simpa using hg'

class Irrelevant {α : Sort u} (α_extra : new_type% α) where
  encoding ⦃a : α⦄ (a : α_extra.1 a) : α_extra.2 a 0

instance instIrrelevantSort : Irrelevant New.Sort.{u} where
  encoding _ _ := .zero

instance (priority := low) {p : Prop} (p : New.Sort.{0}.1 p) : Irrelevant p where
  encoding _ _ := (p.3 isProp_prop _ _).mpr .zero

open Nat.Partrec Code in
instance instIrrelevantForall {α : Sort u} (α_extra : new_type% α) {β : α → Sort v}
    (β_extra : ⦃a : α⦄ → α_extra.1 a → New.Sort.1 (β a))
    [∀ ⦃a : α⦄ (a : α_extra.1 a), Irrelevant (β_extra a)] :
    Irrelevant (New.Forall α_extra β_extra) where
  encoding f f := by
    by_cases hprop : IsProp.{imax u v}
    · exact .zero hprop
    rw [encoding_pi_def hprop]
    intros
    simp [ofNatCode_eq, ofNatCode, eval, pure, PFun.pure, Irrelevant.encoding]

structure Encoding {α : Sort u} (α_extra : new_type% α) where
  repr : ℕ

open CompatibleEncodingRelation in
instance {α : Type u} {α_extra : new_type% α} [Encodable α]
    [CompatibleEncodingRelation α_extra] : Primcodable (Encoding α_extra) where
  encode x := encode α_extra x.repr
  decode n := some ⟨decode α_extra n⟩
  encodek := by simp
  prim := .comp .succ (.comp encode_primrec decode_primrec)

theorem Encoding.encode_eq {α : Type u} {α_extra : new_type% α}
    [Encodable α] [CompatibleEncodingRelation α_extra]
    {x : α} {x_extra : new_type% x} {n : ℕ} (h : α_extra.2 x_extra n) :
    Encodable.encode (⟨n⟩ : Encoding α_extra) = Encodable.encode x :=
  CompatibleEncodingRelation.encode_eq h

theorem CompatibleEncodingRelation.encoding_unique
    {α : Type u} {α_extra : new_type% α}
    [Encodable α] [CompatibleEncodingRelation α_extra]
    {x : α} {x_extra : new_type% x}
    {y : α} {y_extra : new_type% y}
    {n : ℕ} (hx : α_extra.2 x_extra n) (hy : α_extra.2 y_extra n) : x = y := by
  apply Encodable.encode_injective
  rw [← Encoding.encode_eq hx, ← Encoding.encode_eq hy]

theorem Option.rec_eq_elim {α : Type u} {β : Type v} (x : Option α) (n : β) (s : α → β) :
    Option.rec n s x = Option.elim x n s := by
  cases x <;> rfl

theorem Encoding.primrec_mk {α : Type u} {α_extra : new_type% α}
    [Encodable α] [CompatibleEncodingRelation α_extra] :
    Primrec (Encoding.mk : ℕ → Encoding α_extra) :=
  Nat.Primrec.comp .succ CompatibleEncodingRelation.encode_primrec

theorem Encoding.primrec_repr {α : Type u} {α_extra : new_type% α}
    [Encodable α] [CompatibleEncodingRelation α_extra] :
    Primrec (Encoding.repr : Encoding α_extra → ℕ) :=
  Nat.Primrec.comp .succ CompatibleEncodingRelation.decode_primrec

def Encoding.of {α : Type u} {α_extra : new_type% α}
    [Encodable α] [CompatibleEncodingRelation α_extra]
    (x : α) : Encoding α_extra := ⟨CompatibleEncodingRelation.decode α_extra (Encodable.encode x)⟩

theorem Encoding.encode_of {α : Type u} {α_extra : new_type% α}
    [Encodable α] [CompatibleEncodingRelation α_extra]
    (x : α) : Encodable.encode (Encoding.of (α_extra := α_extra) x) = Encodable.encode x := by
  obtain ⟨n, hn⟩ := FullyRepresentable.isRepresentable (InhabitedExtra.default x : α_extra.1 x)
  simp [of, ← Encoding.encode_eq hn, Encodable.encode]

theorem Encoding.encoding_of {α : Type u} {α_extra : new_type% α}
    [Encodable α] [CompatibleEncodingRelation α_extra]
    {x : α} (x_extra : new_type% x) :
    α_extra.2 x_extra (Encoding.of (α_extra := α_extra) x).repr := by
  obtain ⟨n, hn⟩ := FullyRepresentable.isRepresentable x_extra
  simp [of, ← Encoding.encode_eq hn, Encodable.encode, hn]

open CompatibleEncodingRelation in
theorem Encoding.primrec_of {α : Type u} {α_extra : new_type% α}
    [Primcodable α] [CompatibleEncodingRelation α_extra] :
    Primrec (Encoding.of : α → Encoding α_extra) := by
  unfold of
  exact .comp primrec_mk (.comp (Primrec.nat_iff.mpr decode_primrec) .encode)

theorem dprimrec_iff_primrec {α : Type u} {α_extra : new_type% α}
    {β : Type v} {β_extra : new_type% β} [Primcodable α] [Primcodable β]
    [CompatibleEncodingRelation α_extra] [CompatibleEncodingRelation β_extra]
    {f : α → β} (f_extra : new_type% f) :
    DPrimrec f_extra ↔ Primrec f := by
  constructor
  · rintro ⟨g, hgprim, hg'⟩
    rw [Primrec]
    rw [← Primrec.nat_iff] at hgprim ⊢
    let g' (a : Encoding α_extra) : Encoding β_extra := ⟨g a.repr⟩
    have commute (a : α) : g' (Encoding.of a) = Encoding.of (f a) := by
      have := hg' (Encoding.encoding_of (InhabitedExtra.default a : α_extra.1 a))
      simp [Encoding.of, g', ← Encoding.encode_eq this, Encodable.encode]
    have hg'prim : Primrec g' := .comp Encoding.primrec_mk (.comp hgprim Encoding.primrec_repr)
    let fn (n : ℕ) : ℕ :=
      (Encodable.decode n : Option α).casesOn 0
        (fun a => Encodable.encode (g' (Encoding.of a)) + 1)
    have : Primrec fn :=
      .option_casesOn .decode (.const 0)
        (Primrec.succ.comp (.comp .encode (.comp hg'prim (.comp Encoding.primrec_of .snd))))
    refine this.of_eq ?_
    intro n
    simp only [fn]
    rcases h : (Encodable.decode n : Option α) with _ | a
    · simp
    · have := Encoding.encode_of (α_extra := β_extra) (f a)
      simp [← this, commute]
  · intro hf
    let fn (n : ℕ) : ℕ :=
      (Encodable.decode (Encodable.encode (⟨n⟩ : Encoding α_extra)) : Option α).casesOn
        0 (fun a => (Encoding.of (α_extra := β_extra) (f a)).repr)
    refine ⟨fn, ?_, ?_⟩
    · rw [← Primrec.nat_iff]
      exact .option_casesOn (.comp .decode (.comp .encode Encoding.primrec_mk)) (.const 0) <|
        Encoding.primrec_repr.comp (Encoding.primrec_of.comp (hf.comp .snd))
    · intro a a n han
      simp [fn, Encoding.encode_eq han, Encoding.encoding_of]

theorem dcomputable_iff_computable {α : Type u} {α_extra : new_type% α}
    {β : Type v} {β_extra : new_type% β} [Primcodable α] [Primcodable β]
    [CompatibleEncodingRelation α_extra] [CompatibleEncodingRelation β_extra]
    {f : α → β} (f_extra : new_type% f) :
    DComputable f_extra ↔ Computable f := by
  constructor
  · rintro ⟨g, hgprim, hg'⟩
    rw [Computable, Partrec]
    rw [← Partrec.nat_iff] at hgprim ⊢
    let g' (a : Encoding α_extra) : Part (Encoding β_extra) := (g a.repr).map Encoding.mk
    have commute (a : α) : g' (Encoding.of a) = Part.some (Encoding.of (f a)) := by
      obtain ⟨y, hy, this⟩ := hg' (Encoding.encoding_of (InhabitedExtra.default a : α_extra.1 a))
      simp only [Encoding.of] at hy
      simp [Encoding.of, g', ← Encoding.encode_eq this, Part.eq_some_iff.mpr hy, Encodable.encode]
    have hg'part : Partrec g' :=
      .map (.comp hgprim Encoding.primrec_repr.to_comp) ((Encoding.primrec_mk.comp .snd).to_comp)
    let fn (n : ℕ) : Part ℕ :=
      (Part.ofOption (Encodable.decode n)).bind
        (fun a => (g' (Encoding.of a)).map Encodable.encode)
    have : Partrec fn :=
      .bind Computable.decode.ofOption
        (Partrec.map (.comp hg'part (.comp Encoding.primrec_of.to_comp .snd))
          (Primrec.encode.comp .snd).to_comp)
    refine this.of_eq ?_
    intro n
    simp only [fn]
    rcases h : (Encodable.decode n : Option α) with _ | a
    · simp
    · have := Encoding.encode_of (α_extra := β_extra) (f a)
      simp [← this, commute]
  · intro hf
    let fn (n : ℕ) : ℕ :=
      (Encodable.decode (Encodable.encode (⟨n⟩ : Encoding α_extra)) : Option α).casesOn
        0 (fun a => (Encoding.of (α_extra := β_extra) (f a)).repr)
    refine ⟨fn, ?_, ?_⟩
    · rw [← Partrec.nat_iff]
      change Computable fn
      unfold fn
      exact .option_casesOn (.comp .decode (.comp .encode Encoding.primrec_mk.to_comp))
        (.const 0) (Encoding.primrec_repr.to_comp.comp (Encoding.primrec_of.to_comp.comp
          (hf.comp .snd)))
    · intro a a n han
      simp [fn, Encoding.encode_eq han, Encoding.encoding_of]

protected theorem DPrimrec.id {α : Sort u} {α_extra : new_type% α} :
    DPrimrec (fun ⦃a : α⦄ (a : α_extra.1 a) => a) := by
  use id, .id
  simp

protected theorem DPrimrec.const' {α : Sort u} {α_extra : new_type% α}
    {β : Sort v} {β_extra : new_type% β}
    {x : β} {x_extra : new_type% x}
    (h : IsRepresentable x_extra) :
    DPrimrec (fun ⦃a : α⦄ (_ : α_extra.1 a) => x_extra) := by
  obtain ⟨n, hn⟩ := h
  use fun _ => n, .const n
  intro a a b hab
  assumption

protected theorem DPrimrec.const {α : Sort u} {α_extra : new_type% α}
    {β : Sort v} {β_extra : new_type% β}
    [FullyRepresentable β_extra] {x : β} (x : β_extra.1 x) :
    DPrimrec (fun ⦃a : α⦄ (_ : α_extra.1 a) => x) :=
  .const' (FullyRepresentable.isRepresentable x)

protected theorem DPrimrec.comp.{u}
    {β : Sort v} {β_extra : new_type% β}
    {γ : β → Sort w} {γ_extra : new_type% γ}
    {f : (x : β) → γ x} {f_extra : new_type% f}
    (hf : DPrimrec f_extra)
    {α : Sort u} {α_extra : new_type% α}
    {g : α → β} {g_extra : new_type% g}
    (hg : DPrimrec g_extra) :
    DPrimrec (new% (fun a => f (g a))) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  refine ⟨_, hgf.comp hgg, ?_⟩
  intro a a b hab
  exact hgf' (hgg' hab)

protected theorem DPrimrec.of_isProp {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {f : (a : α) → β a} {f_extra : new_type% f}
    (hprop : IsProp.{v}) :
    DPrimrec f_extra := by
  use fun _ => 0, .zero
  intro a a n h
  exact ((β_extra a).3 hprop (f_extra a) 0).mpr .zero

protected theorem DPrimrec.proof {α : Sort u} {α_extra : new_type% α}
    {β : α → Prop} {β_extra : new_type% β}
    {f : (a : α) → β a} {f_extra : new_type% f} :
    DPrimrec f_extra := .of_isProp isProp_prop

protected theorem DPrimrec.irrelevant
    {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    [∀ ⦃a⦄ (a : α_extra.1 a), Irrelevant (β_extra a)]
    {f : (a : α) → β a} {f_extra : new_type% f} :
    DPrimrec (new% f) := by
  use fun _ => 0, .zero
  simp [Irrelevant.encoding]

protected theorem DPrimrec.sort {α : Sort u} {α_extra : new_type% α}
    {f : α → Sort v} {f_extra : new_type% f} :
    DPrimrec (new% f) := .irrelevant

protected theorem DPrimrec.dcomputable
    {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {f : (a : α) → β a} {f_extra : new_type% f}
    (hf : DPrimrec f_extra) : DComputable f_extra := by
  obtain ⟨g, hg, hg'⟩ := hf
  use g, .of_primrec hg
  intro a a n h
  use g n
  simpa using hg' h

alias DComputable.of_prim := DPrimrec.dcomputable

protected theorem DComputable.id {α : Sort u} {α_extra : new_type% α} :
    DComputable (fun ⦃a : α⦄ (a : α_extra.1 a) => a) := .of_prim .id

protected theorem DComputable.const' {α : Sort u} {α_extra : new_type% α}
    {β : Sort v} {β_extra : new_type% β}
    {x : β} {x_extra : new_type% x}
    (h : IsRepresentable x_extra) :
    DComputable (fun ⦃a : α⦄ (_ : α_extra.1 a) => x_extra) := .of_prim (.const' h)

protected theorem DComputable.const {α : Sort u} {α_extra : new_type% α}
    {β : Sort v} {β_extra : new_type% β}
    [FullyRepresentable β_extra] {x : β} {x_extra : new_type% x} :
    DComputable (fun ⦃a : α⦄ (_ : α_extra.1 a) => x_extra) := .of_prim (.const x_extra)

protected theorem DComputable.comp.{u}
    {β : Sort v} {β_extra : new_type% β}
    {γ : β → Sort w} {γ_extra : new_type% γ}
    {f : (x : β) → γ x} {f_extra : new_type% f}
    (hf : DComputable f_extra)
    {α : Sort u} {α_extra : new_type% α}
    {g : α → β} {g_extra : new_type% g}
    (hg : DComputable g_extra) :
    DComputable (new% (fun a => f (g a))) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  refine ⟨_, hgf.comp hgg, ?_⟩
  intro a a n han
  obtain ⟨x, hx, hx'⟩ := hgg' han
  obtain ⟨y, hy, hy'⟩ := hgf' hx'
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  exact ⟨y, ⟨x, hx, hy⟩, hy'⟩

protected theorem DPrimrec.compComputable.{u}
    {β : Sort v} {β_extra : new_type% β}
    {γ : β → Sort w} {γ_extra : new_type% γ}
    {f : (x : β) → γ x} {f_extra : new_type% f}
    (hf : DPrimrec f_extra)
    {α : Sort u} {α_extra : new_type% α}
    {g : α → β} {g_extra : new_type% g}
    (hg : DComputable g_extra) :
    DComputable (new% (fun a => f (g a))) :=
  .comp (.of_prim hf) hg

protected theorem DComputable.of_isProp {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {f : (a : α) → β a} {f_extra : new_type% f}
    (hprop : IsProp.{v}) :
    DComputable f_extra := .of_prim (.of_isProp hprop)

protected theorem DComputable.proof {α : Sort u} {α_extra : new_type% α}
    {β : α → Prop} {β_extra : new_type% β}
    {f : (a : α) → β a} {f_extra : new_type% f} :
    DComputable f_extra := .of_prim .proof

protected theorem DComputable.irrelevant
    {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    [∀ ⦃a⦄ (a : α_extra.1 a), Irrelevant (β_extra a)]
    {f : (a : α) → β a} {f_extra : new_type% f} :
    DComputable (new% f) := .of_prim .irrelevant

protected theorem DComputable.sort {α : Sort u} {α_extra : new_type% α}
    {f : α → Sort v} {f_extra : new_type% f} :
    DComputable (new% f) := .of_prim .sort

inductive New.PSigma._induct {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} (β_extra : new_type% β)
    (p : PSigma β) : Sort (max 1 u v) where
  | mk (fst : α_extra.1 p.1) (snd : (β_extra fst).1 p.2)

inductive New.PSigma._encoding {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} (β_extra : new_type% β)
    ⦃p : PSigma β⦄ (p : New.PSigma._induct β_extra p) :
    (n : ℕ) → Prop where
  | mk {fst_n : ℕ} (fst : α_extra.2 p.1 fst_n) {snd_n : ℕ} (snd : (β_extra _).2 p.2 snd_n) :
    _encoding β_extra p (Nat.pair fst_n snd_n)

def New.PSigma.{u, v} : new_type% @PSigma.{u, v} := fun _ _ _ β =>
  .mk (New.PSigma._induct β) (New.PSigma._encoding β) not_isProp.{max u v}.elim

def New.PSigma.mk.{u, v} : new_type% @PSigma.mk.{u, v} :=
  fun _ _ _ _ _ fst _ snd => .mk fst snd

def New.PSigma.fst.{u, v} : new_type% @PSigma.fst.{u, v} :=
  fun _ _ _ _ _ x => x.1

def New.PSigma.snd.{u, v} : new_type% @PSigma.snd.{u, v} :=
  fun _ _ _ _ _ x => x.2

def New.PSigma.rec.{u_1, u, v} : new_type% @PSigma.rec.{u_1, u, v} :=
  fun _ _ _ _ _ _ _ mk _ t => mk t.1 t.2

theorem New.PSigma.mk.primrec.{c, u, v}
    {ctx : Sort c} {ctx_extra : new_type% ctx}
    {α : ctx → Sort u} {α_extra : new_type% α}
    {β : (c : ctx) → α c → Sort v} {β_extra : new_type% β}
    {fst : (c : ctx) → α c} {fst_extra : new_type% fst}
    (fst_prim : DPrimrec fst_extra)
    {snd : (c : ctx) → β c (fst c)} {snd_extra : new_type% snd}
    (snd_prim : DPrimrec snd_extra) :
    DPrimrec (new% fun c =>
      @_root_.PSigma.mk (α c) (β c) (fst c) (snd c)) := by
  obtain ⟨f, hf, hf'⟩ := fst_prim
  obtain ⟨g, hg, hg'⟩ := snd_prim
  refine ⟨_, .pair hf hg, ?_⟩
  intros
  constructor
  · apply hf'
    assumption
  · apply hg'
    assumption

theorem New.PSigma.fst.primrec.{c, u, v}
    {ctx : Sort c} {ctx_extra : new_type% ctx}
    {α : ctx → Sort u} {α_extra : new_type% α}
    {β : (c : ctx) → α c → Sort v} {β_extra : new_type% β}
    {self : (c : ctx) → (a : α c) ×' β c a}
    {self_extra : new_type% self}
    (self_prim : DPrimrec (new% self)) :
    DPrimrec (new% fun c =>
      @_root_.PSigma.fst (α c) (β c) (self c)) := by
  obtain ⟨f, hf, hf'⟩ := self_prim
  refine ⟨_, .comp .left hf, ?_⟩
  intro a a n han
  refine (hf' han).casesOn ?_
  intros
  simpa

theorem New.PSigma.snd.primrec.{c, u, v}
    {ctx : Sort c} {ctx_extra : new_type% ctx}
    {α : ctx → Sort u} {α_extra : new_type% α}
    {β : (c : ctx) → α c → Sort v} {β_extra : new_type% β}
    {self : (c : ctx) → (a : α c) ×' β c a}
    {self_extra : new_type% self}
    (self_prim : DPrimrec (new% self)) :
    DPrimrec (new% fun c =>
      @_root_.PSigma.snd (α c) (β c) (self c)) := by
  obtain ⟨f, hf, hf'⟩ := self_prim
  refine ⟨_, .comp .right hf, ?_⟩
  intro a a n han
  refine (hf' han).casesOn ?_
  intros
  simpa

theorem New.PSigma.mk.computable.{c, u, v}
    {ctx : Sort c} {ctx_extra : new_type% ctx}
    {α : ctx → Sort u} {α_extra : new_type% α}
    {β : (c : ctx) → α c → Sort v} {β_extra : new_type% β}
    {fst : (c : ctx) → α c} {fst_extra : new_type% fst}
    (fst_prim : DComputable fst_extra)
    {snd : (c : ctx) → β c (fst c)} {snd_extra : new_type% snd}
    (snd_prim : DComputable snd_extra) :
    DComputable (new% fun c =>
      @_root_.PSigma.mk (α c) (β c) (fst c) (snd c)) := by
  obtain ⟨f, hf, hf'⟩ := fst_prim
  obtain ⟨g, hg, hg'⟩ := snd_prim
  refine ⟨_, .pair hf hg, ?_⟩
  intro a a n han
  obtain ⟨n₁, hn₁, hn₁'⟩ := hf' han
  obtain ⟨n₂, hn₂, hn₂'⟩ := hg' han
  use Nat.pair n₁ n₂
  simp only [Seq.seq, Part.map_eq_map, Part.bind_map, Part.mem_bind_iff, Part.mem_map_iff,
    Nat.pair_eq_pair, exists_eq_right_right, hn₂, true_and, exists_eq_right, hn₁]
  constructor <;> simpa

theorem New.PSigma.fst.computable.{c, u, v}
    {ctx : Sort c} {ctx_extra : new_type% ctx}
    {α : ctx → Sort u} {α_extra : new_type% α}
    {β : (c : ctx) → α c → Sort v} {β_extra : new_type% β}
    {self : (c : ctx) → (a : α c) ×' β c a}
    {self_extra : new_type% self}
    (self_prim : DComputable (new% self)) :
    DComputable (new% fun c =>
      @_root_.PSigma.fst (α c) (β c) (self c)) := by
  obtain ⟨f, hf, hf'⟩ := self_prim
  refine ⟨_, .comp .left hf, ?_⟩
  intro a a n han
  simp only [Part.bind_eq_bind, Part.mem_bind_iff, PFun.coe_val, Part.mem_some_iff, ↓existsAndEq,
    and_true]
  obtain @⟨_, hy, x, hy₁, x', hy₂⟩ := hf' han
  exact ⟨_, hy, by simpa using hy₁⟩

theorem New.PSigma.snd.computable.{c, u, v}
    {ctx : Sort c} {ctx_extra : new_type% ctx}
    {α : ctx → Sort u} {α_extra : new_type% α}
    {β : (c : ctx) → α c → Sort v} {β_extra : new_type% β}
    {self : (c : ctx) → (a : α c) ×' β c a}
    {self_extra : new_type% self}
    (self_prim : DComputable (new% self)) :
    DComputable (new% fun c =>
      @_root_.PSigma.snd (α c) (β c) (self c)) := by
  obtain ⟨f, hf, hf'⟩ := self_prim
  refine ⟨_, .comp .right hf, ?_⟩
  intro a a n han
  simp only [Part.bind_eq_bind, Part.mem_bind_iff, PFun.coe_val, Part.mem_some_iff, ↓existsAndEq,
    and_true]
  obtain @⟨_, hy, x, hy₁, x', hy₂⟩ := hf' han
  exact ⟨_, hy, by simpa using hy₂⟩

open Nat.Partrec (Code) in
theorem DPrimrec.curry
    {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {γ : (a : α) → β a → Sort w} {γ_extra : new_type% γ}
    {f : (a : α) → (b : β a) → γ a b} {f_extra : new_type% f}
    (hf : DComputable (new% fun x : (a : α) ×' β a => f x.1 x.2)) :
    DPrimrec (new% f) := by
  by_cases hprop : IsProp.{imax v w}
  · exact .of_isProp hprop
  obtain ⟨g, hg, hc⟩ := hf
  obtain ⟨c, rfl⟩ := Nat.Partrec.Code.exists_code.mp hg
  have : Nat.Primrec (fun a => Encodable.encode (c.curry a)) := by
    rw [← Primrec.nat_iff]
    exact .comp .encode (Code.primrec₂_curry.comp (.const c) .id)
  refine ⟨_, this, ?_⟩
  intro a a n hna
  rw [encoding_pi_def hprop]
  intro b b m hmb
  simp only [Denumerable.ofNat_encode, Code.eval_curry]
  exact @hc ⟨_, _⟩ ⟨a, b⟩ (Nat.pair n m) ⟨by simpa, by simpa⟩

theorem DPrimrec.constCurry.{u}
    {β : Sort v} {β_extra : new_type% β}
    {γ : β → Sort w} {γ_extra : new_type% γ}
    {f : (a : β) → γ a} {f_extra : new_type% f}
    (hf : DComputable f_extra)
    {α : Sort u} {α_extra : new_type% α} :
    DPrimrec (new% fun _ : α => f) := by
  refine .const' (x_extra := new% f) ?_
  rwa [isRepresentable_function_iff]

protected theorem DComputable.constCurry.{u}
    {β : Sort v} {β_extra : new_type% β}
    {γ : β → Sort w} {γ_extra : new_type% γ}
    {f : (a : β) → γ a} {f_extra : new_type% f}
    (hf : DComputable f_extra)
    {α : Sort u} {α_extra : new_type% α} :
    DComputable (new% fun _ : α => f) :=
  .of_prim (.constCurry hf)

theorem DPrimrec.curriedApp.{u}
    {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {γ : (a : α) → β a → Sort w} {γ_extra : new_type% γ}
    {f : (a : α) → (b : β a) → γ a b} {f_extra : new_type% f}
    (hf : DPrimrec (new% fun x : (a : α) ×' β a => f x.1 x.2))
    {g : (a : α) → β a} {g_extra : new_type% g}
    (hg : DPrimrec g_extra) :
    DPrimrec (new% fun x => f x (g x)) :=
  .comp hf (New.PSigma.mk.primrec .id hg)

example
    {β : Sort v} {β_extra : new_type% β}
    {γ : β → Sort w} {γ_extra : new_type% γ}
    {δ : (a : β) → γ a → Sort w'} {δ_extra : new_type% δ}
    {f : (a : β) → (b : γ a) → δ a b} {f_extra : new_type% f}
    (hf : DPrimrec (new% fun x : (a : β) ×' γ a => f x.1 x.2))
    {α : Sort u} {α_extra : new_type% α}
    {g₁ : α → β} {g₁_extra : new_type% g₁}
    (hg₁ : DPrimrec g₁_extra)
    {g₂ : (a : α) → γ (g₁ a)} {g₂_extra : new_type% g₂}
    (hg₂ : DPrimrec g₂_extra) :
    DPrimrec (new% fun x => f (g₁ x) (g₂ x)) :=
  .comp hf (New.PSigma.mk.primrec hg₁ hg₂)

protected theorem DComputable.curry
    {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {γ : (a : α) → β a → Sort w} {γ_extra : new_type% γ}
    {f : (a : α) → (b : β a) → γ a b} {f_extra : new_type% f}
    (hf : DComputable (new% (fun x : (a : α) ×' β a => f x.1 x.2))) :
    DComputable (new% f) :=
  .of_prim (.curry hf)

protected theorem DComputable.app
    {ctx : Sort u} {ctx_extra : new_type% ctx}
    {α : ctx → Sort v} {α_extra : new_type% α}
    {β : (c : ctx) → α c → Sort w} {β_extra : new_type% β}
    {f : (c : ctx) → (a : α c) → β c a} {f_extra : new_type% f}
    {g : (c : ctx) → α c} {g_extra : new_type% g}
    (hf : DComputable (new% f)) (hg : DComputable (new% g)) :
    DComputable (new% fun c => f c (g c)) := by
  by_cases hprop : IsProp.{imax v w}
  · exact .of_isProp @(isProp_of_isProp_imax.{v, w} hprop)
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  let fn (n : ℕ) : Part ℕ :=
    (gf n).bind fun a => (gg n).bind fun b => (Denumerable.ofNat Nat.Partrec.Code a).eval b
  refine ⟨fn, ?_, ?_⟩
  · rw [← Partrec.nat_iff] at hgf hgg ⊢
    refine .bind hgf (.bind (.comp hgg .fst) (Nat.Partrec.Code.eval_part.comp ?_ .snd))
    exact .comp (.ofNat _) (.comp .snd .fst)
  · intro a a n han
    obtain ⟨x, hx, hc⟩ := hgf' han
    rw [encoding_pi_def hprop] at hc
    obtain ⟨y, hy, hy'⟩ := hgg' han
    simp only [Part.mem_bind_iff, fn]
    obtain ⟨z, hz, hz'⟩ := hc hy'
    exact ⟨z, ⟨_, hx, y, hy, by simpa using hz⟩, hz'⟩

theorem dcomputable_curry
    {α : Sort u} {α_extra : new_type% α}
    {β : α → Sort v} {β_extra : new_type% β}
    {γ : (a : α) → β a → Sort w} {γ_extra : new_type% γ}
    {f : (a : α) → (b : β a) → γ a b} {f_extra : new_type% f} :
    DComputable (new% f) ↔
      DComputable (new% fun x : (a : α) ×' β a => f x.1 x.2) := by
  constructor
  · intro f_comp
    refine .app ?_ ?_
    · refine .app (f_extra := new% fun _ : (a : α) ×' β a => f) ?_ ?_
      · exact .constCurry f_comp
      · refine .of_prim ?_
        apply New.PSigma.fst.primrec
        exact .id
    · refine .of_prim ?_
      apply New.PSigma.snd.primrec
      exact .id
  · exact .curry
