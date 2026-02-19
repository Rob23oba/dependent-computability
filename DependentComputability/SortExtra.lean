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
    ⦃a_base : α⦄ → (a : Extra a_base) → (n : ℕ) → Prop where
  | zero {a_base} {a : Extra a_base} : TrivialEncoding Extra a 0

attribute [simp] trivialEncoding_iff

def IsPropEncodingTrivial {α : Sort u} {Extra : α → Sort u}
    (Encoding : ∀ ⦃a_base : α⦄, Extra a_base → ℕ → Prop) : Prop :=
  IsProp.{u} → ∀ {a_base} a n, @Encoding a_base a n ↔ TrivialEncoding Extra a n

theorem IsPropEncodingTrivial.trivialEncoding {α : Sort u} (Extra : α → Sort u) :
    IsPropEncodingTrivial (TrivialEncoding Extra) := by
  intro; simp

theorem IsPropEncodingTrivial.eq_of_isProp {α : Sort u} {Extra : α → Sort u}
    {Encoding : ∀ ⦃a_base : α⦄, Extra a_base → ℕ → Prop}
    (h : IsPropEncodingTrivial Encoding) (hprop : IsProp.{u}) :
    Encoding = TrivialEncoding Extra := by
  ext a_base a n
  apply h hprop

theorem IsPropEncodingTrivial.eq {α : Prop} {Extra : α → Prop}
    {Encoding : ∀ ⦃a_base : α⦄, Extra a_base → ℕ → Prop}
    (h : IsPropEncodingTrivial Encoding) :
    Encoding = TrivialEncoding Extra := h.eq_of_isProp isProp_prop

theorem IsPropEncodingTrivial.univElim {α : Sort (max 1 u)} {Extra : α → Sort (max 1 u)}
    (Encoding : ∀ ⦃a_base : α⦄, Extra a_base → ℕ → Prop) :
    @IsPropEncodingTrivial α Extra Encoding := by
  intro h
  exact absurd h not_isProp.{u}

inductive SortExtra (α : Sort u) where
  | mk (Extra : α → Sort u) (Encoding : ∀ ⦃a_base : α⦄ (_ : Extra a_base), ℕ → Prop)
    (propElim : IsPropEncodingTrivial Encoding)

theorem IsProp.encoding_eq {x : SortExtra.{u} α} (hprop : IsProp.{u}) :
    x.2 = TrivialEncoding x.1 := x.3.eq_of_isProp hprop

@[pp_with_univ]
def New.«Sort».{u} : SortExtra (Sort u) :=
  .mk SortExtra (@TrivialEncoding (Sort u) SortExtra)
    (IsPropEncodingTrivial.trivialEncoding SortExtra)

inductive ForallEncoding
    {α_base : Sort u} (α : New.Sort.{u}.1 α_base) {β_base : α_base → Sort v}
    (β : ∀ ⦃a_base : α_base⦄, ∀ _ : α.1 a_base, New.Sort.{v}.1 (β_base a_base))
    ⦃f_base : (a : α_base) → β_base a⦄
    (f : ∀ ⦃a_base : α_base⦄ (a : α.1 a_base), (β a).1 (f_base a_base)) :
    ℕ → Prop where
  | zero (hprop : IsProp.{imax u v}) : ForallEncoding α β f 0
  | encode (hprop : ¬IsProp.{imax u v}) (code : Nat.Partrec.Code)
    (hcode : ∀ ⦃a_base a n⦄, @α.2 a_base a n → ∃ m ∈ code.eval n, (β a).2 (f a) m) :
    ForallEncoding α β f (Encodable.encode code)

theorem IsPropEncodingTrivial.forallEncoding
    {α_base : Sort u} (α : New.Sort.{u}.1 α_base) {β_base : α_base → Sort v}
    (β : ∀ ⦃a_base : α_base⦄, ∀ _ : α.1 a_base, New.Sort.{v}.1 (β_base a_base)) :
    IsPropEncodingTrivial (ForallEncoding α β) := by
  intro hprop a_base a n
  constructor
  · rintro (⟨⟩ | ⟨h⟩)
    · constructor
    · contradiction
  · rintro ⟨⟩
    constructor
    assumption

def New.«Forall».{u, v}
    {α_base : Sort u} (α : New.Sort.{u}.1 α_base) {β_base : α_base → Sort v}
    (β : ∀ ⦃a_base : α_base⦄, ∀ _ : α.1 a_base, New.Sort.{v}.1 (β_base a_base)) :
    New.Sort.{imax u v}.1 ((a : α_base) → β_base a) :=
  .mk (Extra := fun f => ∀ ⦃a_base : α_base⦄, ∀ a : α.1 a_base, (β a).1 (f a_base))
    (Encoding := ForallEncoding α β) (propElim := .forallEncoding α β)

def mkNewName (nm : Lean.Name) : Lean.Name :=
  match nm with
  | .anonymous => `New
  | .str pre s => .str (mkNewName pre) s
  | .num pre n => .num (mkNewName pre) n

def mkNewInductName (nm : Lean.Name) : Lean.Name :=
  .str (mkNewName nm) "_induct"

open Lean Meta in
partial def conversionStepNew (e : Expr) : MetaM Expr := do
  let rec visit (e : Expr) (baseMap : FVarIdMap Expr) : MonadCacheT ExprStructEq Expr MetaM Expr :=
    withTraceNode `debug (fun err => return m!"{exceptEmoji err} Transforming {e}") do
    checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
      match e with
      | .lit (.natVal _) => return .app (.const `uniqueNatVal []) e
      | .lit (.strVal _) => return .app (.const `uniqueStrVal []) e
      | .fvar f => return baseMap.get! f
      | .mvar _ => panic! "unexpected metavariable"
      | .bvar _ => panic! "unexpected bound variable"
      | .mdata m e => return .mdata m (← visit e baseMap)
      | .proj t i e => return .proj (mkNewInductName t) i (← visit e baseMap)
      | .app f a => return mkApp2 (← visit f baseMap) a (← visit a baseMap)
      | .letE nm t v b nd =>
        let baseName := nm.appendAfter "_base"
        withLetDecl baseName t v (nondep := false) fun baseVar => do
          let newT ← visit t baseMap
          let newT' := .app (.proj ``SortExtra 0 newT) (.bvar 0)
          let newV ← visit v baseMap
          withLetDecl nm newT' newV (nondep := nd) fun var => do
            let newB ← visit (b.instantiate1 baseVar) (baseMap.insert baseVar.fvarId! var)
            let newB := newB.abstract #[baseVar, var]
            return .letE baseName t v (.letE nm newT' newV newB nd) false
      | .sort u => return .const ``New.Sort [u]
      | .const nm us => return .const (mkNewName nm) us
      | .forallE nm t b bi =>
        let u ← getLevel t
        let v ← withLocalDecl nm bi t fun a => getLevel (b.instantiate1 a)
        let baseName := nm.appendAfter "_base"
        withLocalDecl baseName bi t fun baseVar => do
          let newT ← visit t baseMap
          let newT' := .app (.proj ``SortExtra 0 newT) (.bvar 0)
          withLocalDecl nm bi newT fun var => do
            let newB ← visit (b.instantiate1 baseVar) (baseMap.insert baseVar.fvarId! var)
            let newB := newB.abstract #[baseVar, var]
            return mkApp4 (.const ``New.Forall [u, v]) t newT
              (.lam nm t b bi) (.lam baseName t (.lam nm newT' newB bi)
                (if bi.isImplicit then .implicit else .strictImplicit))
      | .lam nm t b bi =>
        let baseName := nm.appendAfter "_base"
        withLocalDecl baseName bi t fun baseVar => do
          let newT ← visit t baseMap
          let newT' := .app (.proj ``SortExtra 0 newT) (.bvar 0)
          withLocalDecl nm bi newT fun var => do
            let newB ← visit (b.instantiate1 baseVar) (baseMap.insert baseVar.fvarId! var)
            let newB := newB.abstract #[baseVar, var]
            return .lam baseName t (.lam nm newT' newB bi)
              (if bi.isImplicit then .implicit else .strictImplicit)
  (visit e {}).run

open Lean Meta in
def populateBaseMap : MetaM (FVarIdMap Expr) := do
  let lctx ← getLCtx
  let mut baseMap : FVarIdMap Expr := {}
  for decl in lctx do
    let type := decl.type
    let .app (.proj ``SortExtra 0 _ty) (.fvar baseVar) := type | continue
    baseMap := baseMap.insert baseVar decl.toExpr
  return baseMap

open Lean Elab Term in
elab tk:"convert_to_new% " t:term : term => do
  let expectedType? : Option Expr := ‹_›
  let expr ← elabTerm t none
  let expr ← instantiateMVars expr
  let baseMap ← populateBaseMap
  if expr.hasAnyFVar (not ∘ baseMap.contains) then
    throwErrorAt tk "expression has free variables"
  if expr.hasMVar then
    throwErrorAt tk "expression has metavariables"
  let res ← (conversionStepNew.visit expr baseMap).run
  if let some expTy := expectedType? then
    let expTy ← instantiateMVars expTy
    let .app (.proj ``SortExtra 0 ty) val := expTy | return res
    let type ← Meta.inferType expr
    let typeRes ← (conversionStepNew.visit type baseMap).run
    discard <| Meta.isDefEq ty typeRes
    discard <| Meta.isDefEq val expr
  return res

open Lean Elab Term in
elab tk:"convert_to_new_type% " t:term : term => do
  let expr ← elabTerm t none
  let type ← Meta.inferType expr
  let type ← instantiateMVars type
  let baseMap ← populateBaseMap
  if type.hasAnyFVar (not ∘ baseMap.contains) then
    throwErrorAt tk "expression has free variables"
  if type.hasMVar then
    throwErrorAt tk "expression has metavariables"
  let newExpr ← (conversionStepNew.visit type baseMap).run
  return .app (.proj ``SortExtra 0 newExpr) expr

class NonemptyExtra {α_base : Sort u} (α : convert_to_new_type% α_base) where
  nonempty : ∀ a, Nonempty (α.1 a)

class SubsingletonExtra {α_base : Sort u} (α : convert_to_new_type% α_base) where
  subsingleton : ∀ a, Subsingleton (α.1 a)

class UniqueExtra {α_base : Sort u} (α : convert_to_new_type% α_base)
    extends SubsingletonExtra α where
  default : ∀ a, α.1 a

attribute [instance] NonemptyExtra.nonempty SubsingletonExtra.subsingleton

instance [UniqueExtra α] : NonemptyExtra α where
  nonempty x := ⟨UniqueExtra.default x⟩

theorem NonemptyExtra.transfer {p_base : Prop} (p : convert_to_new_type% p_base)
    [NonemptyExtra p] (h : p_base) : p.1 h := by
  obtain ⟨h'⟩ := NonemptyExtra.nonempty (α := p) h
  exact h'

/-
inductive New.Option._induct {α_base : Type u} (α : convert_to_new_type% α_base) :
    Option α_base → Type u where
  | none : @_induct α_base α (@Option.none α_base)
  | some {x_base : α_base} (x : α.1 x_base) : @_induct α_base α (@Option.some α_base x_base)


inductive New.Prod._induct {α_base : Type u} (α : convert_to_new_type% α_base)
    {β_base : Type v} (β : convert_to_new_type% β_base)
    (p : Prod α_base β_base) : Type (max u v) where
  | mk (fst : α.1 p.1) (snd : β.1 p.2) : @_induct α_base α β_base β p

inductive New.List._induct {α_base : Type u} (α : convert_to_new_type% α_base) :
    List α_base → Type u where
  | nil : @_induct α_base α (@List.nil α_base)
  | cons {head_base : α_base} (head : α.1 head_base)
    {tail_base : List α_base} (tail : @_induct α_base α tail_base) :
    @_induct α_base α (@List.cons α_base head_base tail_base)
-/

open Lean Meta

def IsRepresentable {α_base : Sort u} {α : convert_to_new_type% α_base}
    {x_base : α_base} (x : convert_to_new_type% x_base) : Prop :=
  ∃ n, α.2 x n

def DComputable {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {f_base : (a : α_base) → β_base a} (f : convert_to_new_type% f_base) : Prop :=
  ∃ g, Nat.Partrec g ∧ ∀ ⦃a_base a n⦄, @α.2 a_base a n → ∃ m ∈ g n, (β a).2 (f a) m

def DPrimrec {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {f_base : (a : α_base) → β_base a} (f : convert_to_new_type% f_base) : Prop :=
  ∃ g, Nat.Primrec g ∧ ∀ ⦃a_base a n⦄, @α.2 a_base a n → (β a).2 (f a) (g n)

class FullyRepresentable {α_base : Sort u} (α : convert_to_new_type% α_base)
    extends UniqueExtra α where
  isRepresentable : ∀ {x_base : α_base} (x : α.1 x_base), IsRepresentable x

class CompatibleEncodingRelation {α_base : Type u} (α : convert_to_new_type% α_base)
    [Encodable α_base] extends FullyRepresentable α where
  encode : ℕ → ℕ := id
  decode : ℕ → ℕ := id
  decode_encode (n : ℕ) : decode (encode n) = n := by intro; rfl
  encode_primrec : Nat.Primrec encode := by exact .id
  decode_primrec : Nat.Primrec decode := by exact .id
  encode_eq {x_base : α_base} {x : α.1 x_base} {n : ℕ}
      (hx : α.2 x n) : encode n = Encodable.encode x_base

attribute [simp] CompatibleEncodingRelation.decode_encode

theorem encoding_pi_def {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    (h : ¬ IsProp.{imax u v})
    {f_base : (a : α_base) → β_base a} (f : convert_to_new_type% f_base) (n : ℕ) :
    (convert_to_new% ∀ a, β_base a).2 f n ↔ ∀ ⦃a_base a n₁⦄, @α.2 a_base a n₁ →
      ∃ n₂ ∈ (Denumerable.ofNat Nat.Partrec.Code n).eval n₁, (β a).2 (f a) n₂ := by
  constructor
  · rintro (⟨⟩ | ⟨_, code, hcode⟩)
    · contradiction
    · simpa
  · intro h
    rw [← Denumerable.encode_ofNat (α := Nat.Partrec.Code) n]
    exact .encode ‹_› _ h

theorem isRepresentable_function_iff {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {f_base : (a : α_base) → β_base a} (f : convert_to_new_type% f_base) :
    IsRepresentable (convert_to_new% f_base) ↔ DComputable f := by
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

structure Encoding {α_base : Sort u} (α : convert_to_new_type% α_base) where
  repr : ℕ

open CompatibleEncodingRelation in
instance {α_base : Type u} {α : convert_to_new_type% α_base} [Encodable α_base]
    [CompatibleEncodingRelation α] : Primcodable (Encoding α) where
  encode x := encode α x.repr
  decode n := some ⟨decode α n⟩
  encodek := by simp
  prim := .comp .succ (.comp encode_primrec decode_primrec)

theorem Encoding.encode_eq {α_base : Type u} {α : convert_to_new_type% α_base}
    [Encodable α_base] [CompatibleEncodingRelation α]
    {x_base : α_base} {x : convert_to_new_type% x_base} {n : ℕ} (h : α.2 x n) :
    Encodable.encode (⟨n⟩ : Encoding α) = Encodable.encode x_base :=
  CompatibleEncodingRelation.encode_eq h

theorem CompatibleEncodingRelation.encoding_unique
    {α_base : Type u} {α : convert_to_new_type% α_base}
    [Encodable α_base] [CompatibleEncodingRelation α]
    {x_base : α_base} {x : convert_to_new_type% x_base}
    {y_base : α_base} {y : convert_to_new_type% y_base}
    {n : ℕ} (hx : α.2 x n) (hy : α.2 y n) : x_base = y_base := by
  apply Encodable.encode_injective
  rw [← Encoding.encode_eq hx, ← Encoding.encode_eq hy]

theorem Option.rec_eq_elim {α : Type u} {β : Type v} (x : Option α) (n : β) (s : α → β) :
    Option.rec n s x = Option.elim x n s := by
  cases x <;> rfl

theorem Encoding.primrec_mk {α_base : Type u} {α : convert_to_new_type% α_base}
    [Encodable α_base] [CompatibleEncodingRelation α] :
    Primrec (Encoding.mk : ℕ → Encoding α) :=
  Nat.Primrec.comp .succ CompatibleEncodingRelation.encode_primrec

theorem Encoding.primrec_repr {α_base : Type u} {α : convert_to_new_type% α_base}
    [Encodable α_base] [CompatibleEncodingRelation α] :
    Primrec (Encoding.repr : Encoding α → ℕ) :=
  Nat.Primrec.comp .succ CompatibleEncodingRelation.decode_primrec

def Encoding.of {α_base : Type u} {α : convert_to_new_type% α_base}
    [Encodable α_base] [CompatibleEncodingRelation α]
    (x : α_base) : Encoding α := ⟨CompatibleEncodingRelation.decode α (Encodable.encode x)⟩

theorem Encoding.encode_of {α_base : Type u} {α : convert_to_new_type% α_base}
    [Encodable α_base] [CompatibleEncodingRelation α]
    (x : α_base) : Encodable.encode (Encoding.of (α := α) x) = Encodable.encode x := by
  obtain ⟨n, hn⟩ := FullyRepresentable.isRepresentable (UniqueExtra.default x : α.1 x)
  simp [of, ← Encoding.encode_eq hn, Encodable.encode]

theorem Encoding.encoding_of {α_base : Type u} {α : convert_to_new_type% α_base}
    [Encodable α_base] [CompatibleEncodingRelation α]
    {x_base : α_base} (x : convert_to_new_type% x_base) :
    α.2 x (Encoding.of (α := α) x_base).repr := by
  obtain ⟨n, hn⟩ := FullyRepresentable.isRepresentable x
  simp [of, ← Encoding.encode_eq hn, Encodable.encode, hn]

open CompatibleEncodingRelation in
theorem Encoding.primrec_of {α_base : Type u} {α : convert_to_new_type% α_base}
    [Primcodable α_base] [CompatibleEncodingRelation α] :
    Primrec (Encoding.of : α_base → Encoding α) := by
  unfold of
  exact .comp primrec_mk (.comp (Primrec.nat_iff.mpr decode_primrec) .encode)

theorem dprimrec_iff_primrec {α_base : Type u} {α : convert_to_new_type% α_base}
    {β_base : Type v} {β : convert_to_new_type% β_base} [Primcodable α_base] [Primcodable β_base]
    [CompatibleEncodingRelation α] [CompatibleEncodingRelation β]
    {f_base : α_base → β_base} (f : convert_to_new_type% f_base) :
    DPrimrec f ↔ Primrec f_base := by
  rw [DPrimrec]
  constructor
  · rintro ⟨g, hgprim, hg'⟩
    rw [Primrec]
    rw [← Primrec.nat_iff] at hgprim ⊢
    let g' (a : Encoding α) : Encoding β := ⟨g a.repr⟩
    have commute (a : α_base) : g' (Encoding.of a) = Encoding.of (f_base a) := by
      have := hg' (Encoding.encoding_of (UniqueExtra.default a : α.1 a))
      simp [Encoding.of, g', ← Encoding.encode_eq this, Encodable.encode]
    have hg'prim : Primrec g' := .comp Encoding.primrec_mk (.comp hgprim Encoding.primrec_repr)
    let fn (n : ℕ) : ℕ :=
      (Encodable.decode n : Option α_base).casesOn 0
        (fun a => Encodable.encode (g' (Encoding.of a)) + 1)
    have : Primrec fn :=
      .option_casesOn .decode (.const 0)
        (Primrec.succ.comp (.comp .encode (.comp hg'prim (.comp Encoding.primrec_of .snd))))
    refine this.of_eq ?_
    intro n
    simp only [fn]
    rcases h : (Encodable.decode n : Option α_base) with _ | a
    · simp
    · have := Encoding.encode_of (α := β) (f_base a)
      simp [← this, commute]
  · intro hf
    let fn (n : ℕ) : ℕ :=
      (Encodable.decode (Encodable.encode (⟨n⟩ : Encoding α)) : Option α_base).casesOn
        0 (fun a => (Encoding.of (α := β) (f_base a)).repr)
    refine ⟨fn, ?_, ?_⟩
    · rw [← Primrec.nat_iff]
      exact .option_casesOn (.comp .decode (.comp .encode Encoding.primrec_mk)) (.const 0) <|
        Encoding.primrec_repr.comp (Encoding.primrec_of.comp (hf.comp .snd))
    · intro a_base a n han
      simp [fn, Encoding.encode_eq han, Encoding.encoding_of]

theorem dcomputable_iff_computable {α_base : Type u} {α : convert_to_new_type% α_base}
    {β_base : Type v} {β : convert_to_new_type% β_base} [Primcodable α_base] [Primcodable β_base]
    [CompatibleEncodingRelation α] [CompatibleEncodingRelation β]
    {f_base : α_base → β_base} (f : convert_to_new_type% f_base) :
    DComputable f ↔ Computable f_base := by
  constructor
  · rintro ⟨g, hgprim, hg'⟩
    rw [Computable, Partrec]
    rw [← Partrec.nat_iff] at hgprim ⊢
    let g' (a : Encoding α) : Part (Encoding β) := (g a.repr).map Encoding.mk
    have commute (a : α_base) : g' (Encoding.of a) = Part.some (Encoding.of (f_base a)) := by
      obtain ⟨y, hy, this⟩ := hg' (Encoding.encoding_of (UniqueExtra.default a : α.1 a))
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
    rcases h : (Encodable.decode n : Option α_base) with _ | a
    · simp
    · have := Encoding.encode_of (α := β) (f_base a)
      simp [← this, commute]
  · intro hf
    let fn (n : ℕ) : ℕ :=
      (Encodable.decode (Encodable.encode (⟨n⟩ : Encoding α)) : Option α_base).casesOn
        0 (fun a => (Encoding.of (α := β) (f_base a)).repr)
    refine ⟨fn, ?_, ?_⟩
    · rw [← Partrec.nat_iff]
      change Computable fn
      unfold fn
      exact .option_casesOn (.comp .decode (.comp .encode Encoding.primrec_mk.to_comp))
        (.const 0) (Encoding.primrec_repr.to_comp.comp (Encoding.primrec_of.to_comp.comp
          (hf.comp .snd)))
    · intro a_base a n han
      simp [fn, Encoding.encode_eq han, Encoding.encoding_of]

protected theorem DPrimrec.id {α_base : Sort u} {α : convert_to_new_type% α_base} :
    DPrimrec (fun ⦃a_base : α_base⦄ (a : α.1 a_base) => a) := by
  use id, .id
  simp

protected theorem DPrimrec.const' {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : Sort v} {β : convert_to_new_type% β_base}
    {x_base : β_base} {x : convert_to_new_type% x_base}
    (h : IsRepresentable x) :
    DPrimrec (fun ⦃a_base : α_base⦄ (_ : α.1 a_base) => x) := by
  obtain ⟨n, hn⟩ := h
  use fun _ => n, .const n
  intro a_base a b hab
  assumption

protected theorem DPrimrec.const {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : Sort v} {β : convert_to_new_type% β_base}
    [FullyRepresentable β] {x_base : β_base} (x : β.1 x_base) :
    DPrimrec (fun ⦃a_base : α_base⦄ (_ : α.1 a_base) => x) :=
  .const' (FullyRepresentable.isRepresentable x)

protected theorem DPrimrec.comp {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : Sort v} {β : convert_to_new_type% β_base}
    {γ_base : β_base → Sort w} {γ : convert_to_new_type% γ_base}
    {f_base : (x : β_base) → γ_base x} {f : convert_to_new_type% f_base}
    {g_base : α_base → β_base} {g : convert_to_new_type% g_base}
    (hf : DPrimrec f) (hg : DPrimrec g) :
    DPrimrec (convert_to_new% (fun a => f_base (g_base a))) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  refine ⟨_, hgf.comp hgg, ?_⟩
  intro a_base a b hab
  exact hgf' (hgg' hab)

protected theorem DPrimrec.of_isProp {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {f_base : (a : α_base) → β_base a} {f : convert_to_new_type% f_base}
    (hprop : IsProp.{v}) :
    DPrimrec f := by
  use fun _ => 0, .zero
  intro a_base a n h
  exact ((β a).3 hprop (f a) 0).mpr .zero

protected theorem DPrimrec.proof {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Prop} {β : convert_to_new_type% β_base}
    {f_base : (a : α_base) → β_base a} {f : convert_to_new_type% f_base} :
    DPrimrec f := .of_isProp isProp_prop

protected theorem DPrimrec.asort {α_base : Sort u} {α : convert_to_new_type% α_base}
    {f_base : (a : α_base) → Sort v} {f : convert_to_new_type% f_base} :
    DPrimrec (convert_to_new% f_base) := by
  use fun _ => 0, .zero
  intros; constructor

protected theorem DPrimrec.sort {α_base : Sort u} {α : convert_to_new_type% α_base} :
    DPrimrec (convert_to_new% fun _ : α_base => Sort v) := .asort

protected theorem DPrimrec.dcomputable
    {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {f_base : (a : α_base) → β_base a} {f : convert_to_new_type% f_base}
    (hf : DPrimrec f) : DComputable f := by
  obtain ⟨g, hg, hg'⟩ := hf
  use g, .of_primrec hg
  intro a_base a n h
  use g n
  simpa using hg' h

alias DComputable.of_prim := DPrimrec.dcomputable

protected theorem DComputable.id {α_base : Sort u} {α : convert_to_new_type% α_base} :
    DComputable (fun ⦃a_base : α_base⦄ (a : α.1 a_base) => a) := .of_prim .id

protected theorem DComputable.const' {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : Sort v} {β : convert_to_new_type% β_base}
    {x_base : β_base} {x : convert_to_new_type% x_base}
    (h : IsRepresentable x) :
    DComputable (fun ⦃a_base : α_base⦄ (_ : α.1 a_base) => x) := .of_prim (.const' h)

protected theorem DComputable.const {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : Sort v} {β : convert_to_new_type% β_base}
    [FullyRepresentable β] {x_base : β_base} {x : convert_to_new_type% x_base} :
    DComputable (fun ⦃a_base : α_base⦄ (_ : α.1 a_base) => x) := .of_prim (.const x)

protected theorem DComputable.comp {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : Sort v} {β : convert_to_new_type% β_base}
    {γ_base : β_base → Sort w} {γ : convert_to_new_type% γ_base}
    {f_base : (x : β_base) → γ_base x} {f : convert_to_new_type% f_base}
    {g_base : α_base → β_base} {g : convert_to_new_type% g_base}
    (hf : DComputable f) (hg : DComputable g) :
    DComputable (convert_to_new% (fun a => f_base (g_base a))) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  refine ⟨_, hgf.comp hgg, ?_⟩
  intro a_base a n han
  obtain ⟨x, hx, hx'⟩ := hgg' han
  obtain ⟨y, hy, hy'⟩ := hgf' hx'
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  exact ⟨y, ⟨x, hx, hy⟩, hy'⟩

protected theorem DComputable.of_isProp {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {f_base : (a : α_base) → β_base a} {f : convert_to_new_type% f_base}
    (hprop : IsProp.{v}) :
    DComputable f := .of_prim (.of_isProp hprop)

protected theorem DComputable.proof {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Prop} {β : convert_to_new_type% β_base}
    {f_base : (a : α_base) → β_base a} {f : convert_to_new_type% f_base} :
    DComputable f := .of_prim .proof

protected theorem DComputable.asort {α_base : Sort u} {α : convert_to_new_type% α_base}
    {f_base : (a : α_base) → Sort v} {f : convert_to_new_type% f_base} :
    DComputable (convert_to_new% f_base) := .of_prim .asort

protected theorem DComputable.sort {α_base : Sort u} {α : convert_to_new_type% α_base} :
    DComputable (convert_to_new% fun _ : α_base => Sort v) := .asort

inductive New.PSigma._induct {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} (β : convert_to_new_type% β_base)
    (p_base : PSigma β_base) : Sort (max 1 u v) where
  | mk (fst : α.1 p_base.1) (snd : (β fst).1 p_base.2)

inductive New.PSigma._encoding {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} (β : convert_to_new_type% β_base)
    ⦃p_base : PSigma β_base⦄ (p : New.PSigma._induct β p_base) (n : ℕ) :
    Prop where
  | mk (fst : α.2 p.1 n.unpair.1) (snd : (β _).2 p.2 n.unpair.2)

def New.PSigma.{u, v} : convert_to_new_type% @PSigma.{u, v} := fun _ _ _ β =>
  .mk (New.PSigma._induct β) (New.PSigma._encoding β) not_isProp.{max u v}.elim

def New.PSigma.mk.{u, v} : convert_to_new_type% @PSigma.mk.{u, v} :=
  fun _ _ _ _ _ fst _ snd => .mk fst snd

def New.PSigma.fst.{u, v} : convert_to_new_type% @PSigma.fst.{u, v} :=
  fun _ _ _ _ _ x => x.1

def New.PSigma.snd.{u, v} : convert_to_new_type% @PSigma.snd.{u, v} :=
  fun _ _ _ _ _ x => x.2

theorem New.PSigma.mk.primrec.{c, u, v}
    {ctx_base : Sort c} {ctx : convert_to_new_type% ctx_base}
    {α_base : ctx_base → Sort u} {α : convert_to_new_type% α_base}
    {β_base : (c : ctx_base) → α_base c → Sort v} {β : convert_to_new_type% β_base}
    {fst_base : (c : ctx_base) → α_base c} {fst : convert_to_new_type% fst_base}
    (fst_prim : DPrimrec fst)
    {snd_base : (c : ctx_base) → β_base c (fst_base c)} {snd : convert_to_new_type% snd_base}
    (snd_prim : DPrimrec snd) :
    DPrimrec (convert_to_new% fun c =>
      @_root_.PSigma.mk (α_base c) (β_base c) (fst_base c) (snd_base c)) := by
  obtain ⟨f, hf, hf'⟩ := fst_prim
  obtain ⟨g, hg, hg'⟩ := snd_prim
  refine ⟨_, .pair hf hg, ?_⟩
  intros
  constructor
  · simp only [Nat.unpair_pair]
    apply hf'
    assumption
  · simp only [Nat.unpair_pair]
    apply hg'
    assumption

theorem New.PSigma.fst.primrec.{c, u, v}
    {ctx_base : Sort c} {ctx : convert_to_new_type% ctx_base}
    {α_base : ctx_base → Sort u} {α : convert_to_new_type% α_base}
    {β_base : (c : ctx_base) → α_base c → Sort v} {β : convert_to_new_type% β_base}
    {self_base : (c : ctx_base) → (a : α_base c) ×' β_base c a}
    {self : convert_to_new_type% self_base}
    (self_prim : DPrimrec (convert_to_new% self_base)) :
    DPrimrec (convert_to_new% fun c =>
      @_root_.PSigma.fst (α_base c) (β_base c) (self_base c)) := by
  obtain ⟨f, hf, hf'⟩ := self_prim
  refine ⟨_, .comp .left hf, ?_⟩
  intro a_base a n han
  exact (hf' han).1

theorem New.PSigma.snd.primrec.{c, u, v}
    {ctx_base : Sort c} {ctx : convert_to_new_type% ctx_base}
    {α_base : ctx_base → Sort u} {α : convert_to_new_type% α_base}
    {β_base : (c : ctx_base) → α_base c → Sort v} {β : convert_to_new_type% β_base}
    {self_base : (c : ctx_base) → (a : α_base c) ×' β_base c a}
    {self : convert_to_new_type% self_base}
    (self_prim : DPrimrec (convert_to_new% self_base)) :
    DPrimrec (convert_to_new% fun c =>
      @_root_.PSigma.snd (α_base c) (β_base c) (self_base c)) := by
  obtain ⟨f, hf, hf'⟩ := self_prim
  refine ⟨_, .comp .right hf, ?_⟩
  intro a_base a n han
  exact (hf' han).2

open Nat.Partrec (Code) in
theorem DPrimrec.curry
    {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {γ_base : (a : α_base) → β_base a → Sort w} {γ : convert_to_new_type% γ_base}
    {f_base : (a : α_base) → (b : β_base a) → γ_base a b} {f : convert_to_new_type% f_base}
    (hf : DComputable (convert_to_new% fun x : (a : α_base) ×' β_base a => f_base x.1 x.2)) :
    DPrimrec (convert_to_new% f_base) := by
  by_cases hprop : IsProp.{imax v w}
  · exact .of_isProp hprop
  obtain ⟨g, hg, hc⟩ := hf
  obtain ⟨c, rfl⟩ := Nat.Partrec.Code.exists_code.mp hg
  have : Nat.Primrec (fun a => Encodable.encode (c.curry a)) := by
    rw [← Primrec.nat_iff]
    exact .comp .encode (Code.primrec₂_curry.comp (.const c) .id)
  refine ⟨_, this, ?_⟩
  intro a_base a n hna
  rw [encoding_pi_def hprop]
  intro b_base b m hmb
  simp only [Denumerable.ofNat_encode, Code.eval_curry]
  exact @hc ⟨_, _⟩ ⟨a, b⟩ (Nat.pair n m) ⟨by simpa, by simpa⟩

theorem DPrimrec.constCurry.{u}
    {β_base : Sort v} {β : convert_to_new_type% β_base}
    {γ_base : β_base → Sort w} {γ : convert_to_new_type% γ_base}
    {f_base : (a : β_base) → γ_base a} {f : convert_to_new_type% f_base}
    (hf : DComputable f)
    {α_base : Sort u} {α : convert_to_new_type% α_base} :
    DPrimrec (convert_to_new% fun _ : α_base => f_base) := by
  refine .const' (x := convert_to_new% f_base) ?_
  rwa [isRepresentable_function_iff]

protected theorem DComputable.constCurry
    {β_base : Sort v} {β : convert_to_new_type% β_base}
    {γ_base : β_base → Sort w} {γ : convert_to_new_type% γ_base}
    {f_base : (a : β_base) → γ_base a} {f : convert_to_new_type% f_base}
    (hf : DComputable f)
    {α_base : Sort u} {α : convert_to_new_type% α_base} :
    DComputable (convert_to_new% fun _ : α_base => f_base) :=
  .of_prim (.constCurry hf)

theorem DPrimrec.curriedApp.{u}
    {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {γ_base : (a : α_base) → β_base a → Sort w} {γ : convert_to_new_type% γ_base}
    {f_base : (a : α_base) → (b : β_base a) → γ_base a b} {f : convert_to_new_type% f_base}
    (hf : DPrimrec (convert_to_new% fun x : (a : α_base) ×' β_base a => f_base x.1 x.2))
    {g_base : (a : α_base) → β_base a} {g : convert_to_new_type% g_base}
    (hg : DPrimrec g) :
    DPrimrec (convert_to_new% fun x => f_base x (g_base x)) :=
  .comp hf (New.PSigma.mk.primrec .id hg)

example
    {β_base : Sort v} {β : convert_to_new_type% β_base}
    {γ_base : β_base → Sort w} {γ : convert_to_new_type% γ_base}
    {δ_base : (a : β_base) → γ_base a → Sort w'} {δ : convert_to_new_type% δ_base}
    {f_base : (a : β_base) → (b : γ_base a) → δ_base a b} {f : convert_to_new_type% f_base}
    (hf : DPrimrec (convert_to_new% fun x : (a : β_base) ×' γ_base a => f_base x.1 x.2))
    {α_base : Sort u} {α : convert_to_new_type% α_base}
    {g₁_base : α_base → β_base} {g₁ : convert_to_new_type% g₁_base}
    (hg₁ : DPrimrec g₁)
    {g₂_base : (a : α_base) → γ_base (g₁_base a)} {g₂ : convert_to_new_type% g₂_base}
    (hg₂ : DPrimrec g₂) :
    DPrimrec (convert_to_new% fun x => f_base (g₁_base x) (g₂_base x)) :=
  .comp hf (New.PSigma.mk.primrec hg₁ hg₂)


/-open Nat.Partrec (Code) in
theorem dcomputable_curry
    {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}
    [EncodingRelation α] [∀ x, EncodingRelation (β x)] [∀ x y, EncodingRelation (γ x y)]
    {f : (a : α) → (b : β a) → γ a b} :
    DComputable f ↔ DComputable (fun x : (a : α) ×' β a => f x.1 x.2) := by
  by_cases h : IsProp.{imax v w}
  · have := @(isProp_of_isProp_imax.{v, w} h).irrelevant
    apply iff_of_true <;> apply DComputable.irrel
  obtain ⟨evalc, hevalc⟩ := Code.exists_code.mp Code.eval_part
  constructor
  · rintro ⟨f, hf, hf'⟩
    have : Nat.Partrec (fun a => (f a.unpair.1).bind
        fun c => (Code.ofNatCode c).eval a.unpair.2) := by
      rw [← Partrec.nat_iff] at hf ⊢
      refine .bind (hf.comp (.comp .fst .unpair)) ?_
      refine Code.eval_part.comp ?_ (.comp .snd (.comp .unpair .fst))
      exact .comp (Computable.ofNat Code) .snd
    refine ⟨_, this, ?_⟩
    intro n ⟨a, b⟩ ⟨h₁, h₂⟩
    obtain ⟨x, hx, hc⟩ := hf' h₁
    rw [encodes_pi_def] at hc
    obtain ⟨y, hy, hy'⟩ := hc _ _ h₂
    simp only [Part.mem_bind_iff]
    refine ⟨y, ⟨_, hx, ?_⟩, hy'⟩
    simpa [← Code.ofNatCode_eq]
  · intro h
    exact .of_prim (.curry h)-/

protected theorem DComputable.curry
    {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {γ_base : (a : α_base) → β_base a → Sort w} {γ : convert_to_new_type% γ_base}
    {f_base : (a : α_base) → (b : β_base a) → γ_base a b} {f : convert_to_new_type% f_base}
    (hf : DComputable (convert_to_new% (fun x : (a : α_base) ×' β_base a => f_base x.1 x.2))) :
    DComputable (convert_to_new% f_base) :=
  .of_prim (.curry hf)

/-protected theorem DPrimrec.constCurry
    {α : Sort u} {β : Sort v} {γ : β → Sort w} {f : (a : β) → γ a}
    [EncodingRelation α] [EncodingRelation β] [∀ a, EncodingRelation (γ a)]
    (hf : DComputable f) : DPrimrec fun _ : α => f := by
  refine .const' ?_
  rwa [isRepresentable_function_iff]

protected theorem DComputable.constCurry
    {α : Sort u} {β : Sort v} {γ : β → Sort w} {f : (a : β) → γ a}
    [EncodingRelation α] [EncodingRelation β] [∀ a, EncodingRelation (γ a)]
    (hf : DComputable f) : DComputable fun _ : α => f := .of_prim (.constCurry hf)-/

protected theorem DComputable.app
    {ctx_base : Sort u} {ctx : convert_to_new_type% ctx_base}
    {α_base : ctx_base → Sort v} {α : convert_to_new_type% α_base}
    {β_base : (c : ctx_base) → α_base c → Sort w} {β : convert_to_new_type% β_base}
    {f_base : (c : ctx_base) → (a : α_base c) → β_base c a} {f : convert_to_new_type% f_base}
    {g_base : (c : ctx_base) → α_base c} {g : convert_to_new_type% g_base}
    (hf : DComputable (convert_to_new% f_base)) (hg : DComputable (convert_to_new% g_base)) :
    DComputable (convert_to_new% fun c => f_base c (g_base c)) := by
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
  · intro a_base a n han
    obtain ⟨x, hx, hc⟩ := hgf' han
    rw [encoding_pi_def hprop] at hc
    obtain ⟨y, hy, hy'⟩ := hgg' han
    simp only [Part.mem_bind_iff, fn]
    obtain ⟨z, hz, hz'⟩ := hc hy'
    exact ⟨z, ⟨_, hx, y, hy, by simpa using hz⟩, hz'⟩

theorem dcomputable_curry
    {α_base : Sort u} {α : convert_to_new_type% α_base}
    {β_base : α_base → Sort v} {β : convert_to_new_type% β_base}
    {γ_base : (a : α_base) → β_base a → Sort w} {γ : convert_to_new_type% γ_base}
    {f_base : (a : α_base) → (b : β_base a) → γ_base a b} {f : convert_to_new_type% f_base} :
    DComputable (convert_to_new% f_base) ↔
      DComputable (convert_to_new% fun x : (a : α_base) ×' β_base a => f_base x.1 x.2) := by
  constructor
  · intro f_comp
    refine .app ?_ ?_
    · refine .app (f := convert_to_new% fun _ : (a : α_base) ×' β_base a => f_base) ?_ ?_
      · exact .constCurry f_comp
      · refine .of_prim ?_
        apply New.PSigma.fst.primrec
        exact .id
    · refine .of_prim ?_
      apply New.PSigma.snd.primrec
      exact .id
  · exact .curry
