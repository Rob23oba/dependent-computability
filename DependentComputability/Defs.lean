import Mathlib.Computability.PartrecCode

variable {α : Sort u}

@[pp_with_univ]
def IsProp := ∀ α : Sort u, ∀ a b : α, a = b

theorem isProp_prop : IsProp.{0} := by
  intro h a b
  rfl

theorem not_isProp : ¬ IsProp.{max u 1} := by
  intro h
  specialize h (PULift.{u} Bool) ⟨false⟩ ⟨true⟩
  simp at h

theorem isProp_of_isProp_imax (h : IsProp.{imax u v}) : IsProp.{v} := by
  intro α a b
  specialize h (PUnit.{u} → α) (fun _ => a) (fun _ => b)
  exact congrArg (· ⟨⟩) h

local syntax "isProp_elim" : tactic

open Qq in
elab_rules : tactic
  | `(tactic| isProp_elim) => do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← goal.getType
    let .forallE _ (.const ``IsProp [u]) b _ ← Lean.Meta.whnfD goalType | failure
    if u.isNeverZero && !b.hasLooseBVars then
      have b : Q(Prop) := b
      have proof : Q(¬IsProp.{max u 1}) := q(not_isProp.{u})
      have proof : Q(¬IsProp.{u}) := proof
      goal.assign q(fun h : IsProp.{u} => (absurd h $proof : $b))
    else
      failure

class EncodingRelation (α : Sort u) where
  Encodes : ℕ → α → Prop
  isProp_imp : IsProp.{u} → ∀ n h, Encodes n h ↔ n = 0 := by first | isProp_elim | simp

theorem IsProp.encodes_iff {α : Sort u} [EncodingRelation α] {n : ℕ} {x : α} (h : IsProp.{u}) :
    EncodingRelation.Encodes n x ↔ n = 0 := EncodingRelation.isProp_imp h n x

structure EncodableSort where
  ToType : Sort u
  [Encoding : EncodingRelation ToType]

attribute [coe] EncodableSort.ToType

instance : CoeSort EncodableSort (Sort u) := ⟨EncodableSort.ToType⟩
instance (α : EncodableSort.{u}) : EncodingRelation α := α.Encoding

open EncodingRelation (Encodes)

def IsRepresentable {α : Sort u} [EncodingRelation α] (x : α) : Prop :=
  ∃ n, Encodes n x

class FullyRepresentable (α : Sort u) [EncodingRelation α] where
  representable : ∀ x : α, IsRepresentable x

class Irrelevant (α : Sort u) [EncodingRelation α] where
  encodes : ∀ x : α, Encodes 0 x

attribute [simp low] Irrelevant.encodes

theorem IsProp.irrelevant {α : Sort u} [EncodingRelation α] (h : IsProp.{u}) :
    Irrelevant α where
  encodes x := by rw [h.encodes_iff]

instance irrelevantProp [EncodingRelation p] : Irrelevant (p : Prop) :=
  IsProp.irrelevant isProp_prop

structure Encoding (α : Sort u) [EncodingRelation α] where
  repr : ℕ

class CompatibleEncodingRelation (α : Type u) [Encodable α] [EncodingRelation α]
    extends FullyRepresentable α where
  encode : ℕ → ℕ := id
  decode : ℕ → ℕ := id
  decode_encode (n : ℕ) : decode (encode n) = n := by intro; rfl
  encode_primrec : Nat.Primrec encode := by exact .id
  decode_primrec : Nat.Primrec decode := by exact .id
  encode_eq {n : ℕ} {x : α} (hx : Encodes n x) : encode n = Encodable.encode x

attribute [simp] CompatibleEncodingRelation.decode_encode

namespace CompatibleEncodingRelation

instance {α : Type u} [EncodingRelation α] [Encodable α] [CompatibleEncodingRelation α] :
    Primcodable (Encoding α) where
  encode x := encode α x.repr
  decode n := some ⟨decode α n⟩
  encodek := by simp
  prim := .comp .succ (.comp encode_primrec decode_primrec)

end CompatibleEncodingRelation

theorem EncodingRelation.Encodes.encode_eq {α : Type u} [Encodable α] [EncodingRelation α]
    [CompatibleEncodingRelation α] {n : ℕ} {x : α} (h : Encodes n x) :
    Encodable.encode x = Encodable.encode (⟨n⟩ : Encoding α) :=
  CompatibleEncodingRelation.encode_eq h |>.symm

theorem CompatibleEncodingRelation.encodes_unique {α : Type u}
    [Encodable α] [EncodingRelation α] [CompatibleEncodingRelation α] {n : ℕ} {x y : α}
    (hx : Encodes n x) (hy : Encodes n y) : x = y := by
  apply Encodable.encode_injective
  rw [hx.encode_eq, hy.encode_eq]

theorem Option.rec_eq_elim {α : Type u} {β : Type v} (x : Option α) (n : β) (s : α → β) :
    Option.rec n s x = Option.elim x n s := by
  cases x <;> rfl

theorem Encoding.primrec_mk {α : Type u}
    [Encodable α] [EncodingRelation α] [CompatibleEncodingRelation α] :
    Primrec (Encoding.mk : ℕ → Encoding α) :=
  Nat.Primrec.comp .succ CompatibleEncodingRelation.encode_primrec

theorem Encoding.primrec_repr {α : Type u}
    [Encodable α] [EncodingRelation α] [CompatibleEncodingRelation α] :
    Primrec (Encoding.repr : Encoding α → ℕ) :=
  Nat.Primrec.comp .succ CompatibleEncodingRelation.decode_primrec

def Encoding.of {α : Type u} [Encodable α] [EncodingRelation α] [CompatibleEncodingRelation α]
    (x : α) : Encoding α := ⟨CompatibleEncodingRelation.decode α (Encodable.encode x)⟩

theorem Encoding.encode_of {α : Type u}
    [Encodable α] [EncodingRelation α] [CompatibleEncodingRelation α]
    (x : α) : Encodable.encode (Encoding.of x) = Encodable.encode x := by
  obtain ⟨n, hn⟩ := FullyRepresentable.representable x
  simp [of, hn.encode_eq, Encodable.encode]

theorem Encoding.encodes_of {α : Type u}
    [Encodable α] [EncodingRelation α] [CompatibleEncodingRelation α]
    (x : α) : Encodes (Encoding.of x).repr x := by
  obtain ⟨n, hn⟩ := FullyRepresentable.representable x
  simp [of, hn.encode_eq, Encodable.encode, hn]

open CompatibleEncodingRelation in
theorem Encoding.primrec_of {α : Type u}
    [Primcodable α] [EncodingRelation α] [CompatibleEncodingRelation α] :
    Primrec (Encoding.of : α → Encoding α) := by
  unfold of
  exact .comp primrec_mk (.comp (Primrec.nat_iff.mpr decode_primrec) .encode)

@[instance_reducible]
def instEncodingRelationOfEncodable {α : Type u} [Encodable α] : EncodingRelation α where
  Encodes n a := n = Encodable.encode a

attribute [local instance] instEncodingRelationOfEncodable in
instance {α : Type u} [Primcodable α] : CompatibleEncodingRelation α where
  encode_eq h := h
  representable x := ⟨Encodable.encode x, rfl⟩

-- proofs are irrelevant
-- this is not an instance because it would create lots of diamonds
@[instance_reducible]
def instEncodingRelationProof {p : Prop} : EncodingRelation p where
  Encodes n _ := n = 0

-- instances for some basic stuff
instance : EncodingRelation (p ∧ q) := instEncodingRelationProof
instance : EncodingRelation (p ∨ q) := instEncodingRelationProof
instance : EncodingRelation (¬p) := instEncodingRelationProof
instance : EncodingRelation (a = b) := instEncodingRelationProof

-- types are irrelevant
instance : EncodingRelation (Sort u) where
  Encodes n _ := n = 0

instance : Irrelevant (Sort u) where
  encodes _ := rfl

instance : EncodingRelation EncodableSort.{u} where
  Encodes n _ := n = 0

instance : Irrelevant EncodableSort.{u} where
  encodes _ := rfl

instance : Irrelevant EncodableSort.{u} where
  encodes _ := rfl

instance : EncodingRelation PUnit.{u} where
  Encodes n _ := n = 0

instance : FullyRepresentable PUnit.{u} where
  representable _ := ⟨0, rfl⟩

instance : Irrelevant PUnit.{u} where
  encodes _ := rfl

instance : CompatibleEncodingRelation PUnit.{u + 1} where
  encode_eq h := h

instance : EncodingRelation PEmpty.{u} where
  Encodes _ x := x.elim

instance : Irrelevant PEmpty.{u} where
  encodes := nofun

instance : EncodingRelation Nat where
  Encodes a b := a = b

instance : FullyRepresentable Nat where
  representable n := ⟨n, rfl⟩

instance : CompatibleEncodingRelation Nat where
  encode_eq h := h

@[simp] theorem Encodes.nat_iff (a b : ℕ) : Encodes a b ↔ a = b := Iff.rfl

instance {α : Sort u} {β : α → Sort v} [EncodingRelation α] [∀ x, EncodingRelation (β x)] :
    EncodingRelation ((a : α) ×' β a) where
  Encodes n x := Encodes n.unpair.1 x.1 ∧ Encodes n.unpair.2 x.2

instance {α : Sort u} {β : α → Sort v} [EncodingRelation α] [∀ x, EncodingRelation (β x)]
    [Irrelevant α] [∀ x, Irrelevant (β x)] : Irrelevant ((a : α) ×' β a) where
  encodes _ := ⟨Irrelevant.encodes _, Irrelevant.encodes _⟩

instance {α : Type u} {β : Type v} [EncodingRelation α] [EncodingRelation β] :
    EncodingRelation (α × β) where
  Encodes n x := Encodes n.unpair.1 x.1 ∧ Encodes n.unpair.2 x.2

instance {α : Sort u} {β : Sort v} [EncodingRelation α] [EncodingRelation β] :
    EncodingRelation (α ×' β) where
  Encodes n x := Encodes n.unpair.1 x.1 ∧ Encodes n.unpair.2 x.2

instance {α : Type u} {β : α → Type v}
    [Encodable α] [EncodingRelation α] [∀ x, EncodingRelation (β x)] :
    EncodingRelation ((a : α) × β a) where
  Encodes n x := Encodes n.unpair.1 x.1 ∧ Encodes n.unpair.2 x.2

instance {α : Sort u} {p : α → Prop} [EncodingRelation α] : EncodingRelation { x : α // p x } where
  Encodes a b := Encodes a b.1

instance {α : Sort u} {r : α → α → Prop} [EncodingRelation α] : EncodingRelation (Quot r) where
  Encodes a b := ∃ x, Quot.mk r x = b ∧ Encodes a x
  isProp_imp hprop := by
    rintro n ⟨h⟩
    simp [hprop.encodes_iff]

instance {α : Sort u} {β : α → Sort v} [EncodingRelation α] [∀ x, EncodingRelation (β x)] :
    EncodingRelation ((a : α) → β a) where
  Encodes n f := (IsProp.{imax u v} → n = 0) ∧
    ∀ a b, Encodes a b → ∃ y ∈ (Denumerable.ofNat Nat.Partrec.Code n).eval a, Encodes y (f b)
  isProp_imp hprop := by
    intro n f
    have := @(isProp_of_isProp_imax.{u, v} hprop).encodes_iff
    simp only [hprop, forall_const, this, exists_eq_right, and_iff_left_iff_imp]
    rintro rfl
    intro a b h
    simp only [Nat.Partrec.Code.ofNatCode_eq, Nat.Partrec.Code.ofNatCode, Nat.Partrec.Code.eval,
      pure, PFun.pure, Part.mem_some_iff]

theorem encodes_pi_def {α : Sort u} {β : α → Sort v}
    [EncodingRelation α] [∀ x, EncodingRelation (β x)]
    (h : ¬ IsProp.{imax u v} := by first | isProp_elim | assumption)
    {n : ℕ} (f : (a : α) → β a) :
    Encodes n f ↔ ∀ a b, Encodes a b →
      ∃ y ∈ (Denumerable.ofNat Nat.Partrec.Code n).eval a, Encodes y (f b) := by
  simp [Encodes, h]

instance {α : Type u} [EncodingRelation α] : EncodingRelation (Part α) where
  Encodes n p := ∀ x ∈ p, ∃ y ∈ (Denumerable.ofNat Nat.Partrec.Code n).eval 0, Encodes n x

instance {α : Sort u} {β : α → Sort v} [EncodingRelation α] [∀ x, EncodingRelation (β x)]
    [∀ x, Irrelevant (β x)] : Irrelevant ((a : α) → β a) where
  encodes _ := by
    by_cases hprop : IsProp.{imax u v}
    · rw [EncodingRelation.isProp_imp hprop]
    · rw [encodes_pi_def]
      intro a b h
      use 0
      simp [Nat.Partrec.Code.ofNatCode_eq, Nat.Partrec.Code.ofNatCode, Nat.Partrec.Code.eval,
        pure, PFun.pure]

def DComputable {α : Sort u} {β : α → Sort v} [EncodingRelation α] [∀ x, EncodingRelation (β x)]
    (f : (a : α) → β a) : Prop :=
  ∃ g, Nat.Partrec g ∧ ∀ ⦃a b⦄, Encodes a b → ∃ y ∈ g a, Encodes y (f b)

def DPrimrec {α : Sort u} {β : α → Sort v} [EncodingRelation α] [∀ x, EncodingRelation (β x)]
    (f : (a : α) → β a) : Prop :=
  ∃ g, Nat.Primrec g ∧ ∀ ⦃a b⦄, Encodes a b → Encodes (g a) (f b)

theorem isRepresentable_function_iff {α : Sort u} {β : α → Sort v}
    [EncodingRelation α] [∀ x, EncodingRelation (β x)] {f : (a : α) → β a} :
    IsRepresentable f ↔ DComputable f := by
  by_cases hprop : IsProp.{imax u v}
  · simp only [IsRepresentable, hprop.encodes_iff, exists_eq, true_iff]
    refine ⟨_, Nat.Partrec.zero, ?_⟩
    simp [pure, PFun.pure, (isProp_of_isProp_imax.{u, v} hprop).encodes_iff]
  simp only [IsRepresentable, encodes_pi_def.{u, v} hprop]
  constructor
  · rintro ⟨n, hn⟩
    let c := Denumerable.ofNat Nat.Partrec.Code n
    exact ⟨c.eval, Partrec.nat_iff.mp (Nat.Partrec.Code.eval_part.comp (.const c) .id), hn⟩
  · rintro ⟨g, hg, hg'⟩
    obtain ⟨c, rfl⟩ := Nat.Partrec.Code.exists_code.mp hg
    use Encodable.encode c
    simpa using hg'

theorem dprimrec_iff_primrec {α : Type u} {β : Type v} [Primcodable α] [Primcodable β]
    [EncodingRelation α] [EncodingRelation β]
    [CompatibleEncodingRelation α] [CompatibleEncodingRelation β]
    (f : α → β) : DPrimrec f ↔ Primrec f := by
  rw [DPrimrec]
  constructor
  · rintro ⟨g, hgprim, hg'⟩
    rw [Primrec]
    rw [← Primrec.nat_iff] at hgprim ⊢
    let g' (a : Encoding α) : Encoding β := ⟨g a.repr⟩
    have commute (a : α) : g' (Encoding.of a) = Encoding.of (f a) := by
      have := hg' (Encoding.encodes_of a)
      simp [Encoding.of, g', this.encode_eq, Encodable.encode]
    have hg'prim : Primrec g' := .comp Encoding.primrec_mk (.comp hgprim Encoding.primrec_repr)
    let fn (n : ℕ) : ℕ :=
      (Encodable.decode n : Option α).casesOn 0 (fun a => Encodable.encode (g' (Encoding.of a)) + 1)
    have : Primrec fn :=
      .option_casesOn .decode (.const 0)
        (Primrec.succ.comp (.comp .encode (.comp hg'prim (.comp Encoding.primrec_of .snd))))
    refine this.of_eq ?_
    intro n
    simp only [fn]
    rcases h : (Encodable.decode n : Option α) with _ | a
    · simp
    · have := Encoding.encode_of (f a)
      simp [← this, commute]
  · intro hf
    let fn (n : ℕ) : ℕ :=
      (Encodable.decode (Encodable.encode (⟨n⟩ : Encoding α)) : Option α).casesOn
        0 (fun a => (Encoding.of (f a)).repr)
    refine ⟨fn, ?_, ?_⟩
    · rw [← Primrec.nat_iff]
      exact .option_casesOn (.comp .decode (.comp .encode Encoding.primrec_mk)) (.const 0) <|
        Encoding.primrec_repr.comp (Encoding.primrec_of.comp (hf.comp .snd))
    · intro a n han
      simp [fn, ← han.encode_eq, Encoding.encodes_of]

theorem dcomputable_iff_computable {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] [EncodingRelation α] [EncodingRelation β]
    [CompatibleEncodingRelation α] [CompatibleEncodingRelation β]
    {f : α → β} : DComputable f ↔ Computable f := by
  constructor
  · rintro ⟨g, hgprim, hg'⟩
    rw [Computable, Partrec]
    rw [← Partrec.nat_iff] at hgprim ⊢
    let g' (a : Encoding α) : Part (Encoding β) := (g a.repr).map Encoding.mk
    have commute (a : α) : g' (Encoding.of a) = Encoding.of (f a) := by
      obtain ⟨y, hy, this⟩ := hg' (Encoding.encodes_of a)
      simp only [Encoding.of] at hy
      simp [Encoding.of, g', this.encode_eq, Part.eq_some_iff.mpr hy, Encodable.encode]
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
    · have := Encoding.encode_of (f a)
      simp [← this, commute]
  · intro hf
    let fn (n : ℕ) : ℕ :=
      (Encodable.decode (Encodable.encode (⟨n⟩ : Encoding α)) : Option α).casesOn
        0 (fun a => (Encoding.of (f a)).repr)
    refine ⟨fn, ?_, ?_⟩
    · rw [← Partrec.nat_iff]
      change Computable fn
      unfold fn
      exact .option_casesOn (.comp .decode (.comp .encode Encoding.primrec_mk.to_comp))
        (.const 0) (Encoding.primrec_repr.to_comp.comp (Encoding.primrec_of.to_comp.comp
          (hf.comp .snd)))
    · intro a n han
      simp [fn, ← han.encode_eq, Encoding.encodes_of]

/-
theorem dcomputable_iff_partrec {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] [EncodingRelation α] [EncodingRelation β]
    [CompatibleEncodingRelation α] [CompatibleEncodingRelation β]
    {f : α → Part β} : DComputable f ↔ Partrec f := by
  constructor
  · sorry
  · intro hf
    let fn (n : ℕ) : Part ℕ :=
      (Encodable.decode (Encodable.encode (⟨n⟩ : Encoding α)) : Option α).casesOn
        0 (fun a => (f a).map (fun x => (Encoding.of x).repr))
    refine ⟨fn, ?_, ?_⟩
    · rw [← Partrec.nat_iff]
      unfold fn
      refine .optionCasesOn_right (.comp .decode (.comp .encode Encoding.primrec_mk.to_comp))
        (.const 0) (.map (.comp hf .snd) ?_)
      exact Encoding.primrec_repr.to_comp.comp (Encoding.primrec_of.to_comp.comp .snd)
    · intro a n han

      simp [fn, ← han.encode_eq, Encoding.encodes_of]
-/

protected theorem DPrimrec.id {α : Sort u} [EncodingRelation α] : DPrimrec (fun x : α => x) := by
  use id, .id
  simp

protected theorem DPrimrec.const' {α β : Sort*} [EncodingRelation α] [EncodingRelation β]
    {x : β} (h : IsRepresentable x) : DPrimrec (fun _ : α => x) := by
  obtain ⟨n, hn⟩ := h
  use fun _ => n, .const n
  intro a b hab
  assumption

protected theorem DPrimrec.const {α β : Sort*} [EncodingRelation α] [EncodingRelation β]
    [FullyRepresentable β] (x : β) : DPrimrec (fun _ : α => x) :=
  .const' (FullyRepresentable.representable x)

protected theorem DPrimrec.comp {α : Sort u} {β : Sort v} {γ : β → Sort w}
    {f : (x : β) → γ x} {g : α → β}
    [EncodingRelation α] [EncodingRelation β] [∀ x, EncodingRelation (γ x)]
    (hf : DPrimrec f) (hg : DPrimrec g) :
    DPrimrec (fun a => f (g a)) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  refine ⟨_, hgf.comp hgg, ?_⟩
  intro a b hab
  exact hgf' (hgg' hab)

protected theorem DPrimrec.irrel {α : Sort u} {β : α → Sort v}
    [EncodingRelation α] [∀ x, EncodingRelation (β x)] [∀ x, Irrelevant (β x)]
    {f : (a : α) → β a} : DPrimrec f := by
  use fun _ => 0, .zero
  intro a b h
  exact Irrelevant.encodes _

protected theorem DPrimrec.dcomputable {α : Sort u} {β : α → Sort v}
    [EncodingRelation α] [∀ x, EncodingRelation (β x)]
    {f : (a : α) → β a} (hf : DPrimrec f) : DComputable f := by
  obtain ⟨g, hg, hg'⟩ := hf
  use g, .of_primrec hg
  intro a b h
  use g a
  simpa using hg' h

alias DComputable.of_prim := DPrimrec.dcomputable

protected theorem DComputable.id {α : Sort u} [EncodingRelation α] :
    DComputable (fun x : α => x) := .of_prim .id

protected theorem DComputable.const' {α β : Sort*} [EncodingRelation α] [EncodingRelation β]
    {x : β} (h : IsRepresentable x) : DComputable (fun _ : α => x) := .of_prim (.const' h)

protected theorem DComputable.const {α β : Sort*} [EncodingRelation α] [EncodingRelation β]
    [FullyRepresentable β] (x : β) : DComputable (fun _ : α => x) := .of_prim (.const x)

protected theorem DComputable.comp {α : Sort u} {β : Sort v} {γ : β → Sort w}
    {f : (x : β) → γ x} {g : α → β}
    [EncodingRelation α] [EncodingRelation β] [∀ x, EncodingRelation (γ x)]
    (hf : DComputable f) (hg : DComputable g) :
    DComputable (fun a => f (g a)) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  refine ⟨_, hgf.comp hgg, ?_⟩
  intro a b hab
  obtain ⟨x, hx, hx'⟩ := hgg' hab
  obtain ⟨y, hy, hy'⟩ := hgf' hx'
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  exact ⟨y, ⟨x, hx, hy⟩, hy'⟩

protected theorem DComputable.irrel {α : Sort u} {β : α → Sort v}
    [EncodingRelation α] [∀ x, EncodingRelation (β x)] [∀ x, Irrelevant (β x)]
    {f : (a : α) → β a} : DComputable f := .of_prim .irrel

open Nat.Partrec (Code) in
theorem DPrimrec.curry {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}
    {f : (a : α) → (b : β a) → γ a b}
    [EncodingRelation α] [∀ x, EncodingRelation (β x)] [∀ x y, EncodingRelation (γ x y)]
    (hf : DComputable (fun x : (a : α) ×' β a => f x.1 x.2)) :
    DPrimrec f := by
  by_cases hprop : IsProp.{imax v w}
  · have := @hprop.irrelevant
    exact .irrel
  obtain ⟨g, hg, hc⟩ := hf
  obtain ⟨c, rfl⟩ := Nat.Partrec.Code.exists_code.mp hg
  have : Nat.Primrec (fun a => Encodable.encode (c.curry a)) := by
    rw [← Primrec.nat_iff]
    exact .comp .encode (Code.primrec₂_curry.comp (.const c) .id)
  refine ⟨_, this, ?_⟩
  intro n a hna
  rw [encodes_pi_def]
  intro m b hmb
  simp only [Denumerable.ofNat_encode, Code.eval_curry]
  exact @hc (Nat.pair n m) ⟨a, b⟩ ⟨by simpa, by simpa⟩

open Nat.Partrec (Code) in
theorem dcomputable_curry {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}
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
    exact .of_prim (.curry h)

protected theorem DComputable.curry {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}
    {f : (a : α) → (b : β a) → γ a b}
    [EncodingRelation α] [∀ a, EncodingRelation (β a)] [∀ a b, EncodingRelation (γ a b)]
    (hf : DComputable fun x : (a : α) ×' β a => f x.1 x.2) : DComputable f :=
  dcomputable_curry.mpr hf

protected theorem DPrimrec.constCurry
    {α : Sort u} {β : Sort v} {γ : β → Sort w} {f : (a : β) → γ a}
    [EncodingRelation α] [EncodingRelation β] [∀ a, EncodingRelation (γ a)]
    (hf : DComputable f) : DPrimrec fun _ : α => f := by
  refine .const' ?_
  rwa [isRepresentable_function_iff]

protected theorem DComputable.constCurry
    {α : Sort u} {β : Sort v} {γ : β → Sort w} {f : (a : β) → γ a}
    [EncodingRelation α] [EncodingRelation β] [∀ a, EncodingRelation (γ a)]
    (hf : DComputable f) : DComputable fun _ : α => f := .of_prim (.constCurry hf)

protected theorem DComputable.app
    {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → (a : α c) → β c a} {g : (c : ctx) → α c}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c x, EncodingRelation (β c x)]
    (hf : DComputable f) (hg : DComputable g) :
    DComputable (fun c => f c (g c)) := by
  by_cases h : IsProp.{imax v w}
  · have := @(isProp_of_isProp_imax.{v, w} h).irrelevant
    apply DComputable.irrel
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  let fn (n : ℕ) : Part ℕ :=
    (gf n).bind fun a => (gg n).bind fun b => (Denumerable.ofNat Nat.Partrec.Code a).eval b
  refine ⟨fn, ?_, ?_⟩
  · rw [← Partrec.nat_iff] at hgf hgg ⊢
    refine .bind hgf (.bind (.comp hgg .fst) (Nat.Partrec.Code.eval_part.comp ?_ .snd))
    exact .comp (.ofNat _) (.comp .snd .fst)
  · intro a b hab
    obtain ⟨x, hx, hc⟩ := hgf' hab
    rw [encodes_pi_def] at hc
    obtain ⟨y, hy, hy'⟩ := hgg' hab
    simp only [Part.mem_bind_iff, fn]
    obtain ⟨z, hz, hz'⟩ := hc y (g b) hy'
    exact ⟨z, ⟨_, hx, y, hy, by simpa using hz⟩, hz'⟩
