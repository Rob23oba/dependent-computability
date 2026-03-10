import DependentComputability.Tactic.RecursorModel

-- Credit to Anthony Vandikas for `ωProp` and `ωPart` (YellPika on github)

open scoped Delab

@[elab_as_elim]
def Nat.geRec {n : ℕ} {motive : ∀ m ≤ n, Sort u}
    (refl : motive n le_rfl) (step : ∀ m, (h : m < n) → motive (m + 1) h → motive m (le_of_lt h))
    {m : ℕ} (t : m ≤ n) : motive m t :=
  if h : m < n then
    step m h (Nat.geRec refl step h)
  else
    Nat.le_antisymm t (Nat.not_lt.mp h) ▸ refl
termination_by n - m
decreasing_by exact sub_succ_lt_self n m h

theorem countableChoice {α : Nat → Type*} (h : ∀ i, Nonempty (α i)) :
    Nonempty (∀ i, α i) := inferInstance

theorem _root_.New.countableChoice : new_type% @countableChoice.{u} := by
  intro α α' h h'
  have (i : ℕ) (i' : new_type% i) : Nonempty ((a : α i) × new_type% a) := by
    obtain @⟨a, b⟩ := @h' i i'
    exact ⟨a, b⟩
  refine .intro (val := ?_) ?_
  · intro x; exact (@this x ()).some.1
  · intro x _; exact (@this x ()).some.2

unsafe def Squash.countableChoiceImpl {α : Nat → Type u} (f : ∀ i, Squash (α i)) :
    Squash (∀ i, α i) := unsafeCast f

@[implemented_by Squash.countableChoiceImpl] -- "justification" below
def Squash.countableChoice {α : Nat → Type u} (f : ∀ i, Squash (α i)) :
    Squash (∀ i, α i) :=
  uniqueChoice (_root_.countableChoice fun i => by obtain ⟨x⟩ := f i; exact ⟨x⟩)

set_option linter.unusedVariables false in
@[other_dprim]
lemma Squash.countableChoice.dprim.{c, u} {ctx : Sort c}
    {α : ctx → Nat → Type u} (f : (c : ctx) → (i : Nat) → Squash (α c i))
    (f_prim : DPrim f) : DPrim fun c => Squash.countableChoice (f c) := .unsafeIntro

@[other_dprim]
lemma Squash.countableChoice.dcomp.{c, u} {ctx : Sort c}
    {α : ctx → Nat → Type u} (f : (c : ctx) → (i : Nat) → Squash (α c i))
    (f_comp : DComp f) : DComp fun c => Squash.countableChoice (f c) :=
  .app (.curry (.of_prim <| by other_dcomp_tac)) f_comp

lemma Part.mem_def {α : Type u} {x : Part α} {y : α} : y ∈ x ↔ ∃ h : x.Dom, x.get h = y := Iff.rfl

convert_to_new Subsingleton.allEq

open Denumerable (ofNat) in
open Nat.Partrec (Code) in
lemma _root_.New.Squash.countableChoice.dprim.{c, u} :
    new_type% @Squash.countableChoice.dprim.{c, u} := by
  intro ctx ctx' α α' f f' hf ⟨g, hg, hg'⟩
  refine ⟨g, hg, ?_⟩ -- by a miracle, `g` already works here
  intro c c' cn hcn
  specialize hg' hcn
  rw [encoding_pi_def not_isProp.{u + 1}] at hg'
  simp only [Part.mem_def, exists_exists_eq_and] at hg'
  have (i : ℕ) : Nonempty ((a : α c i) × (a' : (@α' c c' i ()).1 a) ×'
      (@α' c c' i ()).2 a' (((ofNat Code (g cn)).eval i).get (@hg' i () i rfl).1)) := by
    replace hg' := (@hg' i () i rfl).2
    generalize @f' c c' i () = f' at hg'
    generalize @f c i = f at f' hg'
    rcases hg' with @⟨x, x', _, hx⟩
    exact ⟨x, x', hx⟩
  replace ⟨this⟩ := countableChoice this
  let rep (i : ℕ) := (this i).1
  let rep_extra : new_type% rep := fun i _ => (this i).2.1
  have rep_enc (i : ℕ) := show (@α' c c' i ()).2 (@rep_extra i ()) _ from (this i).2.2
  clear_value rep rep_extra
  have_new eq := Subsingleton.allEq (Squash.mk rep) (Squash.countableChoice (f c))
  refine eq_extra.rec ?_
  constructor
  rw [encoding_pi_def not_isProp.{u + 1}]
  intro i () _ rfl
  exact ⟨_, Part.get_mem (@hg' i () i rfl).1, rep_enc i⟩

@[inline]
def Quotient.countableChoice {α : Nat → Type*} {S : ∀ i, Setoid (α i)}
    (f : ∀ i, Quotient (S i)) : @Quotient (∀ i, α i) inferInstance :=
  Quot.lift (fun g => ⟦fun i => g i⟧) ?_
    (Squash.countableChoice (α := fun i => { x : α i // f i = ⟦x⟧ })
      fun i => (f i).pliftOn (fun x h => .mk ⟨x, h⟩) fun _ _ _ _ _ => Subsingleton.allEq _ _)
where finally
  intro a b ⟨⟩
  apply Quotient.sound
  intro x
  apply Quotient.exact
  simp only [← (a x).2, ← (b x).2]

@[simp]
theorem Squash.countableChoice_mk {α : Nat → Type*} (f : ∀ i, α i) :
    countableChoice (fun i => Squash.mk (f i)) = .mk f := Subsingleton.allEq _ _

@[simp]
theorem Quotient.countableChoice_mk {α : Nat → Type*} {S : ∀ i, Setoid (α i)}
    (f : ∀ i, α i) : countableChoice (fun i => Quotient.mk (S i) (f i)) = ⟦f⟧ := by
  simp only [countableChoice, Quotient.pliftOn, Quot.pliftOn, Quot.rec, lift_mk,
    Squash.countableChoice_mk]
  rfl

@[simp]
theorem Quotient.eval_countableChoice {α : Nat → Type*} {S : ∀ i, Setoid (α i)}
    (f : ∀ i, Quotient (S i)) (i : ℕ) : (countableChoice f).eval i = f i := by
  have (i : ℕ) : Nonempty { x : α i // f i = ⟦x⟧ } := by
    rcases f i with ⟨x⟩
    exact ⟨x, rfl⟩
  replace ⟨this⟩ := _root_.countableChoice this
  rw [funext fun i => (this i).2]
  simp

def ωProp.setoid : Setoid (ℕ → Bool) where
  r f g := (∃ a, f a) ↔ (∃ a, g a)
  iseqv := { refl _ := .rfl, symm h := h.symm, trans h h' := h.trans h' }

structure ωProp where
  mk' ::
  val : Quotient ωProp.setoid

namespace ωProp

def mk (f : ℕ → Bool) : ωProp := ⟨.mk _ f⟩

@[simp]
theorem mk_eq_mk_iff {f g : ℕ → Bool} : mk f = mk g ↔ ((∃ a, f a) ↔ (∃ a, g a)) :=
  ⟨fun h => Quotient.exact (congrArg (·.val) h), fun h => congrArg ωProp.mk' (Quotient.sound h)⟩

def lift (f : (g : ℕ → Bool) → α)
    (h : ∀ g₁ g₂, ((∃ a, g₁ a) ↔ (∃ a, g₂ a)) → f g₁ = f g₂)
    (x : ωProp) : α :=
  x.val.lift f h

def pliftOn (x : ωProp) (f : (g : ℕ → Bool) → x = mk g → α)
    (h : ∀ g₁ g₂ h₁ h₂, ((∃ a, g₁ a) ↔ (∃ a, g₂ a)) → f g₁ h₁ = f g₂ h₂) : α :=
  x.val.pliftOn (fun a h => f a (congrArg ωProp.mk' h)) (fun a b _ _ => h a b _ _)

def liftPi (f : (ℕ → ℕ → Bool) → α)
    (h : ∀ g₁ g₂, (∀ x, (∃ a, g₁ x a) ↔ (∃ a, g₂ x a)) → f g₁ = f g₂)
    (g : ℕ → ωProp) : α :=
  (Quotient.countableChoice (fun i => (g i).val)).lift f h

def pliftOnPi (g : ℕ → ωProp) (f : (g' : ℕ → ℕ → Bool) → g = (fun n => mk (g' n)) → α)
    (h : ∀ g₁ g₂ h₁ h₂, (∀ x, (∃ a, g₁ x a) ↔ (∃ a, g₂ x a)) → f g₁ h₁ = f g₂ h₂) : α :=
  (Quotient.countableChoice (fun i => (g i).val)).pliftOn (fun g' hg' => f g' ?_) ?_
where finally
  · funext n
    replace hg' := congr($(hg').eval n)
    simp only [Quotient.eval_countableChoice, Quotient.eval_mk] at hg'
    exact congrArg ωProp.mk' hg'
  · intro a b h₁ h₂
    exact h a b _ _

@[elab_as_elim, induction_eliminator]
theorem induction {motive : ωProp → Prop} (mk : ∀ f, motive (mk f)) (t : ωProp) : motive t := by
  rcases t with ⟨⟨x⟩⟩
  apply mk

theorem inductionPi {motive : (ℕ → ωProp) → Prop}
    (mk : (f : ℕ → ℕ → Bool) → motive (fun n => mk (f n)))
    (t : ℕ → ωProp) : motive t := by
  have (i : ℕ) : Nonempty { x : ℕ → Bool // t i = ωProp.mk x } := by
    rcases t i with ⟨⟨x⟩⟩
    exact ⟨x, rfl⟩
  replace ⟨this⟩ := _root_.countableChoice this
  rw [funext fun i => (this i).2]
  apply mk

@[simp]
theorem lift_mk (f : (g : ℕ → Bool) → α)
    (h : ∀ g₁ g₂, ((∃ a, g₁ a) ↔ (∃ a, g₂ a)) → f g₁ = f g₂)
    (g : ℕ → Bool) : lift f h (mk g) = f g := rfl

@[simp]
theorem pliftOn_mk (x : ℕ → Bool) (f : (g : ℕ → Bool) → mk x = mk g → α)
    (h : ∀ g₁ g₂ h₁ h₂, ((∃ a, g₁ a) ↔ (∃ a, g₂ a)) → f g₁ h₁ = f g₂ h₂) :
    pliftOn (mk x) f h = f x rfl := rfl

@[simp]
theorem liftPi_mk (f : (ℕ → ℕ → Bool) → α)
    (h : ∀ g₁ g₂, (∀ x, (∃ a, g₁ x a) ↔ (∃ a, g₂ x a)) → f g₁ = f g₂)
    (g : ℕ → ℕ → Bool) : liftPi f h (fun n => mk (g n)) = f g := by
  simp [liftPi, mk]

@[simp]
theorem pliftOnPi_mk (g : ℕ → ℕ → Bool)
    (f : (g' : ℕ → ℕ → Bool) → (fun n => mk (g n)) = (fun n => mk (g' n)) → α)
    (h : ∀ g₁ g₂ h₁ h₂, (∀ x, (∃ a, g₁ x a) ↔ (∃ a, g₂ x a)) → f g₁ h₁ = f g₂ h₂) :
    pliftOnPi (fun n => mk (g n)) f h = f g rfl := by
  simp only [pliftOnPi, mk]
  rw! (castMode := .all) [Quotient.countableChoice_mk]
  rfl

@[coe]
def coe (x : ωProp) : Prop :=
  x.lift (∃ y, · y) (fun _ _ h => propext h)

instance : CoeSort ωProp Prop where
  coe := ωProp.coe

protected def false : ωProp := .mk fun _ => false
protected def true : ωProp := .mk fun _ => true

@[simp] theorem coe_mk (f : ℕ → Bool) : mk f ↔ ∃ n, f n := by simp [coe]
@[simp] theorem coe_false : ωProp.false ↔ False := by simp [ωProp.false]
@[simp] theorem coe_true : ωProp.true ↔ True := by simp [ωProp.true]

@[simp] theorem false_ne_true : ωProp.false ≠ ωProp.true := by apply ne_of_apply_ne coe; simp
@[simp] theorem true_ne_false : ωProp.true ≠ ωProp.false := by apply ne_of_apply_ne coe; simp

theorem coe_inj {x y : ωProp} : ((x : Prop) ↔ (y : Prop)) ↔ x = y := by
  induction x; induction y; simp

@[elab_as_elim, cases_eliminator]
theorem cases {motive : ωProp → Prop} (false : motive .false) (true : motive .true)
    (t : ωProp) : motive t := by
  induction t with | _ t
  have cases : (∃ n, t n) ∨ ¬(∃ n, t n) := by
    as_aux_lemma => apply Classical.em
  obtain h | h := cases
  · convert true
    simpa [← coe_inj] using h
  · convert false
    simpa [← coe_inj] using h

def any (p : ℕ → ωProp) : ωProp :=
  liftPi (fun f => .mk (Nat.unpaired f)) ?_ p
where finally
  intro f g h
  simp only [mk_eq_mk_iff]
  iterate 2 rw [← Equiv.exists_congr Nat.pairEquiv (fun _ => Iff.rfl)]
  simp [h]

@[simp]
theorem coe_any (p : ℕ → ωProp) : (any p : Prop) ↔ ∃ n, p n := by
  induction p using inductionPi with | _ p
  simp only [any, liftPi_mk, coe_mk, Nat.unpaired]
  rw [← Equiv.exists_congr Nat.pairEquiv (fun _ => Iff.rfl)]
  simp

@[simp]
theorem exists_assoc {α : Sort u} {p : α → Prop} {q : (∃ x, p x) → Prop} :
    (∃ h : ∃ x, p x, q h) ↔ ∃ x h, q ⟨x, h⟩ := by
  constructor
  · rintro ⟨⟨x, h⟩, h'⟩; exact ⟨x, h, h'⟩
  · rintro ⟨x, h, h'⟩; exact ⟨⟨x, h⟩, h'⟩

def bind (p : ωProp) (f : p → ωProp) : ωProp :=
  p.pliftOn
    (fun p h => any fun j =>
      if h' : p j then
        f (by simpa [h] using Exists.intro j h')
      else .false) ?_
where finally
  intro g₁ g₂ h₁ h₂ _
  induction p with | _ p
  rw [← coe_inj]
  simp only [coe_any, apply_dite, coe_false, dite_else_false]
  simp only [mk_eq_mk_iff] at h₁ h₂
  suffices (∃ h : ∃ x, g₁ x, f (h₁.mpr h)) ↔ (∃ h : ∃ x, g₂ x, f (h₂.mpr h)) by simpa
  simp only [← h₁, ← h₂]

@[simp] theorem coe_bind {p : ωProp} {f : p → ωProp} :
    bind p f ↔ ∃ h : p, f h := by
  induction p with | _ p
  simp [bind, apply_dite]

private def rfindAux (dom : ℕ → ℕ → Bool) (p : ∀ n, (∃ k, dom n k) → Bool)
    (fuel : ℕ) (n k : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if h : dom n k then
      if p n ⟨k, h⟩ then
        true
      else
        rfindAux dom p fuel (n + 1) 0
    else
      rfindAux dom p fuel n (k + 1)

private theorem exists_rfindAux {dom : ℕ → ℕ → Bool} {p : ∀ n, (∃ k, dom n k) → Bool} :
    (∃ fuel, rfindAux dom p fuel 0 0) ↔
      ∃ n, (∃ h : (∃ k, dom n k), p n h) ∧ ∀ k < n, (∃ i, dom k i) := by
  constructor
  · intro ⟨fuel, hfuel⟩
    let n := 0; let k := 0
    change rfindAux dom p fuel n k at hfuel
    have hn : ∀ m < n, ∃ k, dom m k := by simp [n]
    clear_value n k
    fun_induction rfindAux with
    | case1 => contradiction
    | case2 n k fuel hk hp => exact ⟨n, ⟨⟨k, hk⟩, hp⟩, hn⟩
    | case3 n k fuel hk hp ih =>
      refine ih hfuel ?_
      intro m hm
      rw [Nat.lt_add_one_iff_lt_or_eq] at hm
      rcases hm with hm | rfl
      · exact hn m hm
      · exact ⟨k, hk⟩
    | case4 n k fuel hk ih => exact ih hfuel hn
  · rintro ⟨n, ⟨⟨k, hk⟩, hp⟩, hn⟩
    let n' := 0; let k' := 0
    change ∃ fuel, rfindAux dom p fuel n' k'
    have hn' : n' ≤ n := Nat.zero_le n
    have hk'₁ (hn' : n' < n) : ∃ m, dom n' m ∧ k' ≤ m := by
      obtain ⟨m, hm⟩ := hn n' hn'
      exact ⟨m, hm, m.zero_le⟩
    have hk'₂ : n' = n → k' ≤ k := fun _ => Nat.zero_le k
    clear_value n' k'
    induction hn' using Nat.geRec generalizing k' with
    | refl =>
      specialize hk'₂ rfl; clear hk'₁
      induction hk'₂ using Nat.geRec with
      | refl => use 1; simp [rfindAux, hk, hp]
      | @step k' hk' ih =>
        obtain ⟨fuel, hfuel⟩ := ih
        use fuel + 1; rw [rfindAux]
        split
        · rfl
        · assumption
    | @step n' hn' ih =>
      specialize ih 0 (fun hn' => ?_) (fun _ => k.zero_le)
      · obtain ⟨m, hm⟩ := hn (n' + 1) hn'
        exact ⟨m, hm, m.zero_le⟩
      obtain ⟨fuel, hfuel⟩ := ih
      obtain ⟨m, hm, hm'⟩ := hk'₁ hn'
      clear hk'₁ hk'₂
      induction hm' using Nat.geRec with
      | refl => use fuel + 1; simp [rfindAux, hm, hfuel]
      | @step k' hk' ih =>
        obtain ⟨fuel', hfuel'⟩ := ih
        by_cases hdom : dom n' k'
        · use fuel + 1; simp [rfindAux, hfuel, hdom]
        · use fuel' + 1; simp [rfindAux, hfuel', hdom]

-- ∃ n, ∃ h : ∀ k ≤ n, dom k, p n (h .rfl) = true
def rfind (dom : ℕ → ωProp) (p : ∀ n, dom n → Bool) : ωProp :=
  pliftOnPi dom (fun dom h => mk fun fuel => rfindAux dom (fun n hn => p n (h ▸ hn)) fuel 0 0) ?_
where finally
  intro g₁ g₂ h₁ h₂ h
  simp [exists_rfindAux, h]

@[simp]
theorem coe_rfind {dom : ℕ → ωProp} {p : ∀ n, dom n → Bool} :
    rfind dom p ↔ ∃ n, (∃ h : dom n, p n h) ∧ ∀ k < n, dom k := by
  induction dom using inductionPi with | _ dom
  simp [rfind, exists_rfindAux]

end ωProp

structure ωPart (α : Sort u) where
  Dom : ωProp
  get : Dom → α

@[coe]
def ωPart.coe (x : ωPart α) : Part α where
  Dom := x.Dom
  get := x.get

instance : Coe (ωPart α) (Part α) where
  coe := ωPart.coe

protected def ωPart.none : ωPart α where
  Dom := .false
  get h := by simp at h

protected def ωPart.some (x : α) : ωPart α where
  Dom := .true
  get _ := x

protected def ωPart.bind (x : ωPart α) (f : α → ωPart β) : ωPart β where
  Dom := .bind x.Dom (fun h => (f (x.get h)).Dom)
  get h := (f (x.get (ωProp.coe_bind.mp h).1)).get (ωProp.coe_bind.mp h).2

protected def ωPart.map (f : α → β) (x : ωPart α) : ωPart β where
  Dom := x.Dom
  get h := f (x.get h)

def ωPart.rfind (p : ℕ → ωPart Bool) : ωPart ℕ where
  Dom := .rfind (fun n => (p n).Dom) (fun n => (p n).get)
  get h := Nat.rfindX (fun n => p n) (by simpa using h)

def ωPart.ofOption (x : Option α) : ωPart α :=
  match x with
  | none => .none
  | some y => .some y

@[simp]
theorem ωPart.coe_mk (Dom : ωProp) (get : Dom → α) :
    (ωPart.mk Dom get : Part α) = Part.mk Dom get := rfl

@[simp]
theorem ωPart.dom_coe (x : ωPart α) : (x : Part α).Dom = x.Dom := rfl

@[simp]
theorem ωPart.get_coe {x : ωPart α} (h : (x : Part α).Dom) :
    (x : Part α).get h = x.get h := rfl

@[simp]
theorem ωPart.coe_none : ((ωPart.none : ωPart α) : Part α) = Part.none := by
  apply Part.ext' <;> simp [ωPart.none]

@[simp]
theorem ωPart.coe_some (x : α) :
    (ωPart.some x : Part α) = Part.some x := by
  apply Part.ext' <;> simp [ωPart.some]

@[simp]
theorem ωPart.coe_bind (x : ωPart α) (f : α → ωPart β) :
    (x.bind f : Part β) = Part.bind x (fun y => f y) := by
  apply Part.ext' <;> simp [ωPart.coe, ωPart.bind, Part.bind, Part.assert]

@[simp]
theorem ωPart.coe_map (x : ωPart α) (f : α → β) :
    (x.map f : Part β) = Part.map f x := by
  apply Part.ext' <;> simp [ωPart.coe, ωPart.map]

@[simp]
theorem ωPart.coe_rfind (p : ℕ → ωPart Bool) :
    (rfind p : Part ℕ) = Nat.rfind (fun n => p n) := by
  apply Part.ext' <;> simp [ωPart.coe, ωPart.rfind, Nat.rfind]

@[simp]
theorem ωPart.coe_ofOption (x : Option α) :
    (ofOption x : Part α) = x := by
  cases x <;> simp [ofOption]
