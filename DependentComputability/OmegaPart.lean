import DependentComputability.Tactic.RecursorModel

-- Credit to Anthony Vandikas for the idea of `ωPart` (YellPika on github)

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

structure ωProp where
  toFun : ℕ → Bool

namespace ωProp

@[coe]
def coe (x : ωProp) : Prop :=
  ∃ y, x.toFun y

instance : CoeSort ωProp Prop where
  coe := ωProp.coe

protected def false : ωProp := .mk fun _ => false
protected def true : ωProp := .mk fun _ => true

@[simp] theorem coe_mk (f : ℕ → Bool) : mk f ↔ ∃ n, f n := by simp [coe]
@[simp] theorem coe_false : ωProp.false ↔ False := by simp [ωProp.false]
@[simp] theorem coe_true : ωProp.true ↔ True := by simp [ωProp.true]

def bind (p : ωProp) (f : p → ωProp) : ωProp where
  toFun n := go n 0
where
  go (fuel : ℕ) (n : ℕ) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if h : p.toFun n then
        (f ⟨n, h⟩).toFun fuel
      else
        go fuel (n + 1)

@[simp] theorem coe_bind {p : ωProp} {f : p → ωProp} :
    bind p f ↔ ∃ h : p, f h := by
  simp only [bind, coe_mk]
  constructor
  · intro ⟨fuel, hfuel⟩
    generalize 0 = n at hfuel
    fun_induction bind.go with
    | case1 => contradiction
    | case2 n fuel hp => exact ⟨⟨n, hp⟩, ⟨fuel, hfuel⟩⟩
    | case3 n fuel hp ih => exact ih hfuel
  · rintro ⟨⟨n, hp⟩, ⟨m, hf⟩⟩
    let +generalize n' := 0
    have hn' : n' ≤ n := n.zero_le
    clear_value n'
    induction hn' using Nat.geRec with
    | refl => use m + 1; simp [bind.go, hp, hf]
    | step n' hn' ih =>
      by_cases hp : p.toFun n'
      · use m + 1; simp [bind.go, hp, hf]
      · obtain ⟨fuel, hfuel⟩ := ih
        use fuel + 1; simp [bind.go, hp, hfuel]

-- ∃ n, ∃ h : ∀ k ≤ n, dom k, p n (h .rfl) = true
def rfind (dom : ℕ → ωProp) (p : ∀ n, dom n → Bool) : ωProp where
  toFun n := go n 0 0
where
  go (fuel : ℕ) (n k : ℕ) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if h : (dom n).toFun k then
        if p n ⟨k, h⟩ then
          true
        else
          go fuel (n + 1) 0
      else
        go fuel n (k + 1)

@[simp] theorem coe_rfind {dom : ℕ → ωProp} {p : ∀ n, dom n → Bool} :
    rfind dom p ↔ ∃ n, (∃ h : dom n, p n h) ∧ ∀ k < n, dom k := by
  simp only [rfind, coe_mk]
  constructor
  · intro ⟨fuel, hfuel⟩
    let n := 0; let k := 0
    change rfind.go dom p fuel n k at hfuel
    have hn : ∀ m < n, dom m := by simp [n]
    clear_value n k
    fun_induction rfind.go with
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
    change ∃ fuel, rfind.go dom p fuel n' k'
    have hn' : n' ≤ n := Nat.zero_le n
    have hk'₁ (hn' : n' < n) : ∃ m, (dom n').toFun m ∧ k' ≤ m := by
      obtain ⟨m, hm⟩ := hn n' hn'
      exact ⟨m, hm, m.zero_le⟩
    have hk'₂ : n' = n → k' ≤ k := fun _ => Nat.zero_le k
    clear_value n' k'
    induction hn' using Nat.geRec generalizing k' with
    | refl =>
      specialize hk'₂ rfl; clear hk'₁
      induction hk'₂ using Nat.geRec with
      | refl => use 1; simp [rfind.go, hk, hp]
      | @step k' hk' ih =>
        obtain ⟨fuel, hfuel⟩ := ih
        use fuel + 1; rw [rfind.go]
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
      | refl => use fuel + 1; simp [rfind.go, hm, hfuel]
      | @step k' hk' ih =>
        obtain ⟨fuel', hfuel'⟩ := ih
        by_cases hdom : (dom n').toFun k'
        · use fuel + 1; simp [rfind.go, hfuel, hdom]
        · use fuel' + 1; simp [rfind.go, hfuel', hdom]

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

protected def ωPart.pure (x : α) : ωPart α where
  Dom := .true
  get _ := x

protected def ωPart.bind (x : ωPart α) (f : α → ωPart β) : ωPart β where
  Dom := .bind x.Dom (fun h => (f (x.get h)).Dom)
  get h := (f (x.get (ωProp.coe_bind.mp h).1)).get (ωProp.coe_bind.mp h).2

def ωPart.rfind (p : ℕ → ωPart Bool) : ωPart ℕ where
  Dom := .rfind (fun n => (p n).Dom) (fun n => (p n).get)
  get h := Nat.rfindX (fun n => p n) (by simpa using h)

@[simp]
theorem ωPart.coe_pure (x : α) :
    (ωPart.pure x : Part α) = Part.some x := by
  apply Part.ext' <;> simp [ωPart.coe, ωPart.pure]

@[simp]
theorem ωPart.coe_bind (x : ωPart α) (f : α → ωPart β) :
    (x.bind f : Part β) = Part.bind x (fun y => f y) := by
  apply Part.ext' <;> simp [ωPart.coe, ωPart.bind, Part.bind, Part.assert]

@[simp]
theorem ωPart.coe_rfind (p : ℕ → ωPart Bool) :
    (rfind p : Part ℕ) = Nat.rfind (fun n => p n) := by
  apply Part.ext' <;> simp [ωPart.coe, ωPart.rfind, Nat.rfind]

set_option Elab.async false in
set_option linter.unusedVariables false in
theorem Nat.Partrec.exists_ωPart_eq {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ g : ℕ → ωPart ℕ, ∃ g' : new_type% g, ∃ h : DComp g, ∃ h' : new_type% h, ∀ n, f n = g n := by
  induction hf with
  | zero =>
    use fun _ => .pure 0, new% _, by other_dcomp_tac, new% _
    simp [pure, PFun.pure]
  | succ =>
    use fun n => .pure (n + 1), new% _, by other_dcomp_tac, new% _
    simp
  | left =>
    use fun n => .pure n.unpair.1, new% _, by other_dcomp_tac, new% _
    simp
  | right =>
    use fun n => .pure n.unpair.2, new% _, by other_dcomp_tac, new% _
    simp
  | @pair f g hf hg fih gih =>
    obtain ⟨gf, gf', hgf, hgf', hgf''⟩ := fih
    obtain ⟨gg, gg', hgg, hgg', hgg''⟩ := gih
    use fun n => (gf n).bind fun a => (gg n).bind fun b => .pure (Nat.pair a b)
    use new% _, by other_dcomp_tac, new% _
    simp [Seq.seq, hgf'', hgg'', Part.bind_some_eq_map]
  | @comp f g hf hg fih gih =>
    obtain ⟨gf, gf', hgf, hgf', hgf''⟩ := fih
    obtain ⟨gg, gg', hgg, hgg', hgg''⟩ := gih
    use fun n => (gg n).bind fun m => gf m
    use new% _, by other_dcomp_tac, new% _
    simp [← hgf'', hgg'']
  | @prec f g hf hg fih gih =>
    obtain ⟨gf, gf', hgf, hgf', hgf''⟩ := fih
    obtain ⟨gg, gg', hgg, hgg', hgg''⟩ := gih
    use (unpaired fun a n => n.rec (gf a) fun y IH => IH.bind fun i => gg (a.pair (y.pair i)))
    use new% _, by other_dcomp_tac, new% _
    intro n
    simp only [unpaired, Part.bind_eq_bind]
    induction (unpair n).2 <;> simp_all
  | @rfind f hf ih =>
    obtain ⟨g, g', hg, hg', hg''⟩ := ih
    use fun a => .rfind fun n => (g (a.pair n)).bind fun m => .pure (m = 0)
    use new% _, by other_dcomp_tac, new% _
    simp [hg'', Part.bind_some_eq_map]
