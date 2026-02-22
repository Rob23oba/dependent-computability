import DependentComputability.Tactic.NewDPrimStep
import DependentComputability.Tactic.ConvertToNew
import DependentComputability.Tactic.Delab

convert_to_new Acc

open scoped Delab

open Nat.Partrec Denumerable in
private def selfCallWith (x : ℕ) : Part ℕ :=
  (ofNat Code x.unpair.1).eval x

open Nat.Partrec Denumerable Encodable in
private def thing (selfCallWith : Code) (x : ℕ) : Part ℕ :=
  x.unpaired fun f x => x.unpaired fun x n =>
    (ofNat Code f).eval (Nat.pair n (encode (selfCallWith.curry x)))

open Nat.Partrec Denumerable Encodable in
private def ycomb (thing : Code) (x : ℕ) : Part ℕ :=
  x.unpaired fun f n =>
    (thing.curry f).eval (Nat.pair (encode (thing.curry f)) n)

open Nat.Partrec in
private theorem selfCallWith_part : Nat.Partrec selfCallWith := by
  rw [← Partrec.nat_iff]
  exact Code.eval_part.comp (.comp (.ofNat _) (.comp .fst .unpair)) .id

open Nat.Partrec in
private theorem thing_part (selfCallWith : Code) : Nat.Partrec (thing selfCallWith) := by
  rw [← Partrec.nat_iff]
  refine Code.eval_part.comp (.comp (.ofNat _) (.comp .fst .unpair)) ?_
  have : Computable₂ Nat.pair := by
    refine Primrec.to_comp ?_
    simpa [Primrec] using Nat.Primrec.succ
  refine this.comp ?_ ?_
  · exact .comp .snd (.comp .unpair (.comp .snd .unpair))
  · refine .comp .encode ?_
    refine Code.primrec₂_curry.to_comp.comp (.const _) ?_
    exact .comp .fst (.comp .unpair (.comp .snd .unpair))

open Nat.Partrec in
private theorem ycomb_part (thing : Code) : Nat.Partrec (ycomb thing) := by
  rw [← Partrec.nat_iff]
  have : Computable₂ Nat.pair := by
    refine Primrec.to_comp ?_
    simpa [Primrec] using Nat.Primrec.succ
  refine Code.eval_part.comp ?_ ?_
  · exact Code.primrec₂_curry.to_comp.comp (.const _) (.comp .fst .unpair)
  · refine this.comp ?_ (.comp .snd .unpair)
    refine .comp .encode ?_
    exact Code.primrec₂_curry.to_comp.comp (.const _) (.comp .fst .unpair)

/-open Nat.Partrec (Code) in
theorem dcomputable_reassoc {α : Sort u} {β : α → Sort v} {γ : (a : α) ×' β a → Sort w}
    {δ : (x : (a : α) ×' β a) ×' γ x → Sort w'}
    [EncodingRelation α] [∀ x, EncodingRelation (β x)] [∀ x, EncodingRelation (γ x)]
    [∀ x, EncodingRelation (δ x)]
    (f : (x : (x : (a : α) ×' β a) ×' γ x) → δ x) :
    DComputable f ↔ DComputable fun x : (a : α) ×' (b : β a) ×' γ ⟨a, b⟩ =>
      f ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := by
  constructor
  · intro hf
    refine DComputable.comp hf (DPrimrec.dcomputable ?_)
    dprim_tac
  · intro hf
    refine DComputable.comp
      (g := fun x : (x : (a : α) ×' β a) ×' γ x => ⟨x.1.1, x.1.2, x.2⟩) hf ?_
    refine DPrimrec.dcomputable ?_
    dprim_tac-/

/-open Nat.Partrec Denumerable in
theorem New.Acc.rec.computable.{c, v, u}
    {ctx_base : Sort c}
    {ctx : convert_to_new_type% ctx_base}
    {α_base : ctx_base → Sort u}
    {α : convert_to_new_type% α_base}
    {r_base : (c : ctx_base) → α_base c → α_base c → Prop}
    {r : convert_to_new_type% r_base}
    {motive_base : (c : ctx_base) → (a : α_base c) → _root_.Acc (r_base c) a → Sort v}
    {motive : convert_to_new_type% motive_base}
    {intro_base : (c : ctx_base) → (a : α_base c) →
        (h : ∀ b, r_base c b a → _root_.Acc (r_base c) b) →
      (ih : ∀ b hb, motive_base c b (h b hb)) → motive_base c a (_root_.Acc.intro a h)}
    {intro : convert_to_new_type% intro_base}
    (intro_comp : DComputable (convert_to_new% intro_base))
    {a_base : (c : ctx_base) → α_base c}
    {a : convert_to_new_type% a_base}
    (a_comp : DComputable (convert_to_new% a_base))
    {t_base : (c : ctx_base) → _root_.Acc (r_base c) (a_base c)}
    {t : convert_to_new_type% t_base} :
    DComputable (convert_to_new% fun c => @_root_.Acc.rec
      (α_base c) (r_base c) (motive_base c) (intro_base c) (a_base c) (t_base c)) := by
  by_cases hprop : IsProp.{imax (max (max 1 u) (imax (max 1 u) v)) v}
  · exact .of_isProp @(isProp_of_isProp_imax.{max (max 1 u) (imax (max 1 u) v), v} hprop)
  by_cases hprop : IsProp.{imax (max 1 u) v}
  · exact .of_isProp @(isProp_of_isProp_imax.{max 1 u, v} hprop)
  /-have : DComputable (fun c : ctx =>
      fun x :
        (a : { a : α c // ∀ b, r c b a → Acc (r c) b }) ×'
          (∀ b : { b // r c b a }, motive c b (a.2 b b.2)) =>
          intro c x.1.1 x.1.2 fun b hb => x.2 ⟨b, hb⟩) := by
    simp only [dcomputable_curry, dcomputable_reassoc] at hintro ⊢
    let ty := (c : ctx) ×' (a : { a : α c // ∀ b, r c b a → Acc (r c) b }) ×'
      (∀ b : { b // r c b a }, motive c b (a.2 b b.2))
    refine DComputable.comp
      (g := fun a : ty => ⟨a.1, a.2.1.1, a.2.1.2, fun b hb => a.2.2 ⟨b, hb⟩⟩) hintro ?_
    dprim_tac-/
  obtain ⟨gi, hgi, hgi'⟩ := this
  obtain ⟨ga, hga, hga'⟩ := ha
  obtain ⟨scw, hscw⟩ := Code.exists_code.mp selfCallWith_part
  obtain ⟨th, hth⟩ := Code.exists_code.mp (thing_part scw)
  have hyc := ycomb_part th
  refine ⟨_, .comp hyc (.pair hgi hga), ?_⟩
  intro n b hn
  obtain ⟨na, hna, hna'⟩ := hga' hn
  obtain ⟨ni, hni, hc⟩ := hgi' hn
  let c := Denumerable.ofNat Code ni
  rw [encodes_pi_def] at hc
  clear hga' hgi' hintro
  specialize t b
  have (eq := haeq) a := a b
  dsimp +instances only
  rw! [← haeq] at t hna' ⊢
  simp only [Part.eq_some_iff.mpr hni, Part.map_eq_map, Part.map_some, Part.eq_some_iff.mpr hna,
    seq_eq_bind_map, Part.bind_eq_bind, Part.bind_some]
  change ∃ y ∈ _, EncodingRelation.Encodes y (@Acc.rec (α b) (r b) (motive b) (intro b) a t)
  clear hna haeq
  induction t generalizing na with | intro a ha ih
  have hycomb : ∃ g, (∀ n, (ofNat Code g).eval n = ycomb th (Nat.pair ni n)) ∧
      ycomb th (Nat.pair ni na) = c.eval (Nat.pair na g) := by
    refine ⟨Encodable.encode (scw.curry (Encodable.encode (th.curry ni))), ?_, ?_⟩
    · intro n
      simp [hscw, selfCallWith, ycomb]
    · simp [ycomb, hth, thing, c]
  obtain ⟨g, hg, hg'⟩ := hycomb
  specialize hc (Nat.pair na g)
    ⟨⟨a, ha⟩, fun q => @Acc.rec (α b) (r b) (motive b) (intro b) q.1 (ha q.1 q.2)⟩
  specialize hc ⟨by simpa using hna', ?_⟩
  · simp only [Nat.unpair_pair]
    rw [encodes_pi_def]
    intro x ⟨y, hy⟩ h
    obtain ⟨z, hz, hz'⟩ := ih y hy x h
    simp only [hg]
    use z, hz, hz'
  simpa only [hg', c] using hc-/

example : DComputable (convert_to_new% fun x : Nat => x) := by
  dcomp_tac

attribute [dprim] New.PSigma.fst.computable New.PSigma.snd.computable New.PSigma.mk.computable
  New.PSigma.fst.primrec New.PSigma.snd.primrec New.PSigma.mk.primrec

@[dprim]
theorem New.Unit.unit.computable {ctx_base : Sort u} {ctx : convert_to_new_type% ctx_base} :
    DComputable (convert_to_new% fun _ : ctx_base => ()) := by
  refine .const' (x := convert_to_new% ()) ?_
  exact ⟨0, .zero⟩

example : DComputable (convert_to_new% fun (x : Nat → Nat) y => x y) := by
  dcomp_tac

example : DComputable (convert_to_new% fun (x : Nat → Nat) y => x (x y)) := by
  dcomp_tac

example : DComputable (convert_to_new% fun (x : Nat → (_ : Nat) ×' Nat) y => x (x y).2) := by
  dcomp_tac

@[dprim]
theorem New.Nat.zero.computable {ctx_base : Sort u} {ctx : convert_to_new_type% ctx_base} :
    DComputable (convert_to_new% fun _ : ctx_base => _root_.Nat.zero) := by
  refine .const' (x := convert_to_new% _root_.Nat.zero) ?_
  refine ⟨0, ?_⟩
  rfl

@[dprim]
theorem New.Nat.succ.computable {ctx_base : Sort u} {ctx : convert_to_new_type% ctx_base}
    {f_base : ctx_base → ℕ} {f : convert_to_new_type% f_base}
    (f_comp : DComputable (convert_to_new% f_base)) :
    DComputable (convert_to_new% fun c => _root_.Nat.succ (f_base c)) := by
  refine .comp ?_ (f := convert_to_new% _root_.Nat.succ) f_comp
  refine ⟨_root_.Nat.succ, .succ, ?_⟩
  intro a _ _ rfl
  exact ⟨a + 1, by simp, by rfl⟩

@[dprim]
theorem New.Nat.rec.primrec {ctx_base : Sort u} {ctx : convert_to_new_type% ctx_base}
    {motive_base : ctx_base → ℕ → Sort v} {motive : convert_to_new_type% motive_base}
    {zero_base : (c : ctx_base) → motive_base c .zero}
    {zero : convert_to_new_type% zero_base}
    (zero_comp : DPrimrec (convert_to_new% zero_base))
    {succ_base : (c : ctx_base) → (n : ℕ) → motive_base c n → motive_base c (.succ n)}
    {succ : convert_to_new_type% succ_base}
    (succ_comp : DPrimrec (convert_to_new%
      fun x : (c : ctx_base) ×' (n : ℕ) ×' motive_base c n => succ_base x.1 x.2.1 x.2.2))
    {t_base : ctx_base → ℕ} {t : convert_to_new_type% t_base}
    (t_comp : DPrimrec (convert_to_new% t_base)) :
    DPrimrec (convert_to_new% fun c =>
      @_root_.Nat.rec (motive_base c) (zero_base c) (succ_base c) (t_base c)) := by
  obtain ⟨fz, hfz, hfz'⟩ := zero_comp
  obtain ⟨fs, hfs, hfs'⟩ := succ_comp
  obtain ⟨ft, hft, hft'⟩ := t_comp
  refine ⟨_, .comp (.prec hfz hfs) (.pair .id hft), ?_⟩
  intro c_base c nc hnc
  simp only [Nat.unpaired, id_eq, Nat.unpair_pair]
  specialize hfz' hnc
  specialize hft' hnc
  rw [show t_base c_base = ft nc from hft']
  induction ft nc with
  | zero => exact hfz'
  | succ k ih =>
    specialize @hfs' ⟨c_base, k, _root_.Nat.rec (zero_base c_base) (succ_base c_base) k⟩
    specialize @hfs' ⟨c, (), Nat.rec (motive c) (zero c) (succ c) ()⟩
    exact @hfs' (Nat.pair nc (Nat.pair k _))
      ⟨by simpa using hnc, by simp; rfl, by simpa using ih⟩

convert_to_new Nat.recAux

@[dprim]
theorem New.Nat.rec.computable {ctx_base : Sort u} {ctx : convert_to_new_type% ctx_base}
    {motive_base : ctx_base → ℕ → Sort v} {motive : convert_to_new_type% motive_base}
    {zero_base : (c : ctx_base) → motive_base c .zero}
    {zero : convert_to_new_type% zero_base}
    (zero_comp : DComputable (convert_to_new% zero_base))
    {succ_base : (c : ctx_base) → (n : ℕ) → motive_base c n → motive_base c (.succ n)}
    {succ : convert_to_new_type% succ_base}
    (succ_comp : DComputable (convert_to_new% succ_base))
    {t_base : ctx_base → ℕ} {t : convert_to_new_type% t_base}
    (t_comp : DComputable (convert_to_new% t_base)) :
    DComputable (convert_to_new% fun c =>
      @_root_.Nat.rec (motive_base c) (zero_base c) (succ_base c) (t_base c)) := by
  have := convert_to_new%
    show (fun c => @_root_.Nat.rec (fun n => _root_.Unit → motive_base c n) (fun _ => zero_base c)
          (fun n ih _ => succ_base c n (ih ())) (t_base c) ()) =
        (fun c => @_root_.Nat.rec (motive_base c) (zero_base c) (succ_base c) (t_base c)) by
      funext c; induction t_base c <;> simp_all
  dsimp only at this
  refine Eq._induct.rec (motive := fun a _ _ => DComputable a) ?_ this
  dsimp only
  have recComp : DComputable (convert_to_new% fun x :
      (c : ctx_base) ×' (zero : _root_.Unit → motive_base c 0) ×'
        (succ : (n : ℕ) → (_root_.Unit → motive_base c n) →
          _root_.Unit → motive_base c (n.succ)) ×' ℕ =>
      @_root_.Nat.rec (fun n => _root_.Unit → motive_base x.1 n) x.2.1 x.2.2.1 x.2.2.2) := by
    refine .of_prim ?_
    dcomp_tac
  have mk : DComputable (convert_to_new% fun c : ctx_base =>
      (⟨c, fun _ => zero_base c, fun n ih _ => succ_base c n (ih ()), t_base c⟩ :
        (c : ctx_base) ×' (zero : _root_.Unit → motive_base c 0) ×'
          (succ : (n : ℕ) → (_root_.Unit → motive_base c n) →
            _root_.Unit → motive_base c (n.succ)) ×' ℕ)) := by
    dcomp_tac
  exact .comp (.app recComp Unit.unit.computable) mk
