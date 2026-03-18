import DependentComputability.OmegaPart
import DependentComputability.Bare

open scoped Delab

lemma DPrim.emptyDomain {α : Sort u} {β : α → Sort v}
    {f : (a : α) → β a} [IsEmpty α] : DPrim f := by
  have : f = fun x => (IsEmpty.false x).rec := by
    funext x
    exact (IsEmpty.false x).rec
  rw [this]
  dcomp_tac

instance {α : Type u} {α' : new_type% α} [InhabitedExtra α'] :
    InhabitedExtra (new% Part α) where
  default
  | ⟨dom, get⟩ =>
    .mk _ _ (by with_reducible exact InhabitedExtra.default dom)
      (by with_reducible exact InhabitedExtra.default get)

instance {p : Prop} {p' : new_type% p} : InhabitedExtra (new% ¬p) :=
  inferInstanceAs (InhabitedExtra (new% p → False))

instance {α : Sort u} {α' : new_type% α} : InhabitedExtra (new% IsEmpty α) where
  default h := by
    have : new_type% h.false := by with_reducible exact InhabitedExtra.default h.false
    exact .mk _ _ this

convert_to_new ωProp.cases

namespace ωProp

instance instBareSurjCoe {x : ωProp} : BareSurj x.coe where
  ofBare a := by
    induction x with | _ f
    simp only [ωProp.coe_mk] at a ⊢
    exact a.value
  mk_ofBare _ := rfl

noncomputable instance {x : ωProp} {x_extra : new_type% x} : InhabitedExtra (new% x.coe) :=
  inhabitedExtra_of_bareSurj (new% @instBareSurjCoe x)

end ωProp

instance {α : Type u} {α_extra : new_type% α} {x : ωPart α} {x_extra : new_type% x} :
    InhabitedExtra (new% x.coe.Dom) where
  default y := InhabitedExtra.default (α_extra := new% x.Dom.coe) y

instance : InhabitedExtra (new% ωProp) where
  default x :=
    haveI : InhabitedExtra (new% Quot fun f g : ℕ → Bool ↦ (∃ a, f a) ↔ ∃ a, g a) :=
      inferInstance
    .mk' _ (this.default x.1)

instance : SubsingletonExtra (new% ωProp) where
  subsingleton x := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    dsimp only [Quotient, New.Quotient, New.ωProp.setoid] at a b
    unfold ωProp.setoid at a b
    dsimp only at a b
    haveI : SubsingletonExtra (new% Quot fun f g : ℕ → Bool ↦ (∃ a, f a) ↔ ∃ a, g a) :=
      inferInstance
    cases (this.subsingleton x.1).allEq a b
    rfl

instance {α : Type u} (α_extra : new_type% α) [InhabitedExtra α_extra] :
    InhabitedExtra (new% ωPart α) where
  default x :=
    .mk _ _ (by with_reducible exact InhabitedExtra.default x.1)
      (by with_reducible exact InhabitedExtra.default x.2)

instance {α : Type u} (α_extra : new_type% α) [SubsingletonExtra α_extra] :
    SubsingletonExtra (new% ωPart α) where
  subsingleton x := by
    constructor
    rintro ⟨a, b⟩ ⟨c, d⟩
    cases Subsingleton.allEq a c
    rw [Subsingleton.allEq b d]

instance {α : Type u} (α_extra : new_type% α) [InhabitedExtra α_extra] :
    InhabitedExtra (new% Option α) where
  default | none => .none | some x => .some (InhabitedExtra.default x)

instance {α : Type u} (α_extra : new_type% α) [SubsingletonExtra α_extra] :
    SubsingletonExtra (new% Option α) where
  subsingleton x := by
    constructor
    rintro ⟨⟩ ⟨⟩
    · rfl
    · congr; apply Subsingleton.allEq

instance {α : Type u} (α_extra : new_type% α) [FullyRepresentable α_extra] :
    FullyRepresentable (new% Option α) where
  isRepresentable
    | .none => ⟨_, .none⟩
    | .some x =>
      have ⟨_, h⟩ := FullyRepresentable.isRepresentable x
      ⟨_, .some h⟩

instance {α : Type u} (α_extra : new_type% α) [InhabitedExtra α_extra] [SubsingletonExtra α_extra] :
    InhabitedExtra (new% Encodable α) where
  default x := by
    refine .mk _ _ ?_ ?_ ?_
    · with_reducible exact InhabitedExtra.default _
    · with_reducible exact InhabitedExtra.default _
    · with_reducible exact InhabitedExtra.default _

set_option linter.unusedVariables.funArgs false in
class inductive CompatibleEncodingRelation {α : Type u} (α_extra : new_type% α)
    [inst : Encodable α] : Prop where
  | intro (enc_prim : DPrim (Encodable.encode (α := α)))
    (dec_prim : DPrim (Encodable.decode (α := α)))
    (inst_extra : new_type% inst := by exact new% _)
    (enc_prim_extra :
      haveI : new_type% inst := inst_extra
      new_type% enc_prim := by exact new% _)
    (dec_prim_extra :
      haveI : new_type% inst := inst_extra
      new_type% dec_prim := by exact new% _)

set_option linter.unusedVariables.funArgs false in
class inductive WeaklyCompatibleEncodingRelation {α : Type u} (α_extra : new_type% α)
    [inst : Encodable α] : Prop where
  | intro (enc_comp : DComp (Encodable.encode (α := α)))
    (dec_comp : DComp (Encodable.decode (α := α)))
    (inst_extra : new_type% inst := by exact new% _)
    (enc_comp_extra :
      haveI : new_type% inst := inst_extra
      new_type% enc_comp := by exact new% _)
    (dec_comp_extra :
      haveI : new_type% inst := inst_extra
      new_type% dec_comp := by exact new% _)

instance {α : Type u} {α' : new_type% α} [Encodable α] [CompatibleEncodingRelation α'] :
    WeaklyCompatibleEncodingRelation α' := by
  obtain ⟨enc_prim, dec_prim, _, _, _⟩ := ‹_›
  exact ⟨.of_prim enc_prim, .of_prim dec_prim, new% _, new% _, new% _⟩

lemma dprimrec_iff_natPrimrec (f : ℕ → ℕ) (f_extra : new_type% f) :
    DPrimrec (new% f) ↔ Nat.Primrec f := by
  constructor
  · intro ⟨g, hg, hg'⟩
    have : f = g := funext fun x => @hg' x () x rfl
    subst this
    assumption
  · intro hf
    exact ⟨f, hf, fun | _, _, _, rfl => rfl⟩

def DPart {α : Sort u} {β : α → Type v} (f : (a : α) → Part (β a)) : Prop :=
  ∃ g : (a : α) → ωPart (β a), DComp g ∧ ∀ x, f x = g x

set_option Elab.async false in
set_option linter.unusedVariables false in
set_option backward.dsimp.proofs true in
theorem DPart.of_natPrimrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ f_extra : new_type% f, ∃ h : DPart f, new_type% h := by
  induction hf with
  | zero =>
    exact ⟨new% _, ⟨fun _ => .some 0, by dcomp_tac, by simp [pure, PFun.pure]⟩, new% _⟩
  | succ =>
    exact ⟨new% _, ⟨fun n => .some n.succ, by dcomp_tac, by simp⟩, new% _⟩
  | left =>
    exact ⟨new% _, ⟨fun n => .some n.unpair.1, by dcomp_tac, by simp⟩, new% _⟩
  | right =>
    exact ⟨new% _, ⟨fun n => .some n.unpair.2, by dcomp_tac, by simp⟩, new% _⟩
  | @pair f g hf hg fih gih =>
    obtain ⟨f', _, @⟨gf, gf', ⟨hgf₁, hgf₂⟩, ⟨hgf₁', hgf₂'⟩⟩⟩ := fih
    obtain ⟨g', _, @⟨gg, gg', ⟨hgg₁, hgg₂⟩, ⟨hgg₁', hgg₂'⟩⟩⟩ := gih
    dsimp only at hgf₁' hgf₂' hgg₁' hgg₂'
    exact ⟨new% _, ⟨fun n => (gf n).bind fun a => (gg n).map fun b => Nat.pair a b,
      by dcomp_tac, by simp [Seq.seq, hgf₂, hgg₂]⟩, new% _⟩
  | @comp f g hf hg fih gih =>
    obtain ⟨f', _, @⟨gf, gf', ⟨hgf₁, hgf₂⟩, ⟨hgf₁', hgf₂'⟩⟩⟩ := fih
    obtain ⟨g', _, @⟨gg, gg', ⟨hgg₁, hgg₂⟩, ⟨hgg₁', hgg₂'⟩⟩⟩ := gih
    dsimp only at hgf₁' hgf₂' hgg₁' hgg₂'
    exact ⟨new% _, ⟨fun n => (gg n).bind fun m => gf m,
      by dcomp_tac, by simp [← hgf₂, hgg₂]⟩, new% _⟩
  | @prec f g hf hg fih gih =>
    obtain ⟨f', _, @⟨gf, gf', ⟨hgf₁, hgf₂⟩, ⟨hgf₁', hgf₂'⟩⟩⟩ := fih
    obtain ⟨g', _, @⟨gg, gg', ⟨hgg₁, hgg₂⟩, ⟨hgg₁', hgg₂'⟩⟩⟩ := gih
    dsimp only at hgf₁' hgf₂' hgg₁' hgg₂'
    exact ⟨new% _, ⟨Nat.unpaired fun a n => n.rec (gf a)
      fun y IH => IH.bind fun i => gg (a.pair (y.pair i)), by dcomp_tac,
      by simp only [Nat.unpaired, Part.bind_eq_bind]; intro n; induction n.unpair.2 <;> simp_all⟩,
      new% _⟩
  | @rfind f hf ih =>
    obtain ⟨f', _, @⟨g, g', ⟨hg₁, hg₂⟩, ⟨hg₁', hg₂'⟩⟩⟩ := ih
    dsimp only at hg₁' hg₂'
    exact ⟨new% _, ⟨fun a => .rfind fun n => (g (a.pair n)).map fun m => m = 0,
      by dcomp_tac, by simp [hg₂]⟩, new% _⟩

set_option backward.dsimp.proofs true in
set_option Elab.async false in
set_option linter.unusedVariables false in
open Nat.Partrec (Code) in
open Denumerable (ofNat) in
theorem natPartrec_iff_exists_dpart (f : ℕ →. ℕ) :
    Nat.Partrec f ↔ ∃ f_extra : new_type% f, ∃ h' : DPart f, new_type% h' := by
  constructor
  · intro h
    exact DPart.of_natPrimrec h
  · rintro ⟨f_extra, _, @⟨g, g', ⟨hg₁, hg₂⟩, ⟨hg₁', hg₂'⟩⟩⟩
    dsimp only at hg₁' hg₂' g g'
    have_new f_eq := (funext hg₂).symm
    conv at f_eq_extra => whnf
    dsimp only [PFun, New.PFun] at f f_extra
    with_reducible cases f_eq_extra
    clear hg₂ hg₂'
    have_new (eq := g'_eq) g' :=
      Quotient.countableChoice (fun n => (g n).Dom.val)
    have_new hdom : DComp fun _ : Unit => g' := by
      rw [g'_eq]; dcomp_tac
    have_new hget : DComp fun n : ℕ => (g n).get := by
      dcomp_tac
    obtain ⟨fdom, hfdom, hfdom'⟩ := hdom_extra
    obtain ⟨fget, hfget, hfget'⟩ := hget_extra
    obtain ⟨ndom, hndom₁, hndom⟩ := @hfdom' () () 0 .zero
    clear hfdom hfdom' hndom₁ fdom hdom
    rcases hndom with @⟨f, f', _, hf'⟩
    have hf : DComp f := .unsafeIntro
    have hf_extra : new_type% hf :=
      (isRepresentable_function_iff (new% f)).mp ⟨ndom, hf'⟩
    have_new hdom : DComp fun x : Nat => (!f x.unpair.1 x.unpair.2).toNat := by
      dcomp_tac
    obtain ⟨fdom, hfdom, hfdom'⟩ := hdom_extra
    replace hfdom := hfdom.rfind
    rw [← Partrec.nat_iff] at hfdom hfget ⊢
    have fdom_eq (n m : ℕ) : fdom (n.pair m) = Part.some (!f n m).toNat := by
      obtain ⟨_, h, rfl⟩ := @hfdom' (n.pair m) () _ rfl
      simpa [Part.eq_some_iff] using h
    have_new dom_g (n : ℕ) : (g n).Dom = .mk (f n) := by
      change Quotient.mk _ f = _ at g'_eq
      replace g'_eq := congr(($g'_eq.symm).eval n)
      simp only [Quotient.eval_countableChoice, Quotient.eval_mk] at g'_eq
      exact congrArg ωProp.mk' g'_eq
    clear g'_eq g'_eq_extra
    have (n m : ℕ) (hm : f n m) :
        ∃ h h', ((ofNat Code ((fget n).get h)).eval 0).get h' =
          (g n).get (dom_g n ▸ ⟨m, hm⟩) := by
      obtain ⟨k, hk, hk'⟩ := @hfget' n () n rfl
      simp only [Part.eq_some_iff.mpr hk, Part.get_some, Part.some_dom, exists_true_left]
      rw [encoding_pi_def not_isProp.{1}] at hk'
      let : new_type% n := ()
      let : new_type% m := ()
      let : new_type% hm := by
        with_reducible exact InhabitedExtra.default _
      have_new dom_g : (g n).Dom := dom_g n ▸ ⟨m, hm⟩
      specialize @hk' _ _ 0 (RecursorModel.encodes_proof dom_g_extra)
      obtain ⟨_, hi, rfl⟩ := hk'
      simp [Part.eq_some_iff.mpr hi]
    have (n : ℕ) : g n = (Nat.rfind fun m ↦ (· = 0) <$> fdom (Nat.pair n m)).bind
        fun _ => (fget n).bind (fun c => (ofNat Code c).eval 0) := by
      apply Part.ext'
      · suffices ∀ (x : ℕ), f n x = true →
            ∃ h, ((ofNat Code ((fget n).get h)).eval 0).Dom by
          simpa [ωPart.coe, fdom_eq, dom_g]
        intro m hm
        obtain ⟨h, h'⟩ := this n m hm
        exact ⟨h, h'.1⟩
      · intro (hdom : (g n).Dom) _
        obtain ⟨m, hm⟩ := dom_g n ▸ hdom
        simp [Part.bind, Part.assert, (this n m hm).2.2, ωPart.coe]
    simp only [this]
    exact .bind hfdom (.bind (hfget.comp .fst)
      (Code.eval_part.comp (.comp (.ofNat Code) .snd) (.const 0)))

theorem newEq_comm {α : Sort u} {α_extra : new_type% α} {a : α}
    {a_extra : new_type% a} {b : α} {b_extra : new_type% b} (h : a = b) :
    (@New.Eq α α_extra a a_extra b b_extra).1 h ↔
      (@New.Eq α α_extra b b_extra a a_extra).1 h.symm := by
  subst h; constructor <;> rintro ⟨⟩ <;> constructor

theorem newEq_iff_eq {α : Sort u} {α_extra : new_type% α} {a : α}
    {a_extra : new_type% a} {b : α} {b_extra : new_type% b} (h : a = b) :
    (@New.Eq α α_extra a a_extra b b_extra).1 h ↔ h ▸ a_extra = b_extra := by
  subst h; constructor <;> rintro ⟨⟩ <;> constructor

set_option Elab.async false in
theorem eq_of_iff_ωProp {p : Prop} {p' : new_type% p}
    {q : ωProp} {q' : new_type% q} (h : p ↔ q) (h' : new_type% h)
    (p'₂ : new_type% p) [inst : InhabitedExtra p'₂] :
    p' = p'₂ := by
  have h_extra := New.propext p' _ h'
  conv at h_extra => whnf
  with_reducible cases h_extra
  apply (newEq_iff_eq (α_extra := new% Prop) rfl).mp
  refine @New.propext _ _ _ _ h ?_
  constructor
  · intro h₁ h₂
    with_reducible exact InhabitedExtra.default h₁
  · intro h₁ h₂
    with_reducible exact InhabitedExtra.default h₁

theorem eq_of_eq_ωPart {α : Type u} {α_extra : new_type% α} {p : Part α} {p' : new_type% p}
    {q : ωPart α} {q' : new_type% q} (h : p = q) (h' : new_type% h)
    (p'₂ : new_type% p.Dom) [inst : InhabitedExtra p'₂] :
    p' = .mk _ _ p'₂
      (fun {a a'} =>
        haveI iff : p.Dom ↔ q.Dom := by rw [h]; rfl
        haveI iff_extra : new_type% iff := new% by rw [h]; rfl
        p'.2 (eq_of_iff_ωProp _ (new% iff) p'₂ ▸ a' :)) := by
  have_new iff : p.Dom ↔ q.Dom := by rw [h]; rfl
  have eq := eq_of_iff_ωProp _ (new% iff) p'₂
  rcases p' with ⟨dom, get⟩
  cases eq
  rfl

set_option Elab.async false in
theorem natPartrec_ωPart_iff_dcomputable (f : ℕ → ωPart ℕ) (f_extra : new_type% f) :
    DComputable (new% f) ↔ Nat.Partrec (fun n => f n) := by
  rw [natPartrec_iff_exists_dpart]
  constructor
  · have hf : DComp f := .unsafeIntro
    intro (hcomp : new_type% hf)
    exact ⟨new% _, ⟨f, hf, fun _ => rfl⟩, new% _⟩
  · rintro ⟨f_extra', _, @⟨g, g', ⟨hg₁, hg₂⟩, ⟨hg₁', hg₂'⟩⟩⟩
    have : f_extra' = new% (fun n => f n : ℕ →. ℕ) := by
      funext n n'
      exact eq_of_eq_ωPart _ (@hg₂' n n') (inst := instInhabitedExtraDomCoeDomCoe)
    cases this
    change new_type% hg₁ at hg₁'
    change new_type% hg₂ at hg₂'
    have_new hg₂ : f = g := by
      funext n
      simpa only [ωPart.coe_inj] using hg₂ n
    conv at hg₂_extra => whnf
    with_reducible cases hg₂_extra
    exact hg₁'

set_option backward.dsimp.proofs true in
set_option Elab.async false in
theorem dcomputable_iff_natPartrec (f : ℕ → ℕ) (f_extra : new_type% f) :
    DComputable (new% f) ↔ Nat.Partrec f := by
  change _ ↔ Nat.Partrec (fun n => Part.some (f n))
  rw [natPartrec_iff_exists_dpart]
  constructor
  · have hf : DComp f := .unsafeIntro
    intro (hcomp : new_type% hf)
    exact ⟨new% _, ⟨fun n => .some (f n), by dcomp_tac, by simp⟩, new% _⟩
  · rintro ⟨f_extra', _, @⟨g, g', ⟨hg₁, hg₂⟩, ⟨hg₁', hg₂'⟩⟩⟩
    dsimp only at hg₁' hg₂'
    have : f_extra' = new% (f : ℕ →. ℕ) := by
      funext n n'; exact (eq_of_eq_ωPart _ (@hg₂' n n') (new% True)
        (inst := instInhabitedExtraTrueTrue) :)
    cases this
    have_new hdom (n : ℕ) : (g n : Part ℕ).Dom := by simp [← hg₂]
    have_new hf : DComp fun n => (g n).get (hdom n) := by dcomp_tac
    have_new hf_eq : f = fun n => (g n).get (hdom n) := by
      funext x; simp [← ωPart.get_coe, ← hg₂]
    have_new hf : DComp f := hf_eq ▸ hf
    exact hf_extra

set_option Elab.async false in
@[dcomp]
lemma Option.map.dprim.{c, u, v} {ctx : Sort c} {α : ctx → Type u} {β : ctx → Type v}
    {f : (c : ctx) → α c → β c} (f_prim : DPrim fun x : PSigma α => f x.1 x.2)
    {x : (c : ctx) → Option (α c)} (x_prim : DPrim x) :
    DPrim (fun c => Option.map (f c) (x c)) := by
  let g := fun x : PSigma α => f x.1 x.2
  have g_prim : DPrim g := f_prim
  have : f = fun a b => g ⟨a, b⟩ := rfl
  delta Option.map Option.getD.match_1 Option.casesOn
  simp only [this]
  dcomp_tac

@[dcomp]
lemma Option.get.dprim.{c, u} {ctx : Sort c} {α : ctx → Type u}
    {x : (c : ctx) → Option (α c)} (x_prim : DPrim x)
    {h : (c : ctx) → (x c).isSome} :
    DPrim (fun c => Option.get (x c) (h c)) := by
  let f (c : ctx) : (x c).rec PUnit (fun _ => α c) := (x c).rec PUnit.unit fun x => x
  have β_eq (c : ctx) : (x c).rec PUnit (fun _ => α c) = α c := by
    specialize h c; generalize x c = x at h
    cases x <;> trivial
  have eq (c : ctx) : Option.get (x c) (h c) = β_eq c ▸ f c := by
    generalize β_eq c = β_eq; generalize h c = h
    unfold f; generalize x c = x at β_eq h f
    cases x <;> trivial
  rw [funext eq]
  unfold f; dcomp_tac

local macro "prepare_compatible " pred:ident inst:ident ty:ident : tactic => do
  let ty_extra := Lean.mkIdent (ty.getId.appendAfter "_extra")
  let tyenc := Lean.mkIdent (ty.getId.appendAfter "enc")
  let tydec := Lean.mkIdent (ty.getId.appendAfter "dec")
  let tyenc_eq := Lean.mkIdent (tyenc.getId.appendAfter "_eq")
  let tydec_eq := Lean.mkIdent (tydec.getId.appendAfter "_eq")
  let htyenc := Lean.mkIdent (tyenc.getId.appendBefore "h")
  let htydec := Lean.mkIdent (tydec.getId.appendBefore "h")
  `(tactic|
     (letI : Encodable $ty := inferInstance
      obtain ⟨$htyenc, $htydec, (_ : new_type% this), _, _⟩ := ‹$inst $ty_extra›
      let_new (eq := $tyenc_eq) $tyenc := Encodable.encode (α := $ty)
      let_new (eq := $tydec_eq) $tydec := Encodable.decode (α := $ty)
      change $pred $tyenc at $htyenc:ident
      change $pred $tydec at $htydec:ident))

set_option Elab.async false in -- Elab.async doesn't play well with `have_new`
theorem dprimrec_iff_primrec {α : Type u} {α_extra : new_type% α}
    {β : Type v} {β_extra : new_type% β} [Primcodable α] [Primcodable β]
    [CompatibleEncodingRelation α_extra] [CompatibleEncodingRelation β_extra]
    {f : α → β} (f_extra : new_type% f) :
    DPrimrec f_extra ↔ Primrec f := by
  prepare_compatible DPrim CompatibleEncodingRelation α
  prepare_compatible DPrim CompatibleEncodingRelation β
  unfold Primrec
  let_new g := fun n : ℕ => Encodable.encode (Option.map f (Encodable.decode n))
  change DPrimrec f_extra ↔ Nat.Primrec g
  rw [← dprimrec_iff_natPrimrec g g_extra]
  constructor
  · have f_prim : DPrim f := .unsafeIntro
    intro (h : new_type% f_prim)
    have_new : DPrim g := by
      simp only [g, Encodable.encode, ← αdec_eq, ← βenc_eq]
      dcomp_tac
    exact this_extra
  · have g_prim : DPrim g := .unsafeIntro
    intro (h : new_type% g_prim)
    have_new : DPrim f := by
      have : f = fun x : α =>
          ((Encodable.decode (g (Encodable.encode x)) : Option (Option β)).get
            (by simp [g])).get (by simp [g]) := by simp [g]
      rw [this]
      simp only [Encodable.decode, ← αenc_eq, ← βdec_eq]
      dcomp_tac
    exact this_extra

alias ⟨DPrimrec.primrec, _⟩ := dprimrec_iff_primrec

set_option Elab.async false in -- Elab.async doesn't play well with `have_new`
theorem dcomputable_iff_computable {α : Type u} {α_extra : new_type% α}
    {β : Type v} {β_extra : new_type% β} [Primcodable α] [Primcodable β]
    [WeaklyCompatibleEncodingRelation α_extra] [WeaklyCompatibleEncodingRelation β_extra]
    {f : α → β} (f_extra : new_type% f) :
    DComputable f_extra ↔ Computable f := by
  prepare_compatible DComp WeaklyCompatibleEncodingRelation α
  prepare_compatible DComp WeaklyCompatibleEncodingRelation β
  unfold Computable Partrec
  simp only [← ωPart.coe_ofOption, PFun.coe_val, ← ωPart.coe_some, ← ωPart.coe_map,
    ← ωPart.coe_bind]
  let_new g := fun n : ℕ =>
    (ωPart.ofOption (Encodable.decode n)).bind
      fun y ↦ ωPart.map Encodable.encode (ωPart.some (f y))
  change DComputable f_extra ↔ _
  rw [← natPartrec_ωPart_iff_dcomputable _ (new% g)]
  constructor
  · have f_comp : DComp f := .unsafeIntro
    intro (h : new_type% f_comp)
    have_new : DComp g := by
      simp only [g, ← αdec_eq, ← βenc_eq]
      dcomp_tac
    exact this_extra
  · have g_comp : DComp g := .unsafeIntro
    intro (h : new_type% g_comp)
    have_new : DComp f := by
      have : f = fun x : α =>
        (Encodable.decode ((g (Encodable.encode x)).get (by simp [g])) : Option β).get
          (by simp [g]) := by simp [g]
      rw [this]
      simp only [← αenc_eq, ← βdec_eq]
      dcomp_tac
    exact this_extra

alias ⟨DComputable.computable, _⟩ := dcomputable_iff_computable

instance : CompatibleEncodingRelation (new% Nat) :=
  ⟨.id, Option.some.dprim .id, new% _, new% _, new% _⟩

instance : CompatibleEncodingRelation (new% PUnit.{u + 1}) :=
  ⟨.natLit 0, by simp only [Encodable.decode]; dcomp_tac, new% _, new% _, new% _⟩

instance {α : Type u} {α_extra : new_type% α} [inst : IsEmpty α] :
    CompatibleEncodingRelation (new% α) :=
  haveI : new_type% inst := by with_reducible exact InhabitedExtra.default inst
  ⟨.emptyDomain, Option.none.dprim, new% _, new% _, new% _⟩
