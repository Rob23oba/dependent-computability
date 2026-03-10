import DependentComputability.OmegaPart
import DependentComputability.Bare
import Batteries

#instances Primcodable
#instances Encodable
#instances Denumerable

#print Prop.encodable
open scoped Delab

lemma DPrim.emptyDomain {α : Sort u} {β : α → Sort v}
    {f : (a : α) → β a} [IsEmpty α] : DPrim f := by
  have : f = fun x => (IsEmpty.false x).rec := by
    funext x
    exact (IsEmpty.false x).rec
  rw [this]
  other_dcomp_tac

instance {α : Type u} {α' : new_type% α} [InhabitedExtra α'] :
    InhabitedExtra (new% Part α) where
  default
  | ⟨dom, get⟩ =>
    .mk _ _ (by with_reducible exact InhabitedExtra.default dom)
      (by with_reducible exact InhabitedExtra.default get)

instance {p : Prop} {p' : new_type% p} : InhabitedExtra (new% ¬p) :=
  inferInstanceAs (InhabitedExtra (new% p → False))

convert_to_new ωProp.cases

namespace ωProp

instance instBareSurjCoe {x : ωProp} : BareSurj x.coe where
  ofBare a := by
    induction x with | _ f
    simp only [ωProp.coe_mk] at a ⊢
    exact a.value
  mk_ofBare _ := rfl

noncomputable instance {x : ωProp} {x_extra : new_type% x} : InhabitedExtra (new% x.coe) :=
  inhabitedExtra_of_bareSurj _ (new% @instBareSurjCoe x)

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
    [inst : Encodable α] where
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
    [inst : Encodable α] where
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

theorem dprimrec_iff_natPrimrec (f : ℕ → ℕ) (f_extra : new_type% f) :
    DPrimrec (new% f) ↔ Nat.Primrec f := by
  constructor
  · intro ⟨g, hg, hg'⟩
    have : f = g := funext fun x => @hg' x () x rfl
    subst this
    assumption
  · intro hf
    exact ⟨f, hf, fun | _, _, _, rfl => rfl⟩

axiom New.sorryAx.{u} : new_type% @sorryAx.{u}

def DPart {α : Sort u} {β : α → Type v} (f : (a : α) → Part (β a)) : Prop :=
  ∃ g : (a : α) → ωPart (β a), DComp g ∧ ∀ x, f x = g x

set_option Elab.async false in
set_option linter.unusedVariables false in
set_option backward.dsimp.proofs true in
theorem DPart.of_natPrimrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ f_extra : new_type% f, ∃ h : DPart f, new_type% h := by
  induction hf with
  | zero =>
    exact ⟨new% _, ⟨fun _ => .some 0, by other_dcomp_tac, by simp [pure, PFun.pure]⟩, new% _⟩
  | succ =>
    exact ⟨new% _, ⟨fun n => .some n.succ, by other_dcomp_tac, by simp⟩, new% _⟩
  | left =>
    exact ⟨new% _, ⟨fun n => .some n.unpair.1, by other_dcomp_tac, by simp⟩, new% _⟩
  | right =>
    exact ⟨new% _, ⟨fun n => .some n.unpair.2, by other_dcomp_tac, by simp⟩, new% _⟩
  | @pair f g hf hg fih gih =>
    obtain ⟨f', _, @⟨gf, gf', ⟨hgf₁, hgf₂⟩, ⟨hgf₁', hgf₂'⟩⟩⟩ := fih
    obtain ⟨g', _, @⟨gg, gg', ⟨hgg₁, hgg₂⟩, ⟨hgg₁', hgg₂'⟩⟩⟩ := gih
    dsimp only at hgf₁' hgf₂' hgg₁' hgg₂'
    exact ⟨new% _, ⟨fun n => (gf n).bind fun a => (gg n).map fun b => Nat.pair a b,
      by other_dcomp_tac, by simp [Seq.seq, hgf₂, hgg₂]⟩, new% _⟩
  | @comp f g hf hg fih gih =>
    obtain ⟨f', _, @⟨gf, gf', ⟨hgf₁, hgf₂⟩, ⟨hgf₁', hgf₂'⟩⟩⟩ := fih
    obtain ⟨g', _, @⟨gg, gg', ⟨hgg₁, hgg₂⟩, ⟨hgg₁', hgg₂'⟩⟩⟩ := gih
    dsimp only at hgf₁' hgf₂' hgg₁' hgg₂'
    exact ⟨new% _, ⟨fun n => (gg n).bind fun m => gf m,
      by other_dcomp_tac, by simp [← hgf₂, hgg₂]⟩, new% _⟩
  | @prec f g hf hg fih gih =>
    obtain ⟨f', _, @⟨gf, gf', ⟨hgf₁, hgf₂⟩, ⟨hgf₁', hgf₂'⟩⟩⟩ := fih
    obtain ⟨g', _, @⟨gg, gg', ⟨hgg₁, hgg₂⟩, ⟨hgg₁', hgg₂'⟩⟩⟩ := gih
    dsimp only at hgf₁' hgf₂' hgg₁' hgg₂'
    exact ⟨new% _, ⟨Nat.unpaired fun a n => n.rec (gf a)
      fun y IH => IH.bind fun i => gg (a.pair (y.pair i)), by other_dcomp_tac,
      by simp only [Nat.unpaired, Part.bind_eq_bind]; intro n; induction n.unpair.2 <;> simp_all⟩,
      new% _⟩
  | @rfind f hf ih =>
    obtain ⟨f', _, @⟨g, g', ⟨hg₁, hg₂⟩, ⟨hg₁', hg₂'⟩⟩⟩ := ih
    dsimp only at hg₁' hg₂'
    exact ⟨new% _, ⟨fun a => .rfind fun n => (g (a.pair n)).map fun m => m = 0,
      by other_dcomp_tac, by simp [hg₂]⟩, new% _⟩

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
    have_new hdom : DComp fun _ : Unit => Quotient.countableChoice (fun n => (g n).Dom.val) := by
      other_dcomp_tac
    have_new ex : ∃ g' : ℕ → ℕ → Bool, ∀ n : ℕ, (g n).Dom = ωProp.mk (g' n) := by
      have (n : ℕ) : Nonempty { f : ℕ → Bool // (g n).Dom = ωProp.mk f } := by
        induction (g n).Dom with | _ f; exact ⟨f, rfl⟩
      replace ⟨this⟩ := countableChoice this
      exact ⟨fun i => (this i).1, fun i => (this i).2⟩
    obtain @⟨g', g'_extra, hg', hg'_extra⟩ := ex_extra
    have_new hdom : DComp fun _ : Unit => Quotient.mk _ g' := by
      simpa [hg', ωProp.mk] using hdom
    have_new hdom : DComp fun n : ℕ => (!(g n.unpair.1).Dom.toFun n.unpair.2).toNat := by
      other_dcomp_tac
    have_new hget : DComp fun n : ℕ => (g n).get := by
      other_dcomp_tac
    obtain ⟨fdom, hfdom, hfdom'⟩ := hdom_extra
    obtain ⟨fget, hfget, hfget'⟩ := hget_extra
    replace hfdom := hfdom.rfind
    rw [← Partrec.nat_iff] at hfdom hfget ⊢
    have fdom_eq (n m : ℕ) : fdom (n.pair m) = Part.some (!(g n).Dom.toFun m).toNat := by
      obtain ⟨_, h, rfl⟩ := @hfdom' (n.pair m) () _ rfl
      simpa [Part.eq_some_iff] using h
    have (n m : ℕ) (hm : (g n).Dom.toFun m) :
        ∃ h h', ((ofNat Code ((fget n).get h)).eval 0).get h' = (g n).get ⟨m, hm⟩ := by
      obtain ⟨k, hk, hk'⟩ := @hfget' n () n rfl
      simp only [Part.eq_some_iff.mpr hk, Part.get_some, Part.some_dom, exists_true_left]
      rw [encoding_pi_def not_isProp.{1}] at hk'
      specialize @hk' _ (.intro (w := m) (h := hm) () ?_) 0 .zero
      · with_reducible exact InhabitedExtra.default _
      obtain ⟨_, hi, rfl⟩ := hk'
      simp [Part.eq_some_iff.mpr hi]
    have (n : ℕ) : g n = (Nat.rfind fun m ↦ (· = 0) <$> fdom (Nat.pair n m)).bind
        fun _ => (fget n).bind (fun c => (ofNat Code c).eval 0) := by
      apply Part.ext'
      · suffices ∀ (x : ℕ), (g n).Dom.toFun x = true →
            ∃ h, ((ofNat Code ((fget n).get h)).eval 0).Dom by
          simpa [ωPart.coe, ωProp.coe, fdom_eq]
        intro m hm
        obtain ⟨h, h'⟩ := this n m hm
        exact ⟨h, h'.1⟩
      · intro ⟨m, hm⟩ _
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

def test (x : Nat) : Nat :=
  match x with
  | 0 => 5
  | 1 => 341
  | _ => 21

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
      set_option trace.Meta.synthInstance true in
      exact eq_of_eq_ωPart _ (@hg₂' n n') (inst := instInhabitedExtraDomCoeDomCoe)
    cases this


set_option backward.dsimp.proofs true in
set_option Elab.async false in
theorem dcomputable_iff_natPartrec (f : ℕ → ℕ) (f_extra : new_type% f) :
    DComputable (new% f) ↔ Nat.Partrec f := by
  change _ ↔ Nat.Partrec (fun n => Part.some (f n))
  rw [natPartrec_iff_exists_dpart]
  constructor
  · have hf : DComp f := .unsafeIntro
    intro (hcomp : new_type% hf)
    exact ⟨new% _, ⟨fun n => .some (f n), by other_dcomp_tac, by simp⟩, new% _⟩
  · rintro ⟨f_extra', _, @⟨g, g', ⟨hg₁, hg₂⟩, ⟨hg₁', hg₂'⟩⟩⟩
    dsimp only at hg₁' hg₂'
    have : f_extra' = new% (f : ℕ →. ℕ) := by
      funext n n'; exact (eq_of_eq_ωPart _ (@hg₂' n n') (new% True)
        (inst := instInhabitedExtraTrueTrue) :)
    cases this
    have_new hdom (n : ℕ) : (g n : Part ℕ).Dom := by simp [← hg₂]
    have_new hf : DComp fun n => (g n).get (hdom n) := by other_dcomp_tac
    have_new hf_eq : f = fun n => (g n).get (hdom n) := by
      funext x; simp [← ωPart.get_coe, ← hg₂]
    have_new hf : DComp f := hf_eq ▸ hf
    exact hf_extra

set_option Elab.async false in
@[other_dprim]
lemma Option.map.dprim.{c, u, v} {ctx : Sort c} {α : ctx → Type u} {β : ctx → Type v}
    {f : (c : ctx) → α c → β c} (f_prim : DPrim fun x : PSigma α => f x.1 x.2)
    {x : (c : ctx) → Option (α c)} (x_prim : DPrim x) :
    DPrim (fun c => Option.map (f c) (x c)) := by
  let g := fun x : PSigma α => f x.1 x.2
  have g_prim : DPrim g := f_prim
  have : f = fun a b => g ⟨a, b⟩ := rfl
  delta Option.map Option.getD.match_1 Option.casesOn
  simp only [this]
  other_dcomp_tac

@[other_dprim]
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
  unfold f; other_dcomp_tac

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
      other_dcomp_tac
    exact this_extra
  · have g_prim : DPrim g := .unsafeIntro
    intro (h : new_type% g_prim)
    have_new : DPrim f := by
      have : f = fun x : α =>
          ((Encodable.decode (g (Encodable.encode x)) : Option (Option β)).get
            (by simp [g])).get (by simp [g]) := by simp [g]
      rw [this]
      simp only [Encodable.decode, ← αenc_eq, ← βdec_eq]
      other_dcomp_tac
    exact this_extra

set_option Elab.async false in -- Elab.async doesn't play well with `have_new`
theorem dcomputable_iff_computable {α : Type u} {α_extra : new_type% α}
    {β : Type v} {β_extra : new_type% β} [Primcodable α] [Primcodable β]
    [WeaklyCompatibleEncodingRelation α_extra] [WeaklyCompatibleEncodingRelation β_extra]
    {f : α → β} (f_extra : new_type% f) :
    DComputable f_extra ↔ Computable f := by
  prepare_compatible DComp WeaklyCompatibleEncodingRelation α
  prepare_compatible DComp WeaklyCompatibleEncodingRelation β
  unfold Computable Partrec
  simp [← ωPart.coe_ofOption, ← ωPart.coe_some, ← ωPart.coe_map, ← ωPart.coe_bind]
  let_new g := fun n : ℕ => Encodable.encode (Option.map f (Encodable.decode n))
  change DComputable f_extra ↔ _
  rw [← dprimrec_iff_natPrimrec g g_extra]
  constructor
  · have f_prim : DComp f := .unsafeIntro
    intro (h : new_type% f_prim)
    have_new : DPrim g := by
      simp only [g, Encodable.encode, ← αdec_eq, ← βenc_eq]
      other_dcomp_tac
    exact this_extra
  · have g_prim : DPrim g := .unsafeIntro
    intro (h : new_type% g_prim)
    have_new : DPrim f := by
      have : f = fun x : α =>
          ((Encodable.decode (g (Encodable.encode x)) : Option (Option β)).get
            (by simp [g])).get (by simp [g]) := by simp [g]
      rw [this]
      simp only [Encodable.decode, ← αenc_eq, ← βdec_eq]
      other_dcomp_tac
    exact this_extra

#eval! recAutoDCompMain ``Encodable
#eval! recAutoDCompMain ``some
#eval! recAutoDCompMain ``none
#eval! recAutoDCompMain ``Option.rec

#print New.Encodable._induct
#print Primcodable.empty
#print IsEmpty.toEncodable

instance : CompatibleEncodingRelation (new% Nat) where
  compatible := ⟨new% _, new% .id, new% Option.some.dprim .id⟩

instance : CompatibleEncodingRelation (new% PUnit.{u + 1}) where
  default _ := ⟨⟩
  isRepresentable _ := ⟨0, .zero⟩
  compatible := by
    have_new : DPrim (Encodable.decode (α := PUnit.{u + 1})) := by
      simp only [Encodable.decode]
      other_dcomp_tac
    refine ⟨new% _, new% DPrim.natLit _, this_extra⟩

#synth Encodable PEmpty

instance {α : Type u} {α_extra : new_type% α} [IsEmpty α] :
    CompatibleEncodingRelation (new% α) where
  default

instance : CompatibleEncodingRelation (new% Empty) where
  default := nofun
  isRepresentable := nofun
  compatible := ⟨new% _, new% DPrim.emptyDomain, new% _⟩

instance : CompatibleEncodingRelation (new% Bool) where
  default | true => .true | false => .false
  isRepresentable | .true => ⟨_, .true⟩ | .false => ⟨_, .false⟩
  encode n := 0
  decode n := Nat.pair 0 (n + 1)
  encode_primrec := .succ
  decode_primrec := .pred
  encode_eq | .true => rfl | .false => ⟨_, .false⟩

structure Encoding {α : Sort u} (α_extra : new_type% α) where
  repr : ℕ
  proof : ∃ a a', @α_extra.2 a a' repr

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
