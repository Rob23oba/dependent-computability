import DependentComputability.NewDecls

def Bare (α : Sort u) := α
def Bare.mk (x : α) : Bare α := x

def _root_.New.Bare : new_type% @Bare.{u} :=
  fun _ _ => .mk (fun _ => PUnit) (TrivialEncoding _) (.trivialEncoding _)

def _root_.New.Bare.mk : new_type% @Bare.mk.{u} :=
  fun _ _ _ _ => ⟨⟩

instance {α : Sort u} {α_extra : new_type% α} : InhabitedExtra (new% Bare α) where
  default _ := ⟨⟩

instance {α : Sort u} {α_extra : new_type% α} : SubsingletonExtra (new% Bare α) where
  subsingleton _ := inferInstanceAs (Subsingleton PUnit)

@[simp]
lemma Bare.eq_iff {α : Sort u} {a b : α} :
    Bare (a = b) ↔ Bare.mk a = Bare.mk b := by rfl

def Bare.translate {α : Sort u} {β : Sort v}
    (f : Bare (α → β)) (a : Bare α) : Bare β := f a

@[simp]
lemma Bare.translate_mk {α : Sort u} {β : Sort v} (f : α → β) (a : α) :
    (Bare.mk f).translate (Bare.mk a) = Bare.mk (f a) := rfl

def _root_.New.Bare.translate.{u, v} : new_type% @Bare.translate.{u, v} := by
  intro α α' β β' f f' a a'; constructor

def Bare.apply {α : Sort u} {β : α → Sort v}
    (f : Bare ((a : α) → β a)) (a : α) : Bare (β a) :=
  (Bare.mk fun x : (a : α) → β a => x a).translate f

def Bare.ofApply {α : Sort u} {β : α → Sort v}
    (f : (a : α) → Bare (β a)) : Bare ((a : α) → β a) := f

@[simp]
lemma Bare.apply_mk {α : Sort u} {β : α → Sort v}
    (f : (a : α) → β a) (a : α) : (Bare.mk f).apply a = Bare.mk (f a) := by
  simp [Bare.apply]

@[simp]
lemma Bare.apply_ofApply {α : Sort u} {β : α → Sort v}
    (f : (a : α) → Bare (β a)) : (Bare.ofApply f).apply = f := rfl

@[simp]
lemma Bare.ofApply_apply {α : Sort u} {β : α → Sort v}
    (f : Bare ((a : α) → (β a))) : Bare.ofApply f.apply = f := rfl

lemma Bare.apply_injective {α : Sort u} {β : α → Sort v} :
    (@Bare.apply α β).Injective := by
  intro x y h
  rw [← ofApply_apply x, ← ofApply_apply y, h]

def _root_.New.Bare.apply.{u, v} : new_type% @Bare.apply.{u, v} := by
  intro α α' β β' f f' a a'; constructor

def _root_.New.Bare.ofApply.{u, v} : new_type% @Bare.ofApply.{u, v} := by
  intro α α' β β' f f'; constructor

class BareSurj (α : Sort u) where
  ofBare : Bare α → α
  mk_ofBare (x : Bare α) : Bare.mk (ofBare x) = x

def Bare.value {α : Sort u} [BareSurj α] (x : Bare α) : α :=
  BareSurj.ofBare x

@[simp]
lemma Bare.mk_value {α : Sort u} [BareSurj α] (x : Bare α) : Bare.mk x.value = x :=
  BareSurj.mk_ofBare x

lemma Bare.mk_surjective {α : Sort u} [BareSurj α] : (Bare.mk (α := α)).Surjective := by
  intro x; use x.value; simp

lemma Bare.value_injective {α : Sort u} [BareSurj α] : (Bare.value (α := α)).Injective := by
  intro x y h
  rw [← Bare.mk_value x, ← Bare.mk_value y, h]

@[simp]
lemma Bare.value_inj {α : Sort u} [BareSurj α] {a b : Bare α} : a.value = b.value ↔ a = b :=
  value_injective.eq_iff

class BareInj (α : Sort u) where
  mk_injective : Function.Injective (@Bare.mk α)

lemma Bare.mk_injective {α : Sort u} [BareInj α] :
    Function.Injective (@Bare.mk α) := BareInj.mk_injective

@[simp]
lemma Bare.mk_inj {α : Sort u} {a b : α} [BareInj α] :
    Bare.mk a = Bare.mk b ↔ a = b := BareInj.mk_injective.eq_iff

@[simp]
lemma Bare.value_mk {α : Sort u} [BareSurj α] [BareInj α] (x : α) :
    (Bare.mk x).value = x := by
  apply Bare.mk_injective; simp

def BareSurj.unsafeIntro : BareSurj α where
  ofBare x := x
  mk_ofBare _ := rfl

def inhabitedExtra_of_bareSurj {α : Sort u} {α' : new_type% α}
    (h : BareSurj α) (h' : new_type% h) : InhabitedExtra α' where
  default x := by
    letI val := @h'.1 (Bare.mk x) ⟨⟩
    haveI : h.1 (Bare.mk x) = x := @h.2 (Bare.mk x)
    exact this ▸ val

def bareSurj_of_inhabitedExtra {α : Sort u} {α' : new_type% α} [InhabitedExtra α'] :
    (new% BareSurj α).1 .unsafeIntro :=
  .mk _ _ (fun x _ => InhabitedExtra.default (show α from x)) (fun _ _ => .refl _)

def BareInj.unsafeIntro : BareInj α where
  mk_injective := Function.injective_id

def subsingletonExtra_of_bareInj {α : Sort u} {α' : new_type% α}
    (h : BareInj α) (h' : new_type% h) : SubsingletonExtra α' where
  subsingleton x := by
    constructor
    intro a b
    cases @h'.1 x a x b rfl (.refl _)
    rfl

def bareInj_of_subsingletonExtra {α : Sort u} {α' : new_type% α} [SubsingletonExtra α'] :
    (new% BareInj α).1 .unsafeIntro :=
  .mk _ _ fun x x' y y' h h' => by cases h; cases Subsingleton.allEq x' y'; constructor

attribute [irreducible] Bare Bare.mk

instance {α : Sort u} [BareInj α] {a b : α} : BareSurj (a = b) where
  ofBare := by simp
  mk_ofBare := by simp

instance {α : Sort u} {β : α → Sort v} [∀ a, BareSurj (β a)] : BareSurj ((a : α) → β a) where
  ofBare f := fun a => (f.apply a).value
  mk_ofBare x := by
    apply Bare.apply_injective
    funext a
    simp

instance {α : Sort u} {β : α → Sort v} [∀ a, BareInj (β a)] : BareInj ((a : α) → β a) where
  mk_injective f g h := by
    funext a
    replace h := congr(($h).apply a)
    simpa using h

instance : CoeFun (Bare (α → β)) (fun _ => Bare α → Bare β) where
  coe := Bare.translate

instance : BareInj (p : Prop) where
  mk_injective _ _ _ := rfl

instance instBareSurjBare : BareSurj (Bare α) := .unsafeIntro
instance instBareInjBare : BareInj (Bare α) := .unsafeIntro

def _root_.New.instBareSurjBare : new_type% @instBareSurjBare.{u} :=
  fun _ _ => bareSurj_of_inhabitedExtra

def _root_.New.instBareInjBare : new_type% @instBareInjBare.{u} :=
  fun _ _ => bareInj_of_subsingletonExtra

instance instBareSurjExists {α : Sort u} {p : α → Prop}
    [BareSurj α] [∀ x, BareSurj (p x)] : BareSurj (Exists p) := .unsafeIntro

instance {α : Sort u} {α' : new_type% α} {β : α → Prop} {β' : new_type% β}
    [InhabitedExtra α'] [∀ x x', InhabitedExtra (@β' x x')] :
    InhabitedExtra (new% Exists β) where
  default h := by
    obtain ⟨x, hx⟩ := h
    exact ⟨InhabitedExtra.default x, InhabitedExtra.default hx⟩

def New.instBareSurjExists : new_type% @instBareSurjExists.{u} := by
  intro α α' p p' hα hα' hp hp'
  have := inhabitedExtra_of_bareSurj hα hα'
  have (a a' : _) := inhabitedExtra_of_bareSurj (hp a) (hp' a')
  exact bareSurj_of_inhabitedExtra

instance {α : Sort u} {α_extra : new_type% α} {r : α → α → Prop} {r_extra : new_type% r}
    [InhabitedExtra α_extra] [∀ a a' b b', InhabitedExtra (@r_extra a a' b b')] :
    InhabitedExtra (new% Quot r) where
  default q := by
    refine q.rec ?_ ?_
    · intro x
      refine Quot.mk _ ?_
      constructor
      exact InhabitedExtra.default x
    · intro a b h
      rw! (castMode := .all) [Quot.sound h]
      apply Quot.sound
      let : new_type% a := InhabitedExtra.default a
      let : new_type% b := InhabitedExtra.default b
      let : new_type% h := InhabitedExtra.default h
      exact .mk (new% a) (new% b) (new% h)

@[elab_as_elim]
lemma Iff.mpr_induction (h : p ↔ q) {motive : p → Prop} (mpr : (hq : q) → motive (h.mpr hq))
    (t : p) : motive t := mpr (h.mp t)

@[elab_as_elim]
lemma Iff.mp_induction (h : p ↔ q) {motive : q → Prop} (mp : (hp : p) → motive (h.mp hp))
    (t : q) : motive t := mp (h.mpr t)

instance {α : Sort u} {α_extra : new_type% α} {r : α → α → Prop} {r_extra : new_type% r}
    [InhabitedExtra α_extra] [SubsingletonExtra α_extra]
    [∀ a a' b b', InhabitedExtra (@r_extra a a' b b')] :
    SubsingletonExtra (new% Quot r) where
  subsingleton q := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    rcases a with @⟨a, a'⟩
    have (eq := q'_eq) q' := Quot.mk r a
    rw! (castMode := .all) [← q'_eq]
    generalize q'_eq ▸ b = b
    rcases b with @⟨b, b'⟩
    let iff : Quot.mk r b = Quot.mk r a ↔ Relation.EqvGen r a b :=
      Iff.intro (Quot.eqvGen_exact ·.symm) (Quot.eqvGen_sound · |>.symm)
    induction q'_eq using Iff.mpr_induction iff with | mpr hr
    subst iff
    clear ‹New.Quot._base _ _› ‹(New.Quot _ _).1 _›
    clear ‹(New.Quot _ _).1 _›
    induction hr with
    | @rel a b h =>
      apply Quot.sound
      let : new_type% h := InhabitedExtra.default h
      exact .mk (new% a) (new% b) (new% h)
    | refl a => cases Subsingleton.allEq a' b'; rfl
    | @symm a b h ih =>
      specialize ih b' a'
      rw! (castMode := .all) [Quot.eqvGen_sound h]
      exact ih.symm
    | @trans a b c h h' ih ih' =>
      rename' b' => c'
      let b' : new_type% b := InhabitedExtra.default b
      specialize ih a' b'
      specialize ih' b' c'
      rw! (castMode := .all) [Quot.eqvGen_sound h'] at ih
      exact ih.trans ih'

instance instBareSurjQuot {α : Sort u} {r : α → α → Prop}
    [BareSurj α] [∀ a b, BareSurj (r a b)] : BareSurj (Quot r) := .unsafeIntro

def New.instBareSurjQuot : new_type% @instBareSurjQuot.{u} := by
  intro α α' p p' hα hα' hr hr'
  have := inhabitedExtra_of_bareSurj hα hα'
  have (a a' b b' : _) := inhabitedExtra_of_bareSurj (hr a b) (hr' a' b')
  exact bareSurj_of_inhabitedExtra

instance instBareInjQuot {α : Sort u} {r : α → α → Prop}
    [BareSurj α] [BareInj α] [∀ a b, BareSurj (r a b)] : BareInj (Quot r) := .unsafeIntro

def New.instBareInjQuot : new_type% @instBareInjQuot.{u} := by
  intro α α' p p' hα hα' hα₂ hα₂' hr hr'
  have := inhabitedExtra_of_bareSurj hα hα'
  have := subsingletonExtra_of_bareInj hα₂ hα₂'
  have (a a' b b' : _) := inhabitedExtra_of_bareSurj (hr a b) (hr' a' b')
  exact bareInj_of_subsingletonExtra

instance : InhabitedExtra New.Bool where
  default := by rintro ⟨⟩ <;> constructor

instance : SubsingletonExtra New.Bool where
  subsingleton _ := by constructor; rintro ⟨⟩ ⟨⟩ <;> rfl

instance : InhabitedExtra New.False where
  default := nofun

instance : InhabitedExtra New.True where
  default _ := by constructor

instance instBareInjBool : BareInj Bool := .unsafeIntro
instance instBareSurjBool : BareSurj Bool := .unsafeIntro
instance instBareInjNat : BareInj Nat := .unsafeIntro
instance instBareSurjNat : BareSurj Nat := .unsafeIntro
instance instBareSurjFalse : BareSurj False := .unsafeIntro
instance instBareSurjTrue : BareSurj True := .unsafeIntro

def _root_.New.instBareInjBool : new_type% instBareInjBool := bareInj_of_subsingletonExtra
def _root_.New.instBareSurjBool : new_type% instBareSurjBool := bareSurj_of_inhabitedExtra
def _root_.New.instBareInjNat : new_type% instBareInjNat := bareInj_of_subsingletonExtra
def _root_.New.instBareSurjNat : new_type% instBareSurjNat := bareSurj_of_inhabitedExtra
def _root_.New.instBareSurjFalse : new_type% instBareSurjFalse := bareSurj_of_inhabitedExtra
def _root_.New.instBareSurjTrue : new_type% instBareSurjTrue := bareSurj_of_inhabitedExtra
