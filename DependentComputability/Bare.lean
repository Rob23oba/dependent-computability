import DependentComputability.NewDecls

def Bare (α : Sort u) := α
def Bare.mk {α : Sort u} (a : α) : Bare α := a

def _root_.New.Bare : new_type% @Bare.{u} :=
  fun _ _ => .mk (fun _ => PUnit) (TrivialEncoding _) (.trivialEncoding _)

def New.Bare.mk : new_type% @Bare.mk.{u} :=
  fun _ _ _ _ => ⟨⟩

class BareSurj (α : Sort u) where
  ofBare : Bare α → α
  mk_ofBare (x : Bare α) : Bare.mk (ofBare x) = x

def Bare.value [BareSurj α] (x : Bare α) : α := BareSurj.ofBare x

@[simp]
lemma Bare.mk_value [BareSurj α] (x : Bare α) : mk x.value = x :=
  BareSurj.mk_ofBare x

lemma Bare.mk_surjective [BareSurj α] : (mk (α := α)).Surjective := by
  intro x; use x.value; exact x.mk_value

lemma Bare.value_injective [BareSurj α] : (value (α := α)).Injective := by
  intro x y h
  rw [← mk_value x, ← mk_value y, h]

@[simp]
lemma Bare.value_inj [BareSurj α] {x y : Bare α} :
    x.value = y.value ↔ x = y := value_injective.eq_iff

class BareInj (α : Sort u) where
  mk_injective : (Bare.mk (α := α)).Injective

lemma Bare.mk_injective [BareInj α] : (mk (α := α)).Injective :=
  BareInj.mk_injective

@[simp]
lemma Bare.mk_inj [BareInj α] {x y : α} : mk x = mk y ↔ x = y :=
  mk_injective.eq_iff

@[simp]
lemma Bare.value_mk [BareSurj α] [BareInj α] (x : α) : (mk x).value = x := by
  apply mk_injective; simp

def BareSurj.unsafeIntro : BareSurj α where
  ofBare x := x
  mk_ofBare _ := rfl

def BareInj.unsafeIntro : BareInj α where
  mk_injective := Function.injective_id

def bareSurj_of_inhabitedExtra [@InhabitedExtra α α'] :
    (new% BareSurj α).1 .unsafeIntro :=
  .mk _ _ (fun _ _ => InhabitedExtra.default _) (fun _ _ => .refl _)

@[implicit_reducible]
def inhabitedExtra_of_bareSurj {α : Sort u} {α' : new_type% α}
    {h : BareSurj α} (h' : new_type% h) : InhabitedExtra α' where
  default x := h.2 x ▸ @h'.1 x ⟨⟩

lemma bareInj_of_subsingletonExtra [@SubsingletonExtra α α'] :
    (new% BareInj α).1 .unsafeIntro := by
  constructor
  intro a a' b b' h h'
  cases h
  cases Subsingleton.allEq a' b'
  constructor

lemma subsingletonExtra_of_bareInj {α : Sort u} {α' : new_type% α}
    {h : BareInj α} (h' : new_type% h) : SubsingletonExtra α' where
  subsingleton x := {
    allEq a b := by
      cases @h'.1 x a x b rfl (.refl _)
      rfl
  }

@[simp]
lemma Bare.eq_iff : Bare (a = b) ↔ Bare.mk a = Bare.mk b := Iff.rfl

instance {α : Sort u} {α' : new_type% α} : InhabitedExtra (new% Bare α) where
  default _ := ⟨⟩

instance {α : Sort u} {α' : new_type% α} : SubsingletonExtra (new% Bare α) where
  subsingleton _ := inferInstanceAs (Subsingleton PUnit)

instance {a b : α} [BareInj α] : BareSurj (a = b) where
  ofBare := by simp
  mk_ofBare _ := rfl

instance : InhabitedExtra (new% PUnit.{u}) where
  default _ := ⟨⟩

instance : SubsingletonExtra (new% PUnit.{u}) where
  subsingleton _ := inferInstanceAs (Subsingleton PUnit)

instance : InhabitedExtra (new% Bool) where
  default := by rintro ⟨⟩ <;> constructor

instance : SubsingletonExtra (new% Bool) where
  subsingleton _ := by constructor; rintro ⟨⟩ ⟨⟩ <;> constructor

instance : InhabitedExtra (new% Nat) where
  default _ := ⟨⟩

instance : SubsingletonExtra (new% Nat) where
  subsingleton _ := by constructor; intros; rfl

instance : InhabitedExtra (new% True) where
  default := by rintro ⟨⟩; constructor

instance : InhabitedExtra (new% False) where
  default := nofun

instance instBareSurjPUnit : BareSurj PUnit := .unsafeIntro
instance instBareInjPUnit : BareInj PUnit := .unsafeIntro
instance instBareSurjBool : BareSurj Bool := .unsafeIntro
instance instBareInjBool : BareInj Bool := .unsafeIntro
instance instBareSurjNat : BareSurj Nat := .unsafeIntro
instance instBareInjNat : BareInj Nat := .unsafeIntro
instance instBareSurjTrue : BareSurj True := .unsafeIntro
instance instBareSurjFalse : BareSurj False := .unsafeIntro

def New.instBareSurjPUnit : new_type% @instBareSurjPUnit.{u} := bareSurj_of_inhabitedExtra
def New.instBareInjPUnit : new_type% @instBareInjPUnit.{u} := bareInj_of_subsingletonExtra
def New.instBareSurjBool : new_type% @instBareSurjBool := bareSurj_of_inhabitedExtra
def New.instBareInjBool : new_type% @instBareInjBool := bareInj_of_subsingletonExtra
def New.instBareSurjNat : new_type% @instBareSurjNat := bareSurj_of_inhabitedExtra
def New.instBareInjNat : new_type% @instBareInjNat := bareInj_of_subsingletonExtra
def New.instBareSurjTrue : new_type% @instBareSurjTrue := bareSurj_of_inhabitedExtra
def New.instBareSurjFalse : new_type% @instBareSurjFalse := bareSurj_of_inhabitedExtra

instance {α : Sort u} {α' : new_type% α} {p : α → Prop} {p' : new_type% p}
    [InhabitedExtra α'] [∀ a a', InhabitedExtra (@p' a a')] :
    InhabitedExtra (new% Exists p) where
  default | ⟨x, h⟩ => ⟨InhabitedExtra.default x, InhabitedExtra.default h⟩

instance instBareSurjExists {α : Sort u} {p : α → Prop} [BareSurj α]
    [∀ a, BareSurj (p a)] : BareSurj (Exists p) := .unsafeIntro

def New.instBareSurjExists : new_type% @instBareSurjExists.{u} :=
  fun _ _ _ _ _ hα' _ hp' =>
    let := inhabitedExtra_of_bareSurj hα'
    let (a a' : _) := inhabitedExtra_of_bareSurj (@hp' a a')
    bareSurj_of_inhabitedExtra

instance {α : Sort u} {α' : new_type% α} {r : α → α → Prop} {r' : new_type% r}
    [InhabitedExtra α'] [∀ a a' b b', InhabitedExtra (@r' a a' b b')] :
    InhabitedExtra (new% Quot r) where
  default x := by
    refine x.rec ?_ ?_
    · intro x
      refine Quot.mk _ ?_
      constructor
      exact InhabitedExtra.default x
    · intro a b h
      rw! (castMode := .all) [Quot.sound h]
      apply Quot.sound
      let : new_type% a := InhabitedExtra.default _
      let : new_type% b := InhabitedExtra.default _
      let : new_type% h := InhabitedExtra.default _
      exact .mk (new% a) (new% b) (new% h)

instance {α : Sort u} {α' : new_type% α} {r : α → α → Prop} {r' : new_type% r}
    [InhabitedExtra α'] [SubsingletonExtra α'] [∀ a a' b b', InhabitedExtra (@r' a a' b b')] :
    SubsingletonExtra (new% Quot r) where
  subsingleton x := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    have := 0
    clear ‹new_type% x›
    clear ‹new_type% x›
    rcases a with @⟨a, a'⟩
    have (eq := q_eq) q := Quot.mk r a
    revert b
    rw! (castMode := .all) [← q_eq]
    rintro @⟨b, b'⟩
    revert q_eq
    rw! [eq_comm, Iff.intro Quot.eqvGen_exact Quot.eqvGen_sound]
    intro q_eq
    induction q_eq with
    | rel a b h =>
      apply Quot.sound
      have : new_type% h := InhabitedExtra.default h
      exact .mk (new% a) (new% b) (new% h)
    | refl a => cases Subsingleton.allEq a' b'; rfl
    | symm a b h ih =>
      specialize ih b' a'
      rw! (castMode := .all) [Quot.eqvGen_sound h]
      exact ih.symm
    | trans a b c h h' ih ih' =>
      rename' b' => c'
      let b' : new_type% b := InhabitedExtra.default b
      specialize ih a' b'
      specialize ih' b' c'
      rw! (castMode := .all) [Quot.eqvGen_sound h'] at ih
      exact ih.trans ih'

instance instBareSurjQuot {α : Sort u} {r : α → α → Prop} [BareSurj α]
    [∀ a b, BareSurj (r a b)] : BareSurj (Quot r) := .unsafeIntro

instance instBareInjQuot {α : Sort u} {r : α → α → Prop} [BareSurj α] [BareInj α]
    [∀ a b, BareSurj (r a b)] : BareInj (Quot r) := .unsafeIntro

def New.instBareSurjQuot : new_type% @instBareSurjQuot.{u} :=
  fun _ _ _ _ _ hα' _ hr' =>
    let := inhabitedExtra_of_bareSurj hα'
    let (a a' b b' : _) := inhabitedExtra_of_bareSurj (@hr' a a' b b')
    bareSurj_of_inhabitedExtra

def New.instBareInjQuot : new_type% @instBareInjQuot.{u} :=
  fun _ _ _ _ _ hα' _ hα₂' _ hr' =>
    let := inhabitedExtra_of_bareSurj hα'
    let := subsingletonExtra_of_bareInj hα₂'
    let (a a' b b' : _) := inhabitedExtra_of_bareSurj (@hr' a a' b b')
    bareInj_of_subsingletonExtra
