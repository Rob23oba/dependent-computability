import DependentComputability.Tactic.ConvertToNew


/-!
Essentials
-/

noncomputable opaque uniqueChoice (h : Nonempty α) : Squash α :=
  .mk (Classical.choice h)

namespace New

protected def Nat : new_type% Nat :=
  .mk (fun _ => Unit) (fun {n} _ m => n = m) (IsPropEncodingTrivial.univElim.{0} _)

protected def Nat.zero : new_type% @Nat.zero := ()
protected def Nat.succ : new_type% @Nat.succ := fun _ _ => ()

protected def Nat.rec.{u} : new_type% @Nat.rec.{u} :=
  fun {_} _ {_} zero {_} succ {t_base} _ => t_base.rec zero fun _ ih => succ () ih

protected def PUnit.{u} : new_type% @PUnit.{u} :=
  .mk (fun _ => PUnit.{u}) (TrivialEncoding _) (.trivialEncoding _)

protected def PUnit.unit.{u} : new_type% @PUnit.unit.{u} :=
  @_root_.PUnit.unit.{u}

protected theorem propext : new_type% @propext := by
  intro p_base p q_base q h_base h
  dsimp only
  cases propext h_base
  rcases p with ⟨pty, penc, pelim⟩
  rcases q with ⟨qty, qenc, qelim⟩
  cases pelim.eq
  cases qelim.eq
  rcases h with ⟨hmp, hmpr⟩
  have : pty = qty := by
    ext h
    exact ⟨@hmp h, @hmpr h⟩
  cases this
  constructor

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
set_option genInjectivity false in
inductive Quot._base {α_base : Sort u} {α : new_type% α_base}
    {r_base : α_base → α_base → Prop} (r : new_type% r_base) :
    Quot r_base → Sort u where
  | mk {a_base : α_base} (a : α.1 a_base) : _base r (Quot.mk r_base a_base)

inductive Quot._rel {α_base : Sort u} {α : new_type% α_base}
    {r_base : α_base → α_base → Prop} (r : new_type% r_base) :
    (q : Quot r_base) → Quot._base r q → Quot._base r q → Prop where
  | mk {a_base : α_base} (a : α.1 a_base) {b_base : α_base} (b : α.1 b_base)
    {h_base : r_base a_base b_base} (h : (r a b).1 h_base) :
    _rel r (Quot.mk r_base b_base) (Quot.sound h_base ▸ .mk a) (.mk b)

inductive Quot._encoding {α_base : Sort u} {α : new_type% α_base}
    {r_base : α_base → α_base → Prop} (r : new_type% r_base) :
    ⦃q_base : Quot r_base⦄ → (q : Quot (_rel r q_base)) → (n : ℕ) → Prop where
  | mk {a_base : α_base} {a : α.1 a_base} {n : ℕ} (h : α.2 a n) :
    @_encoding α_base α r_base r (Quot.mk r_base a_base) (Quot.mk _ (.mk a)) n

protected def Quot.{u} : new_type% @Quot.{u} := fun α_base α r_base r =>
  .mk (fun q => Quot (Quot._rel r q)) (Quot._encoding r) <| by
    intro hprop a_base a n
    simp only [trivialEncoding_iff]
    constructor
    · rintro ⟨h⟩
      simpa using (α.3 hprop _ _).mp h
    · rintro rfl
      rcases a with ⟨@⟨a_base, a'⟩⟩
      constructor
      exact (α.3 hprop _ _).mpr .zero

protected def Quot.mk.{u} : new_type% @Quot.mk.{u} := fun _ _ _ _ _ a =>
  _root_.Quot.mk _ (.mk a)

protected theorem Quot.ind.{u} : new_type% @Quot.ind.{u} := by
  intro α_base α r_base r motive_base motive mk_base mk t_base t
  rcases t with ⟨@⟨t_base, t⟩⟩
  apply mk

protected def Quot.lift.{u, v} : new_type% @Quot.lift.{u, v} :=
  fun α_base α r_base r β_base β f_base f h_base h q_base q =>
    _root_.Quot.lift (fun x : _base r q_base =>
      haveI : _root_.Quot.lift f_base h_base q_base = f_base x.1 := by
        rcases x with @⟨a_base, a⟩
        rfl
      this ▸ f x.2) ?_ q
where finally
  rintro _ _ @⟨a_base, a, b_base, b, hab_base, hab⟩
  dsimp only
  rw! (castMode := .all) [← Quot.sound hab_base]
  change h_base a_base b_base hab_base ▸ f a = f b
  refine (h a b hab).rec ?_
  rfl

protected theorem Quot.sound.{u} : new_type% @Quot.sound.{u} := by
  intro α_base α r_base r a_base a b_base b h_base h
  dsimp only
  have sound_base := _root_.Quot.sound h_base
  have sound := _root_.Quot.sound (Quot._rel.mk a b h)
  simp only [Quot.mk]
  rw! [← sound, ← sound_base]
  constructor

theorem subsingletonExtra_of_subsingleton
    {α_base : Sort u} (α : New.Sort.1 α_base)
    {h_base : _root_.Subsingleton α_base} (h : new_type% h_base) :
    SubsingletonExtra α := by
  constructor
  intro x
  constructor
  intro a b
  cases h.1 a b
  rfl

instance {α_base : Sort u} (α : New.Sort.1 α_base) : SubsingletonExtra (new% Squash α_base) :=
  subsingletonExtra_of_subsingleton _ (new% @instSubsingletonSquash α_base)

protected noncomputable def uniqueChoice.{u} : new_type% @uniqueChoice.{u} :=
  fun α_base α h_base h =>
    haveI : _root_.Nonempty ((a : α_base) ×' α.1 a) := by
      obtain @⟨a_base, a⟩ := h
      exact ⟨a_base, a⟩
    (uniqueChoice this).liftOn (fun x =>
        haveI : uniqueChoice h_base = _root_.Squash.mk x.1 := Subsingleton.allEq ..
        this ▸ Squash.mk _ x.2) (by intros; apply Subsingleton.allEq)

end New

instance {α_base : Sort u} (α : new_type% α_base) [SubsingletonExtra α]
    {a_base : α_base} (a : α.1 a_base)
    {b_base : α_base} (b : α.1 b_base) :
    NonemptyExtra (New.Eq α a b) where
  nonempty := by
    rintro rfl
    cases (SubsingletonExtra.subsingleton a_base).allEq a b
    constructor
    constructor

instance : UniqueExtra New.Nat where
  default _ := ()
  subsingleton _ := inferInstanceAs (Subsingleton Unit)

def uniqueNatVal (n : Nat) : new_type% n := ()

inductive New.Subtype._induct {α_base : Sort u} {α : new_type% α_base}
    {p_base : α_base → Prop} (p : new_type% p_base) (t : Subtype p_base) where
  | mk (val : α.1 t.1) (property : (p val).1 t.2)

inductive New.Subtype._encoding {α_base : Sort u} {α : new_type% α_base}
    {p_base : α_base → Prop} (p : new_type% p_base)
    ⦃t_base : Subtype p_base⦄ (t : _induct p t_base) (n : ℕ) : Prop where
  | mk (val_enc : α.2 t.1 n)

def New.Subtype : new_type% @Subtype.{u} := fun _ _ _ p =>
  .mk (Subtype._induct p) (Subtype._encoding p) (.univElim _)

def New.Subtype.mk : new_type% @Subtype.mk.{u} :=
  fun _ _ _ _ _ x _ y => ⟨x, y⟩

def New.Subtype.rec.{v, u} : new_type% @Subtype.rec.{v, u} :=
  fun _ _ _ _ _ _ _ intro _ t => intro t.1 t.2

@[simp]
theorem encoding_subtype_def {α_base : Sort u} {α : new_type% α_base}
    {p_base : α_base → Prop} {p : new_type% p_base}
    {t_base : Subtype p_base} {t : new_type% t_base} {n : ℕ} :
    (new% Subtype p_base).2 t n ↔ α.2 t.1 n := by
  constructor
  · rintro ⟨h⟩
    exact h
  · intro h
    exact ⟨h⟩

inductive New.List._induct {α_base : Type u} (α_extra : α_base → Type u) :
    List α_base → Type u where
  | nil : _induct α_extra []
  | cons {head_base : α_base} (head : α_extra head_base)
    {tail_base : List α_base} (tail : _induct α_extra tail_base) :
    _induct α_extra (head_base :: tail_base)

inductive New.List._encoding {α_base : Type u}
    (α_extra : α_base → Type u) (α_enc : ⦃t_base : α_base⦄ → α_extra t_base → ℕ → Prop) :
    ⦃l_base : List α_base⦄ → _induct α_extra l_base → ℕ → Prop where
  | nil : _encoding α_extra α_enc .nil .zero
  | cons {head_base : α_base} {head : α_extra head_base}
    {head_n : ℕ} (head_enc : α_enc head head_n)
    {tail_base : List α_base} {tail : _induct α_extra tail_base}
    {tail_n : ℕ} (tail_enc : _encoding α_extra α_enc tail tail_n) :
    _encoding α_extra α_enc (.cons head tail) (.succ (Nat.pair head_n tail_n))

def New.List : new_type% @List.{u} :=
  fun _ α => .mk (New.List._induct α.1) (New.List._encoding α.1 α.2)
    (IsPropEncodingTrivial.univElim.{u + 1} _)

def New.List.nil : new_type% @List.nil.{u} :=
  fun _ α => @New.List._induct.nil _ α.1

def New.List.cons : new_type% @List.cons.{u} :=
  fun _ α => @New.List._induct.cons _ α.1

noncomputable def New.List.rec.{u, v} : new_type% @List.rec.{u, v} :=
  fun _ _ _ _ _ nil _ cons _ t => t.rec nil (fun _ _ _ ih => cons _ _ ih)

set_option inductive.autoPromoteIndices false in
inductive New.Array._induct {α_base : Type u} (α_extra : α_base → Type u)
    (t : Array α_base) : Type u where
  | mk (toList : New.List._induct α_extra t.1) : _induct α_extra t

inductive New.Array._encoding {α_base : Type u}
    (α_extra : α_base → Type u) (α_enc : ⦃t_base : α_base⦄ → α_extra t_base → ℕ → Prop)
    ⦃l_base : Array α_base⦄ (l : _induct α_extra l_base) (n : ℕ) : Prop where
  | mk (toList : New.List._encoding α_extra α_enc l.1 n)

def New.Array : new_type% @Array.{u} :=
  fun _ α => .mk (New.Array._induct α.1) (New.Array._encoding α.1 α.2)
    (IsPropEncodingTrivial.univElim.{u + 1} _)

def New.Array.mk : new_type% @Array.mk.{u} :=
  fun _ α _ toList => @New.Array._induct.mk _ α.1 _ toList

def New.Array.rec.{u, v} : new_type% @Array.rec.{u, v} :=
  fun _ _ _ _ _ mk _ t => mk t.1

convert_to_new String

instance {α_base : Type u} {α : new_type% α_base} [SubsingletonExtra α] :
    SubsingletonExtra (New.List α) where
  subsingleton t_base := by
    constructor
    intro t₁ t₂
    induction t₁ with
    | nil => cases t₂; rfl
    | cons head tail ih =>
      rcases t₂ with _ | ⟨head', tail'⟩
      cases Subsingleton.allEq head head'
      cases ih tail'
      rfl

instance {α_base : Type u} {α : new_type% α_base} [UniqueExtra α] : UniqueExtra (New.List α) where
  default t_base := t_base.rec .nil fun head _ ih => .cons (UniqueExtra.default head) ih

instance {α_base : Type u} {α : new_type% α_base} [SubsingletonExtra α] :
    SubsingletonExtra (New.Array α) where
  subsingleton t_base := by
    constructor
    intro t₁ t₂
    refine congrArg New.Array._induct.mk ?_
    apply Subsingleton.allEq (α := new_type% t_base.1)

instance {α_base : Type u} {α : new_type% α_base} [UniqueExtra α] : UniqueExtra (New.Array α) where
  default t_base := t_base.rec fun a => .mk
    (show new_type% a from UniqueExtra.default (α := New.List α) a)

def nonemptyExtraOfDecidable {p_base : Prop} {p : new_type% p_base}
    {h_base : Decidable p_base} (h : new_type% h_base) :
    NonemptyExtra p where
  nonempty t_base := by
    cases h
    · contradiction
    · constructor; assumption

instance {n_base : ℕ} {n : new_type% n_base} {m_base : ℕ} {m : new_type% m_base} :
    NonemptyExtra (@New.Nat.le n_base n m_base m) :=
  nonemptyExtraOfDecidable (new% Nat.decLe n_base m_base)

instance {n_base : ℕ} {n : new_type% n_base} {m_base : ℕ} {m : new_type% m_base} :
    NonemptyExtra (new% n_base ≤ m_base) := instNonemptyExtraLeLe

instance {n_base : ℕ} {n : new_type% n_base} {m_base : ℕ} {m : new_type% m_base} :
    NonemptyExtra (new% n_base < m_base) := instNonemptyExtraLeLe

instance {n_base : ℕ} {n : new_type% n_base} : UniqueExtra (@New.Fin n_base n) where
  subsingleton t_base := by
    constructor
    rintro ⟨⟩ ⟨⟩; rfl
  default t_base :=
    .mk _ _ () (NonemptyExtra.transfer (@New.Nat.le t_base.succ () n_base ()) t_base.2)

instance {n_base : ℕ} {n : new_type% n_base} : UniqueExtra (@New.BitVec n_base n) where
  subsingleton t_base := by
    constructor
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩; rfl
  default t_base := .ofFin _ _ (UniqueExtra.default (α := new% Fin (Nat.pow 2 n_base)) t_base.1)

instance : UniqueExtra New.UInt8 where
  subsingleton t_base := by
    constructor
    rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl
  default t_base := .ofBitVec _ (UniqueExtra.default (α := new% BitVec 8) t_base.1)

instance : UniqueExtra New.UInt32 where
  subsingleton t_base := by
    constructor
    rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl
  default t_base := .ofBitVec _ (UniqueExtra.default (α := new% BitVec 32) t_base.1)

convert_to_new inferInstance instDecidableOr instDecidableAnd

instance {n_base : UInt32} (n : new_type% n_base) :
    NonemptyExtra (New.UInt32.isValidChar n) :=
  nonemptyExtraOfDecidable (new% (inferInstance : Decidable (UInt32.isValidChar n_base)))

instance : UniqueExtra New.Char where
  subsingleton t_base := by
    constructor
    rintro ⟨⟨⟨⟨⟩⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl
  default t_base := .mk _ (UniqueExtra.default (α := New.UInt32) t_base.1)
    (NonemptyExtra.transfer (@New.UInt32.isValidChar t_base.1 _) _)

instance : UniqueExtra New.ByteArray where
  subsingleton t_base := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    cases Subsingleton.allEq a b; rfl
  default t_base := t_base.rec fun a => .mk _
    (show new_type% a from UniqueExtra.default (α := New.Array New.UInt8) a)

instance {b_base : ByteArray} (b : new_type% b_base) :
    NonemptyExtra (New.ByteArray.IsValidUTF8 b) where
  nonempty t_base := by
    rcases t_base with ⟨l, hl⟩
    constructor
    refine @New.ByteArray.IsValidUTF8._induct.intro _ _ l ?_ hl ?_
    · with_reducible exact UniqueExtra.default _
    · with_reducible exact NonemptyExtra.transfer _ _

instance : UniqueExtra New.String where
  subsingleton t_base := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    cases Subsingleton.allEq a b; rfl
  default t_base := .ofByteArray _ (UniqueExtra.default (α := New.ByteArray) _)
    (NonemptyExtra.transfer (@New.ByteArray.IsValidUTF8 t_base.1 _) _)

noncomputable def uniqueStrVal (s : String) : new_type% s :=
  UniqueExtra.default (α := new% String) s

convert_to_new Lean.SourceInfo Lean.SyntaxNodeKind Lean.Syntax.Preresolved

inductive _root_.New.Lean.Syntax._induct : Lean.Syntax → Type where
  | missing : _induct .missing
  | node
    {info_base : Lean.SourceInfo} (info : new_type% info_base)
    {kind_base : Lean.SyntaxNodeKind} (kind : new_type% kind_base)
    {args_base : Array Lean.Syntax}
    (args : @New.List._induct Lean.Syntax _induct args_base.1) :
    _induct (.node info_base kind_base args_base)
  | atom {info_base : Lean.SourceInfo} (info : new_type% info_base)
    {val_base : String} (val : new_type% val_base) : _induct (.atom info_base val_base)
  | ident {info_base : Lean.SourceInfo} (info : new_type% info_base)
    {rawVal_base : Substring.Raw} (rawVal : new_type% rawVal_base)
    {val_base : Lean.Name} (val : new_type% val_base)
    {preresolved_base : List Lean.Syntax.Preresolved}
    (preresolved : new_type% preresolved_base) :
    _induct (.ident info_base rawVal_base val_base preresolved_base)

inductive _root_.New.Lean.Syntax._encoding :
    ⦃t_base : Lean.Syntax⦄ → New.Lean.Syntax._induct t_base → ℕ → Prop where
  | missing : _encoding .missing 0
  | node
    {info_base : Lean.SourceInfo} {info : new_type% info_base}
    {info_n : ℕ} (info_enc : New.Lean.SourceInfo.2 info info_n)
    {kind_base : Lean.SyntaxNodeKind} {kind : new_type% kind_base}
    {kind_n : ℕ} (kind_enc : New.Lean.SyntaxNodeKind.2 kind kind_n)
    {args_base : Array Lean.Syntax}
    {args : @New.List._induct Lean.Syntax New.Lean.Syntax._induct args_base.1}
    {args_n : ℕ} (args_enc : New.List._encoding New.Lean.Syntax._induct _encoding args args_n) :
    _encoding (.node info kind args) (Nat.pair info_n (Nat.pair kind_n args_n) * 3 + 1)
  | atom {info_base : Lean.SourceInfo} {info : new_type% info_base}
    {info_n : ℕ} (info_enc : New.Lean.SourceInfo.2 info info_n)
    {val_base : String} {val : new_type% val_base}
    {val_n : ℕ} (val_enc : New.String.2 val val_n) :
    _encoding (.atom info val) (Nat.pair info_n val_n * 3 + 2)
  | ident  {info_base : Lean.SourceInfo} {info : new_type% info_base}
    {info_n : ℕ} (info_enc : New.Lean.SourceInfo.2 info info_n)
    {rawVal_base : Substring.Raw} {rawVal : new_type% rawVal_base}
    {rawVal_n : ℕ} (rawVal_enc : New.Substring.Raw.2 rawVal rawVal_n)
    {val_base : Lean.Name} (val : new_type% val_base)
    {val_n : ℕ} (val_enc : New.Lean.Name.2 val val_n)
    {preresolved_base : List Lean.Syntax.Preresolved}
    (preresolved : new_type% preresolved_base)
    {preresolved_n : ℕ}
    (preresolved_enc : (New.List New.Lean.Syntax.Preresolved).2 preresolved preresolved_n) :
    _encoding (.ident info rawVal val preresolved)
      (Nat.pair info_n (Nat.pair rawVal_n (Nat.pair val_n preresolved_n)) * 3 + 3)

def New.Lean.Syntax : new_type% Lean.Syntax :=
  .mk Syntax._induct Syntax._encoding (IsPropEncodingTrivial.univElim.{1} _)

def New.Lean.Syntax.missing : new_type% Lean.Syntax.missing := @_induct.missing
def New.Lean.Syntax.atom : new_type% Lean.Syntax.atom := @_induct.atom
def New.Lean.Syntax.ident : new_type% Lean.Syntax.ident := @_induct.ident
def New.Lean.Syntax.node : new_type% Lean.Syntax.node :=
  fun _ info _ kind _ args => _induct.node info kind args.1

noncomputable def New.Lean.Syntax.rec : new_type% @Lean.Syntax.rec.{u} :=
  fun motive_1_base motive_1 motive_2_base _ motive_3_base motive_3
      missing_base missing node_base node atom_base atom ident_base ident
      mk_base mk nil_base nil cons_base cons t_base t =>
    @Syntax._induct.rec (fun t_base t => (motive_1 t).1
        (@_root_.Lean.Syntax.rec motive_1_base motive_2_base motive_3_base
          missing_base node_base atom_base ident_base mk_base nil_base cons_base t_base))
      (fun t_base t => (motive_3 t).1
        (@Lean.Syntax.rec_2 motive_1_base motive_2_base motive_3_base
          missing_base node_base atom_base ident_base mk_base nil_base cons_base t_base))
      missing
      (fun _ _ _ _ _ ih => node _ _ _ (mk _ ih))
      @atom @ident @nil
      (fun _ _ _ head_ih tail_ih => cons _ _ head_ih tail_ih)
      t_base t

convert_to_new Prod

instance {α_base : Type u} (α : new_type% α_base)
    {β_base : Type v} (β : new_type% β_base)
    [SubsingletonExtra α] [SubsingletonExtra β] :
    SubsingletonExtra (New.Prod α β) where
  subsingleton t_base := by
    constructor
    rintro ⟨a, b⟩ ⟨a', b'⟩
    cases Subsingleton.allEq a a'
    cases Subsingleton.allEq b b'
    rfl

convert_to_new Nat.mul_add_lt_mul_of_lt_of_lt
convert_to_new List.attach
convert_to_new Array.attach
convert_to_new List.mapM
convert_to_new List.zip_eq_zip_take_min
convert_to_new not_exists
convert_to_new List.cons.injEq
convert_to_new eq_comm
convert_to_new eq_false
convert_to_new Part

inductive Middle : Prop where
  | intro

instance : Decidable Middle := .isTrue .intro

def _root_.New.Middle : new_type% Middle :=
  .mk (fun _ => False) (TrivialEncoding _) (.trivialEncoding _)

theorem almostEm (p : Prop) : p ∨ (p ↔ Middle) ∨ ¬p := by
  obtain h | h := Classical.em p
  · exact .inl h
  · exact .inr (.inr h)

theorem New.almostEm : new_type% almostEm := by
  intro p_base p
  by_cases h : p_base
  · by_cases h' : p.1 h
    · exact .inl h'
    · have iff := iff_of_true h Middle.intro
      refine @New.Or._induct.inr _ _ _ _ (.inl iff) ?_
      refine @New.Or._induct.inl _ _ _ _ iff ?_
      constructor
      · intro _ _; contradiction
      · intro _ _; contradiction
  · refine @New.Or._induct.inr _ _ _ _ (.inr h) ?_
    refine @New.Or._induct.inr _ _ _ _ h ?_
    intro h'
    contradiction

theorem not_em : ¬ new_type% Classical.em := by
  intro h
  cases @h Middle New.Middle
  · contradiction
  · contradiction

theorem not_em' : ¬ ∃ h : type_of% Classical.em, new_type% h := by
  intro ⟨_, h⟩
  cases @h Middle New.Middle
  · contradiction
  · contradiction

theorem not_not_em' : ¬ ∃ h : ¬(type_of% Classical.em), new_type% h := by
  intro ⟨h, _⟩
  simp at h

def splitLeft (p : ℕ → Prop) : ℕ → Prop :=
  fun n => ∃ k, n = k * 2 ∧ p k

def splitRight (p : ℕ → Prop) : ℕ → Prop :=
  fun n => ∃ k, n = k * 2 + 1 ∧ p k

def split (p : ℕ → ℕ → Prop) : ℕ → Prop :=
  Nat.unpaired p

inductive New.Prod._encodes {α_base : Type u} {α : new_type% α_base}
    {β_base : Type v} {β : new_type% β_base} :
    {x_base : α_base × β_base} → (x : New.Prod._induct α β x_base) → Nat → Prop where
  | mk {fst_base : α_base} {fst : α.1 fst_base} {fst_num : ℕ} (fst_encodes : α.2 fst fst_num)
       {snd_base : β_base} {snd : β.1 snd_base} {snd_num : ℕ} (snd_encodes : β.2 snd snd_num) :
       _encodes (New.Prod.mk α β fst snd) (Nat.pair fst_num snd_num)

lemma Nat.rfindX._proof_1_alt : type_of% @Nat.rfindX._proof_1 := by
  intro p H m al
  rcases H with ⟨n, h₁, h₂⟩
  rcases Nat.lt_trichotomy m n with (h₃ | h₃ | h₃)
  · exact h₂ _ h₃
  · rw [h₃]
    exact h₁.fst
  · injection Part.mem_unique h₁ (al _ h₃)

convert_to_new Nat.rfindX._proof_1_alt

lemma New.Nat.rfindX._proof_1 : new_type% @Nat.rfindX._proof_1 :=
  @New.Nat.rfindX._proof_1_alt

convert_to_new New.Sort
convert_to_new New.Forall
convert_to_new Quot.rec
convert_to_new New.Nat
convert_to_new New.Nat.add
