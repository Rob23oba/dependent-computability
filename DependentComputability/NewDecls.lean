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
  fun {_} _ {_} zero {_} succ {t} _ => t.rec zero fun _ ih => succ () ih

protected def PUnit.{u} : new_type% @PUnit.{u} :=
  .mk (fun _ => PUnit.{u}) (TrivialEncoding _) (.trivialEncoding _)

protected def PUnit.unit.{u} : new_type% @PUnit.unit.{u} :=
  @_root_.PUnit.unit.{u}

protected theorem propext : new_type% @propext := by
  intro p p_extra q q_extra h h_extra
  dsimp only
  cases propext h
  rcases p_extra with ⟨pty, penc, pelim⟩
  rcases q_extra with ⟨qty, qenc, qelim⟩
  cases pelim.eq
  cases qelim.eq
  rcases h_extra with ⟨hmp, hmpr⟩
  have : pty = qty := by
    ext h
    exact ⟨@hmp h, @hmpr h⟩
  cases this
  constructor

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
set_option genInjectivity false in
inductive Quot._base {α : Sort u} {α_extra : new_type% α}
    {r : α → α → Prop} (r_extra : new_type% r) :
    Quot r → Sort u where
  | mk {a : α} (a_extra : α_extra.1 a) : _base r_extra (Quot.mk r a)

inductive Quot._rel {α : Sort u} {α_extra : new_type% α}
    {r : α → α → Prop} (r_extra : new_type% r) :
    (q : Quot r) → Quot._base r_extra q → Quot._base r_extra q → Prop where
  | mk {a : α} (a_extra : α_extra.1 a) {b : α} (b_extra : α_extra.1 b)
    {h : r a b} (h_extra : (r_extra a_extra b_extra).1 h) :
    _rel r_extra (Quot.mk r b) (Quot.sound h ▸ .mk a_extra) (.mk b_extra)

inductive Quot._encoding {α : Sort u} {α_extra : new_type% α}
    {r : α → α → Prop} (r_extra : new_type% r) :
    ⦃q : Quot r⦄ → (q : Quot (_rel r_extra q)) → (n : ℕ) → Prop where
  | mk {a : α} {a_extra : α_extra.1 a} {n : ℕ} (h : α_extra.2 a_extra n) :
    @_encoding α α_extra r r_extra (Quot.mk r a) (Quot.mk _ (.mk a_extra)) n

protected def Quot.{u} : new_type% @Quot.{u} := fun α α_extra r r_extra =>
  .mk (fun q => Quot (Quot._rel r_extra q)) (Quot._encoding r_extra) <| by
    intro hprop a a_extra n
    simp only [trivialEncoding_iff]
    constructor
    · rintro ⟨h⟩
      simpa using (α_extra.3 hprop _ _).mp h
    · rintro rfl
      rcases a_extra with ⟨@⟨a, a'⟩⟩
      constructor
      exact (α_extra.3 hprop _ _).mpr .zero

protected def Quot.mk.{u} : new_type% @Quot.mk.{u} := fun _ _ _ _ _ a =>
  _root_.Quot.mk _ (.mk a)

protected theorem Quot.ind.{u} : new_type% @Quot.ind.{u} := by
  intro α α_extra r r_extra motive motive mk mk t t
  rcases t with ⟨@⟨t, t⟩⟩
  apply mk

protected def Quot.lift.{u, v} : new_type% @Quot.lift.{u, v} :=
  fun α α_extra r r_extra β β_extra f f_extra h h_extra q q_extra =>
    _root_.Quot.lift (fun x : _base r_extra q =>
      haveI : _root_.Quot.lift f h q = f x.1 := by
        rcases x with @⟨a, a⟩
        rfl
      this ▸ f_extra x.2) ?_ q_extra
where finally
  rintro _ _ @⟨a, a_extra, b, b_extra, hab, hab_extra⟩
  dsimp only
  rw! (castMode := .all) [← Quot.sound hab]
  change h a b hab ▸ f_extra a_extra = f_extra b_extra
  refine (h_extra a_extra b_extra hab_extra).rec ?_
  rfl

protected theorem Quot.sound.{u} : new_type% @Quot.sound.{u} := by
  intro α α_extra r r_extra a a_extra b b_extra h h_extra
  dsimp only
  have sound := _root_.Quot.sound h
  have sound_extra := _root_.Quot.sound (Quot._rel.mk a_extra b_extra h_extra)
  simp only [Quot.mk]
  rw! [← sound_extra, ← sound]
  constructor

theorem subsingletonExtra_of_subsingleton
    {α : Sort u} (α_extra : new_type% α)
    {h : _root_.Subsingleton α} (h_extra : new_type% h) :
    SubsingletonExtra α_extra := by
  constructor
  intro x
  constructor
  intro a b
  cases h_extra.1 a b
  rfl

instance {α : Sort u} (α_extra : new_type% α) : SubsingletonExtra (new% Squash α) :=
  subsingletonExtra_of_subsingleton _ (new% @instSubsingletonSquash α)

protected noncomputable def uniqueChoice.{u} : new_type% @uniqueChoice.{u} :=
  fun α α_extra h h_extra =>
    haveI : _root_.Nonempty ((a : α) ×' α_extra.1 a) := by
      obtain @⟨a, a_extra⟩ := h_extra
      exact ⟨a, a_extra⟩
    (uniqueChoice this).liftOn (fun x =>
        haveI : uniqueChoice h = _root_.Squash.mk x.1 := Subsingleton.allEq ..
        this ▸ Squash.mk _ x.2) (by intros; apply Subsingleton.allEq)

end New

instance {α : Sort u} (α_extra : new_type% α) [SubsingletonExtra α_extra]
    {a : α} (a_extra : new_type% a)
    {b : α} (b_extra : new_type% b) :
    InhabitedExtra (new% a = b) where
  default := by
    rintro rfl
    cases (SubsingletonExtra.subsingleton a).allEq a_extra b_extra
    constructor

instance : FullyRepresentable New.Nat where
  default _ := ()
  subsingleton _ := inferInstanceAs (Subsingleton Unit)
  isRepresentable {x} _ := ⟨x, rfl⟩

def uniqueNatVal (n : Nat) : new_type% n := ()

inductive New.Subtype._induct {α : Sort u} {α_extra : new_type% α}
    {p : α → Prop} (p_extra : new_type% p) (t : Subtype p) where
  | mk (val : α_extra.1 t.1) (property : (p_extra val).1 t.2)

inductive New.Subtype._encoding {α : Sort u} {α_extra : new_type% α}
    {p : α → Prop} (p_extra : new_type% p)
    ⦃t : Subtype p⦄ (t_extra : _induct p_extra t) (n : ℕ) : Prop where
  | mk (val_enc : α_extra.2 t_extra.1 n)

def New.Subtype : new_type% @Subtype.{u} := fun _ _ _ p =>
  .mk (Subtype._induct p) (Subtype._encoding p) (.univElim _)

def New.Subtype.mk : new_type% @Subtype.mk.{u} :=
  fun _ _ _ _ _ x _ y => ⟨x, y⟩

def New.Subtype.rec.{v, u} : new_type% @Subtype.rec.{v, u} :=
  fun _ _ _ _ _ _ _ intro _ t => intro t.1 t.2

@[simp]
theorem encoding_subtype_def {α : Sort u} {α_extra : new_type% α}
    {p : α → Prop} {p_extra : new_type% p}
    {t : Subtype p} {t_extra : new_type% t} {n : ℕ} :
    (new% Subtype p).2 t_extra n ↔ α_extra.2 t_extra.1 n := by
  constructor
  · rintro ⟨h⟩
    exact h
  · intro h
    exact ⟨h⟩

inductive New.List._induct {α : Type u} (α_extra : α → Type u) :
    List α → Type u where
  | nil : _induct α_extra []
  | cons {head : α} (head_extra : α_extra head)
    {tail : List α} (tail_extra : _induct α_extra tail) :
    _induct α_extra (head :: tail)

inductive New.List._encoding {α : Type u}
    (α_extra : α → Type u) (α_enc : ⦃t : α⦄ → α_extra t → ℕ → Prop) :
    ⦃l : List α⦄ → _induct α_extra l → ℕ → Prop where
  | nil : _encoding α_extra α_enc .nil (Nat.pair 0 1)
  | cons {head : α} {head_extra : α_extra head}
    {head_n : ℕ} (head_enc : α_enc head_extra head_n)
    {tail : List α} {tail_extra : _induct α_extra tail}
    {tail_n : ℕ} (tail_enc : _encoding α_extra α_enc tail_extra tail_n) :
    _encoding α_extra α_enc (.cons head_extra tail_extra)
      (Nat.pair (Nat.pair head_n tail_n) 2)

def New.List : new_type% @List.{u} :=
  fun _ α_extra => .mk (New.List._induct α_extra.1) (New.List._encoding α_extra.1 α_extra.2)
    (IsPropEncodingTrivial.univElim.{u + 1} _)

def New.List.nil : new_type% @List.nil.{u} :=
  fun _ α_extra => @New.List._induct.nil _ α_extra.1

def New.List.cons : new_type% @List.cons.{u} :=
  fun _ α_extra => @New.List._induct.cons _ α_extra.1

noncomputable def New.List.rec.{u, v} : new_type% @List.rec.{u, v} :=
  fun _ _ _ _ _ nil _ cons _ t => t.rec nil (fun _ _ _ ih => cons _ _ ih)

set_option inductive.autoPromoteIndices false in
inductive New.Array._induct {α : Type u} (α_extra : α → Type u)
    (t : Array α) : Type u where
  | mk (toList : New.List._induct α_extra t.1) : _induct α_extra t

inductive New.Array._encoding {α : Type u}
    (α_extra : α → Type u) (α_enc : ⦃t : α⦄ → α_extra t → ℕ → Prop)
    ⦃l : Array α⦄ (l : _induct α_extra l) (n : ℕ) : Prop where
  | mk (toList : New.List._encoding α_extra α_enc l.1 n)

def New.Array : new_type% @Array.{u} :=
  fun _ α_extra => .mk (New.Array._induct α_extra.1) (New.Array._encoding α_extra.1 α_extra.2)
    (IsPropEncodingTrivial.univElim.{u + 1} _)

def New.Array.mk : new_type% @Array.mk.{u} :=
  fun _ α _ toList => @New.Array._induct.mk _ α.1 _ toList

def New.Array.rec.{u, v} : new_type% @Array.rec.{u, v} :=
  fun _ _ _ _ _ mk _ t => mk t.1

convert_to_new String

instance {α : Type u} {α_extra : new_type% α} [SubsingletonExtra α_extra] :
    SubsingletonExtra (new% List α) where
  subsingleton t := by
    constructor
    intro t₁ t₂
    induction t₁ with
    | nil => cases t₂; rfl
    | cons head tail ih =>
      rcases t₂ with _ | ⟨head', tail'⟩
      cases Subsingleton.allEq head head'
      cases ih tail'
      rfl

instance {α : Type u} {α_extra : new_type% α} [InhabitedExtra α_extra] :
    InhabitedExtra (new% List α) where
  default t := t.rec .nil fun head _ ih => .cons (InhabitedExtra.default head) ih

instance {α : Type u} {α_extra : new_type% α} [SubsingletonExtra α_extra] :
    SubsingletonExtra (new% Array α) where
  subsingleton t := by
    constructor
    intro t₁ t₂
    refine congrArg New.Array._induct.mk ?_
    apply Subsingleton.allEq (α := new_type% t.1)

instance {α : Type u} {α_extra : new_type% α} [InhabitedExtra α_extra] :
    InhabitedExtra (new% Array α) where
  default t := t.rec fun a => .mk (InhabitedExtra.default (α_extra := new% List α) a)

def inhabitedExtraOfDecidable {p : Prop} {p_extra : new_type% p}
    {h : Decidable p} (h_extra : new_type% h) :
    InhabitedExtra p_extra where
  default t := by cases h_extra <;> trivial

instance {n : ℕ} {n_extra : new_type% n} {m : ℕ} {m_extra : new_type% m} :
    InhabitedExtra (new% Nat.le n m) :=
  inhabitedExtraOfDecidable (new% Nat.decLe n m)

instance {n : ℕ} {n_extra : new_type% n} {m : ℕ} {m_extra : new_type% m} :
    InhabitedExtra (new% n ≤ m) :=
  inferInstanceAs (InhabitedExtra (new% Nat.le n m))

instance {n : ℕ} {n_extra : new_type% n} {m : ℕ} {m_extra : new_type% m} :
    InhabitedExtra (new% n < m) :=
  inferInstanceAs (InhabitedExtra (new% Nat.le n.succ m))

instance {n : ℕ} {n_extra : new_type% n} : InhabitedExtra (new% Fin n) where
  default t :=
    .mk _ _ () (InhabitedExtra.default (α_extra := @New.Nat.le t.succ () n ()) t.2)

instance {n : ℕ} {n_extra : new_type% n} : SubsingletonExtra (new% Fin n) where
  subsingleton t := by
    constructor
    rintro ⟨⟩ ⟨⟩; rfl

instance {n : ℕ} {n_extra : new_type% n} : InhabitedExtra (new% BitVec n) where
  default t := .ofFin _ _ (InhabitedExtra.default (α_extra := new% Fin (Nat.pow 2 n)) t.1)

instance {n : ℕ} {n_extra : new_type% n} : SubsingletonExtra (@New.BitVec n n_extra) where
  subsingleton t := by
    constructor
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩; rfl

instance : InhabitedExtra New.UInt8 where
  default t := .ofBitVec _ (InhabitedExtra.default (α_extra := new% BitVec 8) t.1)

instance : SubsingletonExtra New.UInt8 where
  subsingleton t := by
    constructor
    rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl

instance : InhabitedExtra New.UInt32 where
  default t := .ofBitVec _ (InhabitedExtra.default (α_extra := new% BitVec 32) t.1)

instance : SubsingletonExtra New.UInt32 where
  subsingleton t := by
    constructor
    rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl

convert_to_new inferInstance instDecidableOr instDecidableAnd

instance {n : UInt32} (n_extra : new_type% n) :
    InhabitedExtra (new% UInt32.isValidChar n) :=
  inhabitedExtraOfDecidable (new% (inferInstance : Decidable (UInt32.isValidChar n)))

instance : InhabitedExtra New.Char where
  default t := .mk _ (InhabitedExtra.default (α_extra := New.UInt32) t.1)
    (InhabitedExtra.default (α_extra := @New.UInt32.isValidChar t.1 _) _)

instance : SubsingletonExtra New.Char where
  subsingleton t := by
    constructor
    rintro ⟨⟨⟨⟨⟩⟩⟩⟩ ⟨⟨⟨⟩⟩⟩; rfl

instance : SubsingletonExtra New.ByteArray where
  subsingleton t := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    cases Subsingleton.allEq a b; rfl

instance : InhabitedExtra New.ByteArray where
  default t := t.rec fun a => .mk _
    (show new_type% a from InhabitedExtra.default (α_extra := New.Array New.UInt8) a)

instance {b : ByteArray} (b_extra : new_type% b) :
    InhabitedExtra (New.ByteArray.IsValidUTF8 b_extra) where
  default t := by
    rcases t with ⟨l, hl⟩
    refine @New.ByteArray.IsValidUTF8._induct.intro _ _ l ?_ hl ?_
    · with_reducible exact InhabitedExtra.default _
    · with_reducible exact InhabitedExtra.default _

instance : SubsingletonExtra New.String where
  subsingleton t := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    cases Subsingleton.allEq a b; rfl

instance : InhabitedExtra New.String where
  default t := .ofByteArray _ (InhabitedExtra.default (α_extra := New.ByteArray) _)
    (InhabitedExtra.default (α_extra := @New.ByteArray.IsValidUTF8 t.1 _) _)

noncomputable def uniqueStrVal (s : String) : new_type% s :=
  InhabitedExtra.default (α_extra := new% String) s

instance {p : Prop} {p_extra : new_type% p} {q : Prop} {q_extra : new_type% q}
    [InhabitedExtra p_extra] [InhabitedExtra q_extra] :
    InhabitedExtra (New.Iff p_extra q_extra) where
  default h := by
    constructor
    · intro hp hp'
      exact InhabitedExtra.default (h.mp hp)
    · intro hq hq'
      exact InhabitedExtra.default (h.mpr hq)

instance {p : Prop} {p_extra : new_type% p} {q : Prop} {q_extra : new_type% q}
    [InhabitedExtra p_extra] [InhabitedExtra q_extra] :
    InhabitedExtra (New.And p_extra q_extra) where
  default h := by
    constructor
    · exact InhabitedExtra.default h.1
    · exact InhabitedExtra.default h.2

instance {p : Prop} {p_extra : new_type% p} {q : Prop} {q_extra : new_type% q}
    [InhabitedExtra p_extra] [InhabitedExtra q_extra] :
    InhabitedExtra (New.Or p_extra q_extra) where
  default h := by
    rcases h with h | h
    · left; exact InhabitedExtra.default h
    · right; exact InhabitedExtra.default h

convert_to_new Lean.SourceInfo Lean.SyntaxNodeKind Lean.Syntax.Preresolved

inductive _root_.New.Lean.Syntax._induct : Lean.Syntax → Type where
  | missing : _induct .missing
  | node
    {info : Lean.SourceInfo} (info_extra : new_type% info)
    {kind : Lean.SyntaxNodeKind} (kind_extra : new_type% kind)
    {args : Array Lean.Syntax}
    (args_extra : @New.List._induct Lean.Syntax _induct args.1) :
    _induct (.node info kind args)
  | atom {info : Lean.SourceInfo} (info_extra : new_type% info)
    {val : String} (val_extra : new_type% val) : _induct (.atom info val)
  | ident {info : Lean.SourceInfo} (info_extra : new_type% info)
    {rawVal : Substring.Raw} (rawVal_extra : new_type% rawVal)
    {val : Lean.Name} (val_extra : new_type% val)
    {preresolved : List Lean.Syntax.Preresolved}
    (preresolved_extra : new_type% preresolved) :
    _induct (.ident info rawVal val preresolved)

inductive _root_.New.Lean.Syntax._encoding :
    ⦃t : Lean.Syntax⦄ → New.Lean.Syntax._induct t → ℕ → Prop where
  | missing : _encoding .missing 1
  | node
    {info : Lean.SourceInfo} {info_extra : new_type% info}
    {info_n : ℕ} (info_enc : New.Lean.SourceInfo.2 info_extra info_n)
    {kind : Lean.SyntaxNodeKind} {kind_extra : new_type% kind}
    {kind_n : ℕ} (kind_enc : New.Lean.SyntaxNodeKind.2 kind_extra kind_n)
    {args : Array Lean.Syntax}
    {args_extra : @New.List._induct Lean.Syntax New.Lean.Syntax._induct args.1}
    {args_n : ℕ} (args_enc : New.List._encoding
      New.Lean.Syntax._induct _encoding args_extra args_n) :
    _encoding (.node info_extra kind_extra args_extra)
      (Nat.pair (Nat.pair info_n kind_n) args_n * 4 + 2)
  | atom {info : Lean.SourceInfo} {info_extra : new_type% info}
    {info_n : ℕ} (info_enc : New.Lean.SourceInfo.2 info_extra info_n)
    {val : String} {val_extra : new_type% val}
    {val_n : ℕ} (val_enc : New.String.2 val_extra val_n) :
    _encoding (.atom info_extra val_extra) (Nat.pair info_n val_n * 4 + 3)
  | ident  {info : Lean.SourceInfo} {info_extra : new_type% info}
    {info_n : ℕ} (info_enc : New.Lean.SourceInfo.2 info_extra info_n)
    {rawVal : Substring.Raw} {rawVal_extra : new_type% rawVal}
    {rawVal_n : ℕ} (rawVal_enc : New.Substring.Raw.2 rawVal_extra rawVal_n)
    {val : Lean.Name} (val_extra : new_type% val)
    {val_n : ℕ} (val_enc : New.Lean.Name.2 val_extra val_n)
    {preresolved : List Lean.Syntax.Preresolved}
    (preresolved_extra : new_type% preresolved)
    {preresolved_n : ℕ}
    (preresolved_enc : (New.List New.Lean.Syntax.Preresolved).2 preresolved_extra preresolved_n) :
    _encoding (.ident info_extra rawVal_extra val_extra preresolved_extra)
      (Nat.pair (Nat.pair (Nat.pair info_n rawVal_n) val_n) preresolved_n * 4 + 4)

def New.Lean.Syntax : new_type% Lean.Syntax :=
  .mk Syntax._induct Syntax._encoding (IsPropEncodingTrivial.univElim.{1} _)

def New.Lean.Syntax.missing : new_type% Lean.Syntax.missing := @_induct.missing
def New.Lean.Syntax.atom : new_type% Lean.Syntax.atom := @_induct.atom
def New.Lean.Syntax.ident : new_type% Lean.Syntax.ident := @_induct.ident
def New.Lean.Syntax.node : new_type% Lean.Syntax.node :=
  fun _ info _ kind _ args => _induct.node info kind args.1

noncomputable def New.Lean.Syntax.rec : new_type% @Lean.Syntax.rec.{u} :=
  fun motive_1 motive_1_extra motive_2 _ motive_3 motive_3_extra
      missing missing_extra node node_extra atom atom_extra ident ident_extra
      mk mk_extra nil nil_extra cons cons_extra t t_extra =>
    @Syntax._induct.rec (fun t t_extra => (motive_1_extra t_extra).1
        (@_root_.Lean.Syntax.rec motive_1 motive_2 motive_3
          missing node atom ident mk nil cons t))
      (fun t t_extra => (motive_3_extra t_extra).1
        (@Lean.Syntax.rec_2 motive_1 motive_2 motive_3
          missing node atom ident mk nil cons t))
      missing_extra
      (fun _ _ _ _ _ ih => node_extra _ _ _ (mk_extra _ ih))
      @atom_extra @ident_extra @nil_extra
      (fun _ _ _ head_ih tail_ih => cons_extra _ _ head_ih tail_ih)
      t t_extra

convert_to_new Prod

instance {α : Type u} (α_extra : new_type% α)
    {β : Type v} (β_extra : new_type% β)
    [SubsingletonExtra α_extra] [SubsingletonExtra β_extra] :
    SubsingletonExtra (New.Prod α_extra β_extra) where
  subsingleton t := by
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
  intro p p_extra
  by_cases h : p
  · by_cases h' : p_extra.1 h
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
