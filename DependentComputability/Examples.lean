import DependentComputability.Tactic.RecursorModel

#eval! recAutoDCompMain ``String.all
#eval! recAutoDCompMain ``Nat.gcd
#eval! recAutoDCompMain ``List.mapM
#eval! recAutoDCompMain ``List.filterMapM
#eval! recAutoDCompMain ``List.filterMapTR

#eval! recAutoDCompMain ``List.eraseDups

convert_to_new List.eraseDups.dcomp
convert_to_new List.filterMapM.dcomp

instance {s : String.Slice} {s' : new_type% s}
    {a : s.Pos} {a' : new_type% a}
    {b : s.Pos} {b' : new_type% b} :
    InhabitedExtra (new% a < b) where
  default x := InhabitedExtra.default (α_extra := new% a.offset.byteIdx < b.offset.byteIdx) x

def _root_.New.Lean.opaqueId.{u} : new_type% @Lean.opaqueId.{0} :=
  fun _ _ _ h => (fun _ => _root_.Lean.opaqueId h) (Sort u)

#time convert_to_new String.all.dcomp

#print New.Subsingleton._induct

def weirdType (b : Bool) : Type 1 :=
  match b with
  | false => ULift Nat
  | true => Type

def weirdValue (b : Bool) : weirdType b :=
  match b with
  | false => .up 1234
  | true => Bool

def weirdFunction (x : weirdType b) : Nat :=
  match b with
  | false => x.down
  | true => 24

def myFunction (x : Nat) : Nat :=
  weirdFunction (weirdValue (x == 0))

#eval! recAutoDCompMain ``myFunction
convert_to_new myFunction.dcomp

theorem test : Computable myFunction := by
  have : DComputable (new% myFunction) := new% myFunction.dcomp id .id
  rwa [dcomputable_iff_computable (α_extra := new% ℕ) (β_extra := new% ℕ)] at this

#eval! recAutoDCompMain ``Part.instMonad

#eval! recAutoDCompMain ``Nat.rfind
convert_to_new Nat.rfind.dcomp

#print New.Nat.rfindX.dcomp

#check Part.unwrap
#print HAdd.hAdd.dcomp

#print myFunction.dcomp

#print Eq.rec.dprim
#eval! recAutoDCompMain ``Quotient.rec
convert_to_new Quotient.rec.dcomp

#print DComp
#print New.Quotient.rec.dcomp
#print Quot.rec.dcomp
#eval! recAutoDCompMain ``Finset.sumEquiv

#print List.eq_nil_iff_forall_not_mem

private lemma List.eq_nil_iff_forall_not_mem._alt :
    type_of% @List.eq_nil_iff_forall_not_mem.{u} := by
  intro α l
  rcases l with _ | ⟨a, l⟩
  · simp
  · apply iff_of_false
    · simp
    · intro h
      exact h a List.mem_cons_self

convert_to_new List.eq_nil_iff_forall_not_mem._alt

lemma _root_.New.List.eq_nil_iff_forall_not_mem :
    new_type% @List.eq_nil_iff_forall_not_mem.{u} := by
  exact new% @List.eq_nil_iff_forall_not_mem._alt.{u}

convert_to_new Finset.sumEquiv.dcomp

#print Finset.sumEquiv.dcomp

#synth InhabitedExtra New.Nat
