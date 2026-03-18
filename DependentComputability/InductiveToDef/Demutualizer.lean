import DependentComputability.InductiveToDef.ConvertIndexType
import Mathlib.Data.List.Forall2
import Mathlib.Logic.Relation
import Mathlib

namespace InductiveToDef

open Lean Meta

def expandMutualInduct (addNonMutualDecl : Declaration → MetaM Unit) (decl : Declaration) :
    MetaM Unit := do
  let .inductDecl lparams nparams inducts isUnsafe := decl | unreachable!
  let levels := lparams.map Level.param
  let primaryName := inducts.head!.name
  let mut indexCtors := #[]
  for induct in inducts do
    indexCtors := indexCtors.push {
      name := .str induct.name "_index_ctor"
      type := induct.type
    }
  let indexIndType ← forallBoundedTelescope inducts.head!.type (some nparams) fun vars _body => do
    mkForallFVars vars default -- `addDeclIndexTypeWrapper` will ignore the body anyways
  let indexInd := {
    name := .str primaryName "_index"
    type := indexIndType
    ctors := indexCtors.toList
  }
  let indexDecl : Declaration := .inductDecl lparams nparams [indexInd] isUnsafe
  addDeclIndexTypeWrapper indexDecl
  let mut mutualCtors := #[]
  let mutualName := .str primaryName "_mutual"
  let indices : Std.HashMap Name Nat := .ofList (inducts.mapIdx fun idx val => (val.name, idx))
  let mut inductValues : Array Expr := #[]
  for induct in inducts do
    let value ← forallTelescope induct.type fun vars _body => do
      let params := vars.take nparams
      let indexVal := mkAppN (.const (.str induct.name "_index_ctor") levels) vars
      mkLambdaFVars vars (.app (mkAppN (.const mutualName levels) params) indexVal)
    inductValues := inductValues.push value
  for induct in inducts do
    for ctor in induct.ctors do
      let mutualCtorType := ctor.type.replace fun expr => do
        expr.withApp fun fn args => do
          let .const nm _us := fn | none
          let some index := indices[nm]? | none
          return inductValues[index]!.beta args
      mutualCtors := mutualCtors.push {
        name := .str ctor.name "_mutual_ctor"
        type := mutualCtorType
      }
  let mutualIndType ← forallTelescopeReducing (whnfType := true) inducts.head!.type
      fun vars body => do
    unless body.isSort do
      throwError "Invalid inductive type, expected universe at{indentExpr body}"
    let params := vars.take nparams
    let indexTy := mkAppN (.const indexInd.name levels) params
    mkForallFVars params (.forallE `index indexTy body .default)
  let mutualInd := {
    name := mutualName
    type := mutualIndType
    ctors := mutualCtors.toList
  }
  let mutualDecl : Declaration := .inductDecl lparams nparams [mutualInd] isUnsafe
  addNonMutualDecl mutualDecl
  for induct in inducts, val in inductValues do
    addDecl <| .defnDecl {
      name := induct.name
      levelParams := lparams
      type := induct.type
      value := val
      hints := .abbrev
      safety := if isUnsafe then .unsafe else .safe
    }
    for ctor in induct.ctors do
      addDecl <| .defnDecl {
        name := ctor.name
        levelParams := lparams
        type := ctor.type
        value := .const (.str ctor.name "_mutual_ctor") levels
        hints := .abbrev
        safety := if isUnsafe then .unsafe else .safe
      }

open Lean Elab Command in
elab "simple_mutual_inductive_decl " params:num inducts:rawInductive* : command => do
  liftTermElabM do
    elabRawInductiveDecl params.getNat inducts fun decl =>
      expandMutualInduct (fun decl => addDecl decl) decl

simple_mutual_inductive_decl 1
  raw_inductive MyType : Nat → Type
    | InductiveToDef.MyType.abc : (a : Nat) → (x : Nat) → (y : Fin x) → (z : Fin (x + y)) → MyType a
    | InductiveToDef.MyType.xyz : (a : Nat) → MyType a
    | InductiveToDef.MyType.thing : (a b : Nat) → MyType a → MyType a
  raw_inductive MyOtherType : Nat → Type
    | InductiveToDef.MyOtherType.abc :
      (a : Nat) → (x : Nat) → (y : Fin x) → (z : Fin (x + y)) → MyOtherType a
    | InductiveToDef.MyOtherType.xyz : (a : Nat) → MyOtherType a
    | InductiveToDef.MyOtherType.thing : (a b : Nat) → MyOtherType a

#print Lean.Compiler.LCNF.Code

#print InductiveToDef.MyType._mutual

inductive TestBase (p : ∀ {α : Type}, List α → Prop) where
  | mk (l : List (TestBase @p)) : TestBase @p

inductive TestWF (p : ∀ {α : Type}, List α → Prop) : TestBase p → Prop where
  | mk (l : List (TestBase @p)) (h : p l) (h' : ∀ x ∈ l, TestWF @p x) : TestWF @p (.mk l)

def Test (p : ∀ {α : Type}, List α → Prop) : Type :=
  Subtype (TestWF @p)

def Test.mk (l : List (Test @p)) (h : p l) : Test @p :=
  ⟨.mk (l.map Subtype.val), .mk _ h <| by simp +contextual⟩

#print Std.DHashMap.Raw.WF

axiom TestBad (p : ∀ {α : Type}, List α → Prop) : Type
axiom TestBad.mk (l : List (TestBad @p)) (h : p l) : TestBad @p
axiom TestBad.list (x : TestBad @p) : List (TestBad @p)
axiom TestBad.prop (x : TestBad @p) : p x.list

axiom TestBad.list_mk (l : List (TestBad @p)) (h : p l) : (TestBad.mk l h).list = l

example : False := by
  let p {α : Type} (l : List α) : Prop := α → False
  by_cases h : TestBad @p → False
  · have : TestBad @p := TestBad.mk [] h
    contradiction
  · simp only [Classical.not_forall, not_false_eq_true] at h
    obtain ⟨x, hx⟩ := h
    have := x.prop
    contradiction

inductive QuotTestBase (r : ∀ ⦃α : Type⦄, List α → List α → Prop) where
  | mk (l : List (QuotTestBase r)) : QuotTestBase r

inductive QuotTestRel (r : ∀ ⦃α : Type⦄, List α → List α → Prop) :
    QuotTestBase r → QuotTestBase r → Prop where
  | mk (l l' : List (QuotTestBase r)) (h : r l l')
    (h' : List.Forall₂ (Relation.EqvGen (QuotTestRel r)) l l') : QuotTestRel r (.mk l) (.mk l')

def QuotTest (r : ∀ ⦃α : Type⦄, List α → List α → Prop) : Type :=
  Quot (QuotTestRel r)

instance : Std.Refl (Relation.EqvGen r) := ⟨.refl⟩

def _root_.List.liftQuot {α : Type u} {r : α → α → Prop} (x : List (Quot r)) :
    Quot (List.Forall₂ (Relation.EqvGen r)) :=
  match x with
  | [] => .mk _ []
  | a :: l =>
    a.lift (fun a => l.liftQuot.lift (fun x => Quot.mk _ (a :: x)) ?_) ?_
where finally
  · intro l l' h
    apply Quot.sound
    exact .cons (.refl _) h
  · intro a b h
    cases liftQuot l using Quot.ind with | _ l
    apply Quot.sound
    exact .cons (.rel _ _ h) (List.forall₂_refl l)

#print List.Forall₂

def QuotTest.mk (x : List (QuotTest r)) : QuotTest r :=
  x.liftQuot.lift (fun l => Quot.mk _ (.mk l))
    fun a b h => Quot.sound <| .mk a b _ h

end InductiveToDef
