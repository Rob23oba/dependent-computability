import DependentComputability

def testRat (x : Rat) : Rat :=
  (x * 30) ^ 2 - 27

def test (x : Nat) : Nat :=
  (((x / (x + 3) : Rat) * 30) ^ 2 - 27).floor.toNat

set_option Elab.async false in
lemma test_computable : Computable test := by
  have_new hcomp : DComp test := by
    dcomp_tac
  exact hcomp_extra.computable (new% test)

--import DependentComputability

instance {α : Sort u} {α' : new_type% α} {p : α → Prop} {p' : new_type% p}
    [InhabitedExtra α'] [∀ a a', InhabitedExtra (@p' a a')] :
    InhabitedExtra (new% Subtype p) where
  default x := ⟨InhabitedExtra.default x.1, InhabitedExtra.default x.2⟩

@[dcomp]
lemma System.Platform.getNumBits.dcomp {ctx : Sort u}
    (x : ctx → Unit) : DComp (fun c => System.Platform.getNumBits (x c)) := by
  change DComp fun _ => getNumBits ()
  refine Subtype.mk.dcomp ?_
  exact .natLit _

run_meta
  let mod := `Std.Data.DHashMap.Internal.Defs
  let nm := `Std.DHashMap.Internal.Raw₀.expand.go._unary
  let nm := Lean.mkPrivateNameCore mod nm

set_option trace.debug true in
#eval! recAutoDCompMain ``Nat.gcd

#eval! recAutoDCompMain ``Std.DHashMap.contains
#eval! recAutoDCompMain ``Std.DHashMap.insert

#check 0
#print DComp

open Lean
partial def sizeWithCache (e : Expr) : MetaM Nat :=
  (·.2) <$> (go e).run.run 0
where
  go (e : Expr) : MonadCacheT ExprStructEq Unit (StateRefT Nat MetaM) Unit :=
    checkCache { val := e : ExprStructEq } fun _ => do
      modify fun state => state + 1
      match e with
      | .proj _ _ e => go e
      | .app f a => go f; go a
      | .mdata _ e => go e
      | .letE nm t v b nd =>
        go t
        go v
        Meta.withLetDecl nm t v (nondep := nd) fun var =>
          go (b.instantiate1 var)
      | .lam nm t b bi
      | .forallE nm t b bi =>
        go t
        Meta.withLocalDecl nm bi t fun var =>
          go (b.instantiate1 var)
      | _ => pure ()

convert_to_new Std.DHashMap.insert.dcomp

#check ℤ
#print Std.DHashMap.Internal.Raw₀.insert.dcomp

open Lean Parser
run_meta
  modifyEnv (parserExtension.modifyState · fun x => { x with
    tokens :=
      (x.tokens.values.erase "ℤ").foldl (fun acc s => acc.insert s s) {}
  })

#check Int
#print SortExtra

def testRat (x : Rat) : Rat :=
  (x * 30) ^ 2 - 27

def testNat (x : Nat) : Nat :=
  (testRat (x / (x + 3))).floor.toNat

set_option Elab.async false in
lemma testNat_computable : Computable testNat := by
  have_new : DComp testNat := by
    dcomp_tac
  change DComputable _ at this_extra
  rwa [dcomputable_iff_computable (new% testNat)] at this_extra
