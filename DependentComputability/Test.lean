import DependentComputability.ArbitraryDataExtension

def f (n : Nat) : Nat :=
  n * n + 3

def g (n : Nat) : Nat :=
  n + 7

#eval_set n ← IO.rand 3 10

#eval_set a ← pure (f n)
#eval_set b ← pure (g n)

#eval_set x ← return Fin.ofNat (n + 1) (← IO.rand 0 n)

#eval_set _a : Unit ←
  IO.println s!"{n}, {a}, {b}, {x}"

inductive UnitLike (a : Nat) where
  | intro

#print UnitLike.intro.hinj
#check include_str "Test.lean"

/-

aabb 12345 aabb

aabb 341 aabb
-/
