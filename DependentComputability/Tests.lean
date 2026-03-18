import DependentComputability

open Lean
macro "test_many " nm:ident n:num : command => do
  let n := n.getNat
  let names := Array.ofFn fun i : Fin n => mkIdent ((`a).appendIndexAfter (i + 1))
  let body ← names.foldrM (fun id acc => `($id:ident $acc)) (← `(0))
  `(theorem $nm : DComp fun $[$names:ident]* : Nat → Nat => $body := by dcomp_tac)


test_many thm 64

#print thm
convert_to_new thm

#check 0
#print New.thm
