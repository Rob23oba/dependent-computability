import DependentComputability.DComp
import DependentComputability.Tactic.ConvertToNew

open Lean Meta Qq

set_option backward.do.legacy false

namespace DCompHelperTheorems

def withManyDependentSorts (n : Nat)
    (k : (u : Level) → Q(Sort u) → Array Expr → MetaM α) : MetaM α :=
  match n with
  | 0 => unreachable!
  | k + 1 =>
    have u_1 : Level := .param `u_1
    withLocalDeclQ `α_1 .implicit q(Sort u_1) fun var => do
      go k _ q($var) #[var]
where
  go (n : Nat) (lastUniv : Level) (lastType : Q(Sort lastUniv)) (acc : Array Expr) : MetaM α :=
    match n with
    | 0 => k lastUniv lastType acc
    | n + 1 =>
      have v : Level := .param <| (`u).appendIndexAfter (acc.size + 1)
      let ty := q($lastType → Sort v)
      withLocalDeclQ ((`α).appendIndexAfter (acc.size + 1)) .implicit ty fun var =>
        go n _ q(PSigma $var) (acc.push var)

def mkBVarLemma (comp : Bool) (priv : Bool) (last : Bool) (n : Nat) : MetaM Name := do
  let root := if comp then ``DComp else ``DPrim
  let baseName := root ++ if last then `bvar_last else `bvar_before
  let baseName := baseName.appendIndexAfter n
  if (← getEnv).contains baseName then
    return baseName
  let privName := mkPrivateName (← getEnv) baseName
  if (← getEnv).contains privName then
    return privName
  let prevLemma ←
    if comp then
      mkBVarLemma false priv last n
    else if last then
      if n = 0 then
        unreachable!
      else
        mkBVarLemma comp priv true (n - 1)
    else
      mkBVarLemma comp priv true n
  let name := if priv then privName else baseName
  let nvars := if last then n + 1 else n + 2
  withManyDependentSorts nvars fun u ctx types => do
    have v : Level := if last then .param `u_1 else .param `u_2
    let proj : Expr := n.repeat (.proj ``PSigma 0) (.bvar 0)
    let projTy : Expr := if last then types[0]! else .app types[1]! (.proj ``PSigma 0 proj)
    let proj := if last then proj else .proj ``PSigma 1 proj
    have projTy : Q($ctx → Sort v) := .lam `c ctx projTy .default
    have projFn : Q((c : $ctx) → $projTy c) := .lam `c ctx proj .default
    let us := List.ofFn fun i : Fin nvars => .param <| (`u).appendIndexAfter (i + 1)
    if comp then
      let type := q(DComp $projFn)
      have proof : Q(DPrim $projFn) := mkAppN (.const prevLemma us) types
      let proof : Q(DComp $projFn) := q(.of_prim $proof)
      addDecl <| .thmDecl {
        name,
        levelParams := List.ofFn fun i : Fin nvars => (`u).appendIndexAfter (i + 1)
        type := ← mkForallFVars types type,
        value := ← mkLambdaFVars types proof
      }
      return name
    let lemmaName := if last then ``PSigma.fst.dprim else ``PSigma.snd.dprim
    have αu : Level := .param `u_1
    have βu : Level := .param `u_2
    have αvar : Q(Sort αu) := types[0]!
    have βvar : Q($αvar → Sort βu) := types[1]!
    let newUs := ql(max (max 1 αu) βu) :: us.tail.tail
    let sigma := q(PSigma $βvar)
    let proof := mkAppN (.app (.const prevLemma newUs) sigma) (types.drop 2)
    let proof := mkApp5 (.const lemmaName [u, αu, βu]) ctx
      q(fun _ : $ctx => $αvar) q(fun _ : $ctx => $βvar)
      (.lam `c ctx proj.projExpr! .default) proof
    addDecl <| .thmDecl {
      name,
      levelParams := List.ofFn fun i : Fin nvars => (`u).appendIndexAfter (i + 1)
      type := ← mkForallFVars types q(DPrim $projFn),
      value := ← mkLambdaFVars types proof
    }
    return name
termination_by if comp then 3 * n + 2 else if last then 3 * n else 3 * n + 1
decreasing_by all_goals grind

end DCompHelperTheorems

lemma DPrim.bvar_last_0 {α : Sort u} : DPrim fun c : α => c := .id
lemma DComp.bvar_last_0 {α : Sort u} : DComp fun c : α => c := .id

-- probably as much as you'll ever need
open DCompHelperTheorems in
run_meta
  for i in *...48 do
    discard <| mkBVarLemma (comp := true) (priv := false) (last := false) i
    discard <| mkBVarLemma (comp := true) (priv := false) (last := true) i
