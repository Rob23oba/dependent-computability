import DependentComputability.DComp

open Lean Meta Qq

set_option backward.do.legacy false

namespace DCompHelperTheorems

def mkForallSortTerm (vars : Array Expr) : Expr :=
  go 0
where
  go (i : Nat) : Expr := Id.run do
    if h : i < vars.size then
      let dom := vars[i]
      let dom := i.foldRev (fun j _ dom => dom.app (.bvar j)) dom
      .forallE ((`a).appendIndexAfter (i + 1)) dom (go (i + 1)) .default
    else
      .sort (.param ((`u).appendIndexAfter (i + 1)))

def mkLambdaTerm (vars : Array Expr) (inner : Expr) : Expr :=
  go 0
where
  go (i : Nat) : Expr := Id.run do
    if h : i < vars.size then
      let dom := vars[i]
      let dom := i.foldRev (fun j _ dom => dom.app (.bvar j)) dom
      .lam ((`a).appendIndexAfter (i + 1)) dom (go (i + 1)) .default
    else
      inner

def mkForallFunctionTerm (vars : Array Expr) (body : Expr) : Expr :=
  go 0
where
  go (i : Nat) : Expr := Id.run do
    if h : i < vars.size then
      let dom := vars[i]
      let dom := i.foldRev (fun j _ dom => dom.app (.bvar j)) dom
      .forallE ((`a).appendIndexAfter (i + 1)) dom (go (i + 1)) .default
    else
      i.foldRev (fun j _ dom => dom.app (.bvar j)) body

def mkPSigmaN (vars : Array Expr) : Expr × Level :=
  go 0
where
  go (i : Nat) : Expr × Level := Id.run do
    if h : i + 1 < vars.size then
      let dom := vars[i]
      let dom := i.foldRev (fun j _ dom => dom.app (.bvar j)) dom
      let u := .param ((`u).appendIndexAfter (i + 1))
      let (e, v) := go (i + 1)
      let nm := (`a).appendIndexAfter (i + 1)
      (mkApp2 (.const ``PSigma [u, v]) dom (.lam nm dom e .default),
        if i + 2 < vars.size then u.max v else .max (.max 1 u) v)
    else if h : i < vars.size then
      let body := vars[i]
      let body := i.foldRev (fun j _ dom => dom.app (.bvar j)) body
      let u := .param ((`u).appendIndexAfter (i + 1))
      return (body, u)
    else
      unreachable!

#print PSigma

def withManyDependentSorts (n : Nat) (k : Array Expr → MetaM α) : MetaM α :=
  go n #[]
where
  go (n : Nat) (acc : Array Expr) : MetaM α :=
    match n with
    | 0 => k acc
    | n + 1 =>
      withLocalDecl ((`α).appendIndexAfter (acc.size + 1)) .implicit (mkForallSortTerm acc)
          fun var => go n (acc.push var)

open Qq in
def compressNaryFun {clvl : Level} (ctx : Q(Sort clvl))
    (f : Expr) (n : Nat) (last : Bool) : Expr := Id.run do
  assert! n ≠ 0 ∨ ¬last
  if n = 1 ∧ last then
    return f
  let mut e := f
  let mut base := .bvar 0
  if last then
    for _ in 1...n do
      e := e.app (.proj ``PSigma 0 base)
      base := base.proj ``PSigma 1
    e := e.app base
    return .lam `c ctx e .default
  else
    for _ in *...n do
      e := e.app (.proj ``PSigma 0 base)
      base := base.proj ``PSigma 1
    return .lam `c ctx e .default

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
  withManyDependentSorts nvars fun types => do
    let (ctx, u) := mkPSigmaN types
    have ctx : Q(Sort u) := ctx
    let v := .param ((`u).appendIndexAfter (n + 1))
    let proj : Expr := n.repeat (.proj ``PSigma 1) (.bvar 0)
    let proj := if last then proj else .proj ``PSigma 0 proj
    let type := mkApp3 (.const root [u, v]) ctx (compressNaryFun q($ctx) types[n]! n false)
      (.lam `c ctx proj .default)
    if comp then
      let us := List.ofFn fun i : Fin nvars => .param <| (`u).appendIndexAfter (i + 1)
      let proof := mkAppN (.const prevLemma us) types
      let proof := mkApp4 (.const ``DComp.of_prim [u, v]) ctx
        (compressNaryFun q($ctx) types[n]! n false) (.lam `c ctx proj .default) proof
      addDecl <| .thmDecl {
        name,
        levelParams := List.ofFn fun i : Fin nvars => (`u).appendIndexAfter (i + 1)
        type := ← mkForallFVars types type,
        value := ← mkLambdaFVars types proof
      }
      return name
    let lemmaName := if last then ``PSigma.snd.dprim else ``PSigma.fst.dprim
    let αvar := types[nvars - 2]!
    let βvar := types[nvars - 1]!
    let αu := .param <| (`u).appendIndexAfter (nvars - 1)
    let βu := .param <| (`u).appendIndexAfter nvars
    let newUs := List.ofFn fun i : Fin (nvars - 2) =>
      .param <| (`u).appendIndexAfter (i + 1)
    let newUs := newUs ++ [.max (.max 1 αu) βu]
    let αapp := (nvars - 2).foldRev (fun j _ dom => dom.app (.bvar j)) αvar
    let βapp := (nvars - 2).foldRev (fun j _ dom => dom.app (.bvar j)) βvar
    let sigma := mkApp2 (.const ``PSigma [αu, βu]) αapp βapp
    let sigma := mkLambdaTerm (types.take (nvars - 2)) sigma
    let proof := .app (mkAppN (.const prevLemma newUs) (types.take (nvars - 2))) sigma
    let proof := mkApp5 (.const lemmaName [u, αu, βu]) ctx
      (compressNaryFun q($ctx) αvar (nvars - 2) false)
      (compressNaryFun q($ctx) βvar (nvars - 2) false)
      (.lam `c ctx proj.projExpr! .default) proof
    addDecl <| .thmDecl {
      name,
      levelParams := List.ofFn fun i : Fin nvars => (`u).appendIndexAfter (i + 1)
      type := ← mkForallFVars types type,
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
  for i in *...32 do
    discard <| mkBVarLemma (comp := true) (priv := false) (last := false) i
    discard <| mkBVarLemma (comp := true) (priv := false) (last := true) i
#check 0

#check DPrim.bvar_last_15
#check DPrim.bvar_last_15
