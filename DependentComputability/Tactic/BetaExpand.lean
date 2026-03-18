import Lean

open Lean

namespace BetaExpand

inductive LCtx where
  | empty
  | cdecl (nm : Name) (bi : BinderInfo) (ty : Expr) (tydeps : Nat) (tail : LCtx)
  | ldecl (nm : Name) (ty : Expr) (tydeps : Nat) (val : Expr) (valdeps : Nat) (tail : LCtx)
with
  @[computed_field] protected hash : LCtx → UInt64
    | .empty => 11
    | .cdecl _ _ ty tymask tail =>
        mixHash (mixHash (hash ty) (hash tymask)) tail.hash
    | .ldecl _ ty tymask val valmask tail =>
      mixHash (mixHash (hash ty) (hash tymask))
        (mixHash (mixHash (hash val) (hash valmask)) tail.hash)

instance : Hashable LCtx where
  hash := LCtx.hash

protected def LCtx.beq (a b : LCtx) : Bool :=
  if unsafe ptrEq a b then true else
  if a.hash != b.hash then false else
  match a, b with
  | .empty, .empty => true
  | .cdecl _ _ ty tymask tail, .cdecl _ _ ty' tymask' tail' =>
    tymask == tymask' && ty == ty' && tail.beq tail'
  | .ldecl _ ty tymask val valmask tail, .ldecl _ ty' tymask' val' valmask' tail' =>
    tymask == tymask' && valmask == valmask' && ty == ty' && val == val' && tail.beq tail'
  | _, _ => false

instance : BEq LCtx where
  beq := LCtx.beq

abbrev M := ReaderT LCtx <| StateM (Std.HashMap (Expr × LCtx) (Expr × Nat))

/-
def theVars (n : Nat) : Array Expr :=
  Array.ofFn fun i : Fin n => .fvar ⟨(`_myvar).num i⟩

def mkLocalContext (x : LCtx) : LocalContext :=
  match x with
  | .empty => {}
  | .cdecl nm bi t _ tail =>
    let lctx := mkLocalContext tail
    let t := t.instantiateRev (theVars lctx.size)
    lctx.mkLocalDecl ⟨(`_myvar).num lctx.size⟩ nm t bi
  | .ldecl nm t _ v _ tail =>
    let lctx := mkLocalContext tail
    let t := t.instantiateRev (theVars lctx.size)
    let v := v.instantiateRev (theVars lctx.size)
    lctx.mkLetDecl ⟨(`_myvar).num lctx.size⟩ nm t v

@[inline]
def liftMetaM (x : MetaM α) : M α := do
  Meta.withLCtx' (mkLocalContext (← read)) x
-/

def LCtx.mkApp (e : Expr) (deps : Nat) (lctx : LCtx) (off : Nat := 0) : Expr :=
  match deps with
  | 0 => e
  | deps + 1 =>
    match lctx with
    | .empty => unreachable!
    | .cdecl (tail := tail) .. => (tail.mkApp e deps (off + 1)).app (.bvar off)
    | .ldecl (tail := tail) .. => tail.mkApp e deps (off + 1)

def LCtx.mkLambda (e : Expr) (deps : Nat) (lctx : LCtx) : Expr :=
  match deps with
  | 0 => e
  | deps + 1 =>
    match lctx with
    | .empty => unreachable!
    | .cdecl nm bi ty _ tail =>
      mkLambda (.lam nm ty e bi) deps tail
    | .ldecl nm ty _ val _ tail =>
      mkLambda (.letE nm ty val e false) deps tail

def LCtx.completeDeps (deps : Nat) (lctx : LCtx) : Nat :=
  match deps with
  | 0 => 0
  | deps + 1 =>
    match lctx with
    | .empty => unreachable!
    | .cdecl _ _ _ tydeps tail => max tydeps (tail.completeDeps deps) + 1
    | .ldecl _ _ tydeps _ valdeps tail => max (max tydeps valdeps) (tail.completeDeps deps) + 1

@[inline]
def mkApp (e : Expr) (mask : Nat) : M Expr := do
  return (← read).mkApp e mask

@[inline]
def mkLambda (e : Expr) (mask : Nat) : M Expr := do
  return (← read).mkLambda e mask

def nonrecBetaExpand (e : Expr) : M (Expr × Nat) := do
  return (e, (← read).completeDeps e.looseBVarRange)

partial def betaLet (e : Expr) (revArgs : Array Expr := #[]) : Expr :=
  match e with
  | .letE _ _ v b _ => betaLet (b.instantiate1 v) revArgs
  | .app f a => betaLet f (revArgs.push a)
  | .lam .. => if revArgs.isEmpty then e else betaLet (e.betaRev revArgs)
  | e => mkAppRev e revArgs

mutual

/--
Returns `(e', n)` such that `e ≡ e'` and `e'` only depends on the first `n` loose bound
variables.
-/
partial def betaExpand (e : Expr) : M (Expr × Nat) := do
  let lctx ← read
  if let some res := (← get)[(e, lctx)]? then
    return res
  let res ← betaExpandCore e
  modify fun cache => cache.insert (e, lctx) res
  --liftMetaM do
    --logInfo m!"orig: {e.instantiateRev (theVars (← getLCtx).size)}"
  --logInfo m!"{← mkLambda res.1 res.2}"
  --Meta.check (← mkLambda res.1 res.2)
  return res

-- Assumption: e has loose bvars
partial def betaExpandCore (e : Expr) : M (Expr × Nat) := do
  match e with
  | .bvar i =>
    return (e, (← read).completeDeps (i + 1))
  | .app f a =>
    let (f, fdeps) ← betaExpand f
    let (a, adeps) ← betaExpand a
    if a.isBVar then
      return (f.app a, max fdeps adeps)
    let a ← mkLambda a adeps
    let a ← mkApp a adeps
    return (f.app a, max fdeps adeps)
  | .lam nm t b bi =>
    let (t, tdeps) ← nonrecBetaExpand t
    let t ← mkLambda t tdeps
    let t ← mkApp t tdeps
    withReader (.cdecl nm bi t tdeps) do
      let (b, bdeps) ← betaExpand b
      return (.lam nm t b bi, max tdeps (bdeps - 1))
  | .forallE .. => nonrecBetaExpand e
  | .letE nm t v b nd =>
    let (t, tdeps) ← nonrecBetaExpand t
    let t ← mkLambda t tdeps
    let t ← mkApp t tdeps
    let (v, vdeps) ← betaExpand v
    let v ← mkLambda v vdeps
    let v ← mkApp v vdeps
    if nd then
      withReader (.cdecl nm .default t tdeps) do
        let (b, bdeps) ← betaExpand b
        return (.letE nm t v b true, max (max tdeps vdeps) (bdeps - 1))
    else
      withReader (.ldecl nm t tdeps v vdeps) do
        let (b, bdeps) ← betaExpand b
        return (.letE nm t v b true, max (max tdeps vdeps) (bdeps - 1))
  | .mdata data e =>
    let (e, mask) ← betaExpand e
    return (.mdata data e, mask)
  | .proj t i e =>
    let (e, mask) ← betaExpand e
    return (.proj t i e, mask)
  | _ => return (e, 0)

end

end BetaExpand

/--
Turns the provided expression into beta-expanded normal form. In beta-expanded normal form, every
application argument that isn't part of a type is either a loose bound variable or a
(possibly nullary) application of a term without loose bound variables.

As an example, the beta-expanded normal form of `fun x => x + 2 * x` is
`fun x => x + (fun x => 2 * x) x`.

The point of beta-expansion is that beta-expanded terms are more resilient to instantiations;
instantiating `x + (fun x => 2 * x) x` with `x := 3` only affects the addition application
but does not have an affect to the multiplication which will only be instantiated lazily,
allowing for more caching opportunities while typechecking.
-/
def betaExpand (e : Expr) : Expr := Id.run do
  (·.1) <$> (BetaExpand.betaExpand e).run .empty |>.run' {}
