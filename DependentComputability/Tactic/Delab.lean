import DependentComputability.SortExtra

namespace Delab

open Lean PrettyPrinter Delaborator SubExpr Meta

partial def convertBackFromNew (e : Expr) : OptionT MetaM Expr := do
  match e with
  | .lam nm' t_base (.lam nm t b bi) bi' =>
    withLocalDecl nm' bi' t_base fun var_base => do
    withLocalDecl nm bi (t.instantiate1 var_base) fun var => do
      let res ← convertBackFromNew (b.instantiate #[var_base, var])
      if res.hasAnyFVar (· == var.fvarId!) then failure
      mkLambdaFVars #[var_base] res
  | .letE nm' t_base v_base (.letE nm t v b nd) nd' =>
    withLetDecl nm' t_base v_base fun var_base => do
    withLetDecl nm (t.instantiate1 var_base) (v.instantiate1 var_base) fun var => do
      let res ← convertBackFromNew (b.instantiate #[var_base, var])
      if res.hasAnyFVar (· == var.fvarId!) then failure
      return .letE nm t_base v_base (res.abstract #[var_base]) nd
  | .const nm us =>
    let some nm := (`New).isPrefixOf? nm | failure
    if nm = `Sort then
      let [u] := us | failure
      return .sort u
    unless (← getEnv).contains nm do failure
    return .const nm us
  | .app .. =>
    e.withApp fun fn args => do
      if ¬2 ∣ args.size then failure
      if let .const ``New.Forall .. := fn then
        let #[_α_base, _α, .lam nm t_base b_base bi, _β_base] := args | failure
        return .forallE nm t_base b_base bi
      else if let .const `uniqueNatLit .. := fn then
        let #[n] := args | failure
        return n
      else if let .const `uniqueStrLit .. := fn then
        let #[s] := args | failure
        return s
      let mut expr ← convertBackFromNew fn
      for h : i in *...(args.size/2) do
        have : i < args.size/2 := h
        expr := expr.app args[i * 2]
      return expr
  | .fvar var =>
    let mkExtraApp _ e ← var.getType | failure
    return e
  | .bvar i => failure
  | _ => failure

@[scoped delab app]
def delabNew : Delab := whenNotPPOption getPPExplicit do
  let e ← getExpr
  if let mkExtraApp _ e := e then
    withTheReader SubExpr (fun x => { x with expr := e, pos := x.pos.push 0 }) do
    let stx ← delab
    `(new_type% $stx)
  else
    let some res ← (convertBackFromNew e).run | failure
    withTheReader SubExpr (fun x => { x with expr := res, pos := x.pos.push 0 }) do
      let stx ← delab
      `(new% $stx)

end Delab
