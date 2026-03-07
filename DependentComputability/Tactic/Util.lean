import Qq

open Lean Meta Qq

def Qq.matchForallQ (e : Expr) : MetaM (Option ((u v : Level) × (α : Q(Sort u)) × Q($α → Sort v))) := do
  let .forallE nm t b bi := id e | return none
  let u ← getLevel t
  have t : Q(Sort u) := t
  withLocalDeclQ nm bi q($t) fun x => do
    let v ← getLevel (b.instantiate1 x)
    return some ⟨u, v, q($t), .lam nm t b bi⟩

def Qq.matchLambdaQ (e : Expr) : MetaM (Option ((u v : Level) × (α : Q(Sort u)) × (β : Q($α → Sort v)) × Q((a : $α) → $β a))) := do
  let .lam nm t b bi := e | return none
  let u ← getLevel t
  have t : Q(Sort u) := t
  withLocalDeclQ nm bi q($t) fun x => do
    let bty ← inferType (b.instantiate1 x)
    let v ← getLevel bty
    return some ⟨u, v, q($t), .lam nm t (bty.abstract #[x]) bi, e⟩

@[inline]
def Qq.isAlwaysZeroQ (lvl : Level) : MaybeLevelDefEq lvl Level.zero :=
  if lvl.isAlwaysZero then
    .defEq ⟨⟩
  else
    .notDefEq

@[inline]
def Qq.withLetDeclQ [MonadControlT MetaM n] [Monad n]
    (name : Name) {type : Q(Sort u)} (val : Q($type))
    (k : (var : Q($type)) → $var =Q $val → n α) : n α :=
  withLetDecl name type val (fun e => k e ⟨⟩)

@[inline]
def Qq.withHaveDeclQ [MonadControlT MetaM n] [Monad n]
    (name : Name) {type : Q(Sort u)} (val : Q($type))
    (k : (var : Q($type)) → n α) : n α :=
  withLetDecl name type val k (nondep := true)

/-- Returns whether the recursor has large elimination, i.e. whether it can eliminate into any universe. -/
def Lean.RecursorVal.largeElim (val : RecursorVal) : Bool :=
  go val.numParams val.type
where
  go : Nat → Expr → Bool
    | 0, .forallE _ t _ _ => (t.getForallBody matches .sort (.param _))
    | k + 1, .forallE _ _ b _ => go k b
    | _, _ => false

set_option doc.verso true in
/--
Returns a list of all recursors mutual with this one.
See also {name}`RecursorVal.all` which produces a list of inductives.
-/
def Lean.RecursorVal.allRecs (val : RecursorVal) : List Name := Id.run do
  let fst :: more := val.all | return []
  let numNested := val.numMotives - val.all.length
  let fstRec := mkRecName fst
  return fstRec :: (more.map mkRecName ++ (List.range' 1 numNested).map fstRec.appendIndexAfter)

local syntax (name := matchQqConstApp) "match_qq_const_app" term:arg term:arg term:arg* ";" term:arg term:arg : term
local syntax (name := doMatchQqConstApp) "match_qq_const_app" term:arg term:arg term:arg* ";" doSeq doSeq : doElem

set_option backward.do.legacy false
open Elab Term
elab_rules : term <= exp
  | `(match_qq_const_app $x:term $fn:term $args:term*; $alt:term $default:term) => do
    let (ident, explicit, levels) ← match fn with
      | `($id:ident) => pure (id, false, #[])
      | `(@$id:ident) => pure (id, true, #[])
      | `($id:ident.{$us,*}) => pure (id, false, us.getElems)
      | `(@$id:ident.{$us,*}) => pure (id, true, us.getElems)
      | _ => throwErrorAt fn "Invalid raw Qq match, expected identifier"
    let levels ← levels.mapM fun lvl => match lvl with
      | `($id:ident) => pure id
      | `(_) => withFreshMacroScope `(u)
      | _ => throwErrorAt lvl "Invalid pattern, expected identifier"
    let args ← args.mapM fun arg => match arg with
      | `($id:ident) => pure id
      | `(_) => withFreshMacroScope `(x)
      | _ => throwErrorAt arg "Invalid pattern, expected identifier"
    let nm ← realizeGlobalConstNoOverloadWithInfo ident
    let info ← withRef fn <| getConstVal nm
    if levels.size > info.levelParams.length then
      throwErrorAt (mkNullNode (levels.drop info.levelParams.length)) "Too many level parameters"
    let mut levels := levels
    while levels.size < info.levelParams.length do
      levels := levels.push (← withFreshMacroScope `(ident| u))
    let quotedType ← forallBoundedTelescope info.type args.size fun vars body => do
      if args.size > vars.size then
        throwErrorAt (mkNullNode (args.drop vars.size)) "Too many arguments"
      let levelVarInfos := levels.map (fun x => (x.getId, q(Level)))
      withLocalDeclsDND levelVarInfos fun levelVars => do
      let rec go (i : Nat) (qqVars : Array Expr) : Impl.QuoteM Expr := do
        if h : i < vars.size then
          let decl ← vars[i].fvarId!.getDecl
          let qqVarType : Q(Expr) ← Impl.quoteExpr decl.type
          let qqVarType := q(Quoted $qqVarType)
          withLocalDeclD args[i]!.getId qqVarType fun qqVar => do
            withReader (fun state => { state with exprBackSubst := state.exprBackSubst.insert decl.toExpr (.quoted qqVar) }) do
              go (i + 1) (qqVars.push qqVar)
        else
          let qqResType : Q(Expr) ← Impl.quoteExpr body
          let qqResLevel : Q(Level) ← Impl.quoteLevel (← getLevel body)
          let qqApp : Q(Expr) ← Impl.quoteExpr (mkAppN (.const nm (info.levelParams.map Level.param)) vars)
          mkLambdaFVars qqVars q(($qqResType, $qqResLevel, $qqApp))
      let mut levelBackSubst : Std.HashMap Level Expr := {}
      for param in info.levelParams, var in levelVars do
        levelBackSubst := levelBackSubst.insert (.param param) var
      let ctx := {
        mayPostpone := false
        levelNames := levels.map (·.getId) |>.toList
        levelBackSubst
      }
      (go 0 levelVars).run ctx
    let discr ← elabTermEnsuringTypeQ x q(Expr)
    let (altBranch, altType) ← lambdaTelescope quotedType fun qqVars qqBody => do
      for lvl in levels, qqVar in qqVars do
        addTermInfo' (isBinder := true) lvl qqVar
      for arg in args, qqVar in qqVars[levels.size...*] do
        addTermInfo' (isBinder := true) arg qqVar
      if let `($id:ident) := x then
        let_expr Prod.mk _ _ resType more := qqBody | unreachable!
        let_expr Prod.mk _ _ resLvl resVal := more | unreachable!
        have resLvl : Q(Level) := resLvl
        have resType : Q(Quoted (.sort $resLvl)) := resType
        have resVal : Q(Quoted $resType) := resVal
        withHaveDeclQ id.getId (type := q(Quoted $resType)) discr fun var => do
        let eqName ← mkFreshUserName (id.getId.appendAfter "_eq")
        have discr : Q(Quoted $resType) := var
        withHaveDeclQ eqName (type := q(@QuotedDefEq $resLvl (Quoted.unsafeMk $resType) (Quoted.unsafeMk $discr) (Quoted.unsafeMk $resVal))) q(.unsafeIntro) fun eqVar => do
          let res ← elabTermEnsuringType alt exp
          let qqVars' := qqVars.push var |>.push eqVar
          return (← mkLetFVars qqVars' res (generalizeNondepLet := false), ← mkForallFVars qqVars exp)
      else
        let res ← elabTermEnsuringType alt exp
        return (← mkLambdaFVars qqVars res, ← mkForallFVars qqVars exp)
    let expLevel ← getLevel exp
    have exp : Q(Sort expLevel) := exp
    let defaultBranch : Q($exp) ← elabTermEnsuringType default exp
    let defaultBranch := q(fun _ : Unit => $defaultBranch)
    withLetDecl `alt altType altBranch (nondep := true) fun altBranch => do
    withLetDecl `default q(Unit → $exp) defaultBranch (nondep := true) fun (defaultBranch : Q(Unit → $exp)) => do
      let rec goLevels (discr : Q(List Level)) (revArgs : Array Q(Expr)) (levelVars : Array Q(Level)) (i : Nat) : MetaM Q($exp) := do
        if h : i < levels.size then
          let further : Q(Level → List Level → $exp) ← withLocalDeclD `u q(Level) fun uvar => do
            withLocalDeclD `us q(List Level) fun usvar => do
              let res ← goLevels usvar revArgs (levelVars.push uvar) (i + 1)
              mkLambdaFVars #[uvar, usvar] res
          return q(($discr).casesOn ($defaultBranch ()) $further)
        else
          have res : Q($exp) := mkAppRev (mkAppN altBranch levelVars) revArgs
          return q(($discr).casesOn $res (fun _ _ => $defaultBranch ()))
      termination_by levels.size - i
      let rec goMatch (discr : Q(Expr)) (revArgs : Array Q(Expr)) (n : Nat) : MetaM Q($exp) := do
        match n with
        | 0 =>
          let further : Q(List Level → $exp) ← withLocalDeclD `lvls q(List Level) fun lvlsVar => do
            let res ← goLevels lvlsVar revArgs #[] 0
            mkLambdaFVars #[lvlsVar] res
          have nm : Name := nm
          return q(
            if h : ($discr).isConstOf $nm then
              have lvls := ($discr).constLevels!
              $further lvls
            else $defaultBranch ())
        | n + 1 =>
          let further : Q(Expr → Expr → $exp) ← withLocalDeclD `fn q(Expr) fun fnVar => do
            withLocalDeclD `arg q(Expr) fun argVar => do
              let res ← goMatch fnVar (revArgs.push argVar) n
              mkLambdaFVars #[fnVar, argVar] res
          return q(
            if h : ($discr).isApp then
              have fn := ($discr).appFn h
              have arg := ($discr).appArg h
              $further fn arg
            else $defaultBranch ())
      let res ← goMatch discr #[] args.size
      mkLetFVars #[altBranch, defaultBranch] res (generalizeNondepLet := false)

macro_rules
  | `(match $x:term with | q($fn $args*) => $alt:term | _ => $default:term) => do
    let args ← args.mapM fun stx => do
      let stx := stx.raw
      if stx.isAntiquot && !stx.isEscapedAntiquot then
        return ⟨stx.getAntiquotTerm⟩
      else
        Macro.throwUnsupported
    `(match_qq_const_app $x:term $fn:term $args:term*; $alt:term $default:term)

open Elab Parser Term Do in
@[doElem_elab doMatchQqConstApp]
def elabDoMatchQqConstApp : DoElab := fun stx dec => do
  let `(doElem| match_qq_const_app $x:term $fn:term $args:term*; $alt:doSeq $default:doSeq) := stx |
    throwUnsupportedSyntax
  let doBlockResultType := (← read).doBlockResultType
  let mγ ← mkMonadicType doBlockResultType
  let info ← inferControlInfoElem stx
  dec.withDuplicableCont info fun dec => do
  let mut argsIdents ← args.filterMapM fun arg => match arg with
    | `($id:ident) => pure (some id)
    | `(_) => pure none
    | _ => throwErrorAt arg "Invalid pattern, expected identifier"
  if let `($id:ident) := x then
    argsIdents := argsIdents.push id
  checkMutVarsForShadowing argsIdents
  doElabToSyntax m!"match_qq_const_app alternative" (ref := alt) (elabDoSeq alt dec) fun alt => do
  doElabToSyntax m!"match_qq_const_app alternative" (ref := default) (elabDoSeq default dec) fun default => do
    Term.elabTerm (← `(match_qq_const_app $x:term $fn:term $args:term*; $alt:term $default:term)) mγ

open Elab Do in
@[doElem_control_info doMatchQqConstApp]
def doMatchQqConstAppControlInfo : ControlInfoHandler := fun stx => do
  let `(doElem| match_qq_const_app $_:term $_:term $_:term*; $alt:doSeq $default:doSeq) := stx |
    throwUnsupportedSyntax
  return (← inferControlInfoSeq alt).alternative (← inferControlInfoSeq default)

macro_rules
  | `(doElem| match $x:term with | q($fn $args*) => $alt:doSeq | _ => $default:doSeq) => do
    let args ← args.mapM fun stx => do
      let stx := stx.raw
      if stx.isAntiquot && !stx.isEscapedAntiquot then
        return ⟨stx.getAntiquotTerm⟩
      else
        Macro.throwUnsupported
    `(doElem| match_qq_const_app $x:term $fn:term $args:term*; $alt:doSeq $default:doSeq)

macro_rules
  | `(doElem| let q($fn $args*) := $x:term | $otherwise $(body?)?) => do
    let body ← body?.getDM `(Parser.Term.doSeqIndent| pure PUnit.unit)
    let args ← args.mapM fun stx => do
      let stx := stx.raw
      if stx.isAntiquot && !stx.isEscapedAntiquot then
        return ⟨stx.getAntiquotTerm⟩
      else
        Macro.throwUnsupported
    `(doElem| match_qq_const_app $x:term $fn:term $args:term*; $body:doSeqIndent $otherwise:doSeqIndent)
