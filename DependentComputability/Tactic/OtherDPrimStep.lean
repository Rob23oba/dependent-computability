import DependentComputability.Tactic.DCompHelperLemmas2
import DependentComputability.Tactic.Util

namespace DPrimrec.Tactic.Other

open Lean Meta Elab Term Tactic Qq

def projToFn (x : Expr) : MetaM Expr := do
  if let .proj t i e := x then
    if t == ``PSigma then
      let name ← match i with
        | 0 => pure ``PSigma.fst
        | 1 => pure ``PSigma.snd
        | _ => throwError "bad projection: field index {i} out of bounds for type {t}"
      let type ← inferType e
      let type ← whnfD type
      type.withApp fun c args => do
        unless c.isConstOf t do
          throwError "bad projection: structure type name mismatch"
        return .app (mkAppN (.const name c.constLevels!) args) e
    else
      projToRec t i e
  else
    return x

inductive ParamComputability where
  | always
  | prim
  | computable

structure TheoremInfo where
  prim : Bool
  declName : Name
  thmName : Name
  paramInfos : Array ParamComputability

structure DPrimTheorems where
  primTheorems : NameMap TheoremInfo := {}
  compTheorems : NameMap TheoremInfo := {}
deriving Inhabited

def DPrimTheorems.add (ths : DPrimTheorems) (th : TheoremInfo) : DPrimTheorems :=
  if th.prim then
    { ths with primTheorems := ths.primTheorems.insert th.declName th }
  else
    { ths with compTheorems := ths.compTheorems.insert th.declName th }

initialize otherDPrimExt : SimplePersistentEnvExtension TheoremInfo DPrimTheorems ←
  registerSimplePersistentEnvExtension {
    addEntryFn := DPrimTheorems.add
    addImportedFn xss :=
      xss.foldl (init := {}) fun acc xs => xs.foldl (init := acc)
        fun acc x => acc.add x
  }

def hasDPrimThm (nm : Name) : CoreM Bool := do
  return (otherDPrimExt.getState (← getEnv)).primTheorems.contains nm

def hasDCompThm (nm : Name) : CoreM Bool := do
  return (otherDPrimExt.getState (← getEnv)).compTheorems.contains nm

def mkOtherThmEntry (thm : Name) : MetaM TheoremInfo := do
  let val ← getConstVal thm
  forallTelescope val.type fun xs body => do
    let mkApp3 (.const thing [clvl, rlvl]) ctx α f := body |
      throwError "invalid `other_dprim` attribute, conclusion is not DPrim or DComp"
    let prim ← match thing with
      | ``DPrim => pure true
      | ``DComp => pure false
      | _ => throwError "invalid `other_dprim` attribute, conclusion is not DPrim or DComp"
    let .lam nm _ b bi ← whnfR f |
      throwError "invalid `other_dprim` attribute, conclusion doesn't have a lambda"
    b.withApp fun x args => do
      let .const cnm lvls := x |
        throwError "invalid `other_dprim` attribute, conclusion must be a const"
      unless lvls == val.levelParams.tail.map Level.param do
        throwError "invalid `other_dprim` attribute, bad level parameters"
      unless ctx == xs[0]! do
        throwError "expected context parameter {ctx} but found {xs[0]!}"
      let mut map : Array ParamComputability := #[]
      let mut j := 1
      for h : i in *...args.size do
        let arg := args[i]
        if h : j < xs.size then
          let var := xs[j]
          unless arg.eta == var.app (.bvar 0) do
            throwError "invalid `other_dprim` attribute, parameter #{i} is \
              {Expr.lam nm ctx arg bi} and not {var} as expected"
          if h : j + 1 < xs.size then
            let x := xs[j + 1]
            let ty ← inferType x
            if ty.isAppOf ``DComp then
              map := map.push .computable
              j := j + 2
            else if ty.isAppOf ``DPrim then
              map := map.push .prim
              j := j + 2
            else
              map := map.push .always
              j := j + 1
          else
            map := map.push .always
            j := j + 1
        else
          throwError "invalid `other_dprim` attribute, parameter #{i} out of range"
      return {
        prim
        declName := cnm
        thmName := thm
        paramInfos := map
      }

initialize
  registerBuiltinAttribute {
    name := `other_dprim
    descr := "Attribute for `other_dcomp_tac`"
    add nm stx kind := do
      let entry ← MetaM.run' (mkOtherThmEntry nm)
      modifyEnv (otherDPrimExt.addEntry · entry)
  }

def idLemma (prim : Bool) : Name :=
  if prim then ``DPrim.id else ``DComp.id

def sortLemma (prim : Bool) : Name :=
  if prim then ``DPrim.sort else ``DComp.sort

def natLitLemma (prim : Bool) : Name :=
  if prim then `DPrim.natLit else `DComp.natLit

def strLitLemma (prim : Bool) : Name :=
  if prim then `DPrim.strLit else `DComp.strLit

def mkPred (prim : Bool) {u v : Level} {α : Q(Sort u)} {β : Q($α → Sort v)}
    (f : Q((a : $α) → $β a)) : Q(Prop) :=
  if prim then
    q(DPrim $f)
  else
    q(DComp $f)

partial def whnfFast (e : Expr) (zeta : Bool) (argsRev : Array Expr := #[]) : MetaM Expr := do
  match e with
  | .app f a => whnfFast f zeta (argsRev.push a)
  | .mdata _ e => whnfFast e zeta argsRev
  | .lam .. => if argsRev.isEmpty then return e else whnfFast (e.betaRev argsRev) zeta
  | .letE _ _ v b _ =>
    if zeta then
      whnfFast (b.instantiate1 v) zeta argsRev
    else
      return argsRev.foldr (fun a f => f.app a) e
  | _ => return argsRev.foldr (fun a f => f.app a) e

structure LocalThm where
  value : Expr
  paramInfos : Array ParamComputability

def LocalThm.instantiate (thm : LocalThm) (univ : Name) (clvl : Level) (ctx : Expr) : Expr :=
  let repl (lvl : Name) : Option Level := if lvl = univ then clvl else none
  (thm.value.instantiateLevelParamsCore repl).betaRev #[ctx]

structure Context where
  contextUniv : Name
  localPrimThms : FVarIdMap LocalThm
  localCompThms : FVarIdMap LocalThm
  zeta : Bool

abbrev M := ReaderT Context <| MetaM

instance : Inhabited (M α) := ⟨(default : MetaM _)⟩

@[inline]
def withBasicLocalThm (prim : Bool) {clvl tlvl : Level}
    {ctx : Q(Sort clvl)} {res_lam : Q($ctx → Sort tlvl)}
    {val : Q((a : $ctx) → $res_lam a)} (val_comp : Q($(mkPred prim val)))
    (act : M α) : M α := do
  withReader newContext act
where
  newContext (c : Context) : Context :=
    have u := Level.param c.contextUniv
    match prim with
    | true =>
      let value1 := q(@DPrim.comp.{u} _ _ _ $val_comp)
      let value2 := q(@DPrim.compComputable.{u} _ _ _ $val_comp)
      let thm1 : LocalThm := { value := by exact value1, paramInfos := #[.prim] }
      let thm2 : LocalThm := { value := by exact value2, paramInfos := #[.computable] }
      { c with localPrimThms := c.localPrimThms.insert val.fvarId! thm1,
               localCompThms := c.localCompThms.insert val.fvarId! thm2 }
    | false =>
      let value := q(@DComp.comp.{u} _ _ _ $val_comp)
      let thm : LocalThm := { value := by exact value, paramInfos := #[.computable] }
      { c with localCompThms := c.localCompThms.insert val.fvarId! thm }

def getRawForallArity (e : Expr) : Nat :=
  go e 0
where
  go (e : Expr) (acc : Nat) : Nat :=
    match e with
    | .forallE _ _ b _ => go b (acc + 1)
    | _ => acc

set_option backward.do.legacy false

def checkIrrel (ty : Expr) : Bool :=
  match ty with
  | .sort _ => true
  | .forallE _ _ b _ => checkIrrel b
  | .lam _ _ b _ => checkIrrel b
  | .app f _ => checkIrrel f
  | _ => false

partial def isTriviallyIrrelevant (e : Expr) : MetaM <| Option (Level × Expr) := do
  if let .sort u := e then
    return some ⟨u.succ, q(instIrrelSort.{u})⟩
  else if let .forallE nm t b bi := id e then
    withLocalDecl nm bi t fun var => do
      let some ⟨v, irrel⟩ ← isTriviallyIrrelevant (b.instantiate1 var) | return none
      let ⟨u, t⟩ ← getLevelQ t
      have blam : Q($t → Sort v) := .lam nm t b bi
      let _irrel : Q((x : $t) → Irrel ($blam x)) ← mkLambdaFVars #[var] irrel
      return some ⟨u.imax v, q(@instIrrelForall $t $blam _)⟩
  else
    return none

def isBVarProjCont (e : Expr) : Bool :=
  match e with
  | .proj ``PSigma 0 e => isBVarProjCont e
  | .bvar 0 => true
  | _ => false

def isBVarProj (e : Expr) : Bool :=
  match e with
  | .proj ``PSigma 0 e | .proj ``PSigma 1 e =>
    isBVarProjCont e
  | _ => false

def extractBetasFromPSigma (ty : Expr) (n : Nat) (us : List Level := [])
    (revArgs : Array Expr := #[]) : MetaM (List Level × Array Expr) := do
  let n + 1 := n | unreachable!
  let ty ← if ty.isAppOfArity ``PSigma 2 then pure ty else whnf ty
  let q(PSigma.{u, v} $α $β) := ty | throwError "Internal error in other_dcomp_tac"
  if n = 1 then
    return (u :: v :: us, revArgs.push β |>.push α)
  extractBetasFromPSigma α n (v :: us) (revArgs.push β)

def mkBVarProjProof (prim : Bool) (ctx : Expr) (b : Expr) : MetaM Expr := do
  let mut b := b
  let mut last := true
  if let .proj ``PSigma 1 e := b then
    b := e
    last := false
  let mut n := 0
  repeat
    if let .proj ``PSigma 0 e := b then
      b := e
      n := n + 1
    else
      break
  assert! b matches .bvar 0
  let thm ← DCompHelperTheorems.mkBVarLemma (comp := !prim) (priv := true) last n
  let (us, revArgs) ← extractBetasFromPSigma ctx (if last then n + 1 else n + 2)
  return mkAppRev (.const thm us) revArgs

mutual
partial def handleUnderApplication (prim : Bool) {clvl rlvl : Level}
    {ctx : Q(Sort clvl)} {res : Q($ctx → Sort rlvl)} (f : Q((a : $ctx) → $res a)) :
    M Q($(mkPred prim f)) := do
  let .lam nm _ b bi := id f | unreachable!
  let (t', t'lvl, b', b'lvl) ← withLocalDeclQ nm bi q($ctx) fun ctx_var => do
    let ty ← inferType (b.instantiate1 ctx_var)
    let .forallE nm' t' b' bi' ← whnf ty |
      throwError "function expected for type {ty} but we have {b.instantiate1 ctx_var}"
    let t'lvl ← getLevel t'
    trace[debug] "under-application: {b.instantiate1 ctx_var} has type {ty} : Sort {t'lvl}"
    let b'lvl ← withLocalDecl nm' bi' t' (getLevel <| b'.instantiate1 ·)
    let t'lam := Expr.lam nm ctx (t'.abstract #[ctx_var]) bi
    let b'lam := Expr.lam nm ctx ((Expr.lam nm' t' b' bi').abstract #[ctx_var]) bi
    pure (t'lam.abstract #[ctx_var], t'lvl, b'lam, b'lvl)
  have t' : Q($ctx → Sort t'lvl) := t'
  have b' : Q((c : $ctx) → $t' c → Sort b'lvl) := b'
  have : rlvl =QL imax t'lvl b'lvl := ⟨⟩
  have : $res =Q fun c => (x : $t' c) → $b' c x := ⟨⟩
  let f' : Q((x : PSigma $t') → $b' x.1 x.2) := .lam `c q(PSigma $t')
    (Impl.betaRev' f [.proj ``PSigma 1 (.bvar 0), .proj ``PSigma 0 (.bvar 0)]) .default
  let proof ← solveDPrimGoal false q($f')
  return match prim with
  | true | false => q(.curry $proof)

partial def handleOverApplication
    (prim : Bool) {clvl rlvl : Level} {ctx : Q(Sort clvl)} {res : Q($ctx → Sort rlvl)}
    (f : Q((a : $ctx) → $res a)) (b val : Expr) (overArgs : Subarray Expr) :
    M Expr := do
  if overArgs.isEmpty then
    return val
  let .lam nm _ _ bi := id f | unreachable!
  let false := prim |
    try
      return ← handleUnderApplication prim q($f)
    catch _ =>
      withLocalDecl nm bi ctx fun var => do
        throwError "invalid over-application in primrec goal: \
          expected at most {overArgs.start} arguments but found {overArgs.stop} in\
          {indentExpr <| b.instantiate1 var}"
  let mut type ←
    withLocalDeclQ nm bi q($ctx) fun var => do
      let mut type ← inferType (b.instantiate1 var)
      if getRawForallArity type < overArgs.size then
        type ← liftM <| forallBoundedTelescope type (some overArgs.size) mkForallFVars
      return type.abstract #[var]
  let mut b := b
  let mut val := val
  for arg in overArgs do
    let .forallE nm' t' b' bi' := id type |
      withLocalDecl nm bi ctx fun var =>
        throwError "function expected at{indentExpr (b.instantiate1 var)}\n\
          but found type{indentExpr (type.instantiate1 var)}"
    let t'lvl ← withLocalDecl nm bi ctx fun var => getLevel (t'.instantiate1 var)
    let b'lvl ← withLocalDecl nm bi ctx fun var =>
      withLocalDecl nm' bi' (t'.instantiate1 var) fun var' =>
        getLevel (b'.instantiateRev #[var, var'])
    have t'lam : Q($ctx → Sort t'lvl) := .lam nm ctx t' bi
    have b'lam : Q((c : $ctx) → $t'lam c → Sort b'lvl) :=
      .lam nm ctx (.lam nm' t' b' bi') bi
    have bLambda : Q((c : $ctx) → (a : $t'lam c) → $b'lam c a) := .lam nm ctx b bi
    have argLambda : Q((c : $ctx) → $t'lam c) := .lam nm ctx arg bi
    have val' : Q(DComp $bLambda) := val
    let argProof ← solveDPrimGoal false q($argLambda)
    val := q(DComp.app $val' $argProof)
    type := b'.instantiate1 arg
    b := b.app arg
  return val

-- assumes that `f` is a lambda
partial def solveDPrimGoal (prim : Bool) {clvl rlvl : Level}
    {ctx : Q(Sort clvl)} {res : Q($ctx → Sort rlvl)}
    (f : Q((a : $ctx) → $res a)) :
    M Q($(mkPred prim f)) := withIncRecDepth do
  withTraceNode `debug (return m!"{exceptEmoji ·} trying to solve goal{indentExpr f}") do
  if let .defEq _ := isAlwaysZeroQ rlvl then
    return match prim with
    | true | false => q(.proof)
  let .lam nm _ b bi := id f | unreachable!
  if checkIrrel res then
    return ← withLocalDeclD `c ctx fun var => do
      let some ⟨_, irrel⟩ ← isTriviallyIrrelevant (res.betaRev #[var]) | unreachable!
      let _irrel : Q((x : $ctx) → Irrel ($res x)) ← mkLambdaFVars #[var] irrel
      return match prim with
      | true | false => q(.irrel)
  let mut b ← whnfFast b (← read).zeta
  if isBVarProj b.getAppFn then
    let proof ← mkBVarProjProof prim ctx b.getAppFn
    return ← handleOverApplication prim q($f) b.getAppFn proof b.getAppArgs[*...*]
  if b.getAppFn.isProj then
    b ← withLocalDeclD `c ctx fun var => do
      let b := b.instantiate1 var
      return (b.updateFn (← projToFn b.getAppFn)).abstract #[var]
  b.withApp fun fn args => do
  let thm ← match fn with
    | .sort u =>
      assert! args.isEmpty
      return mkApp2 (.const (sortLemma prim) [clvl, u.succ]) ctx f
    | .forallE .. =>
      assert! args.isEmpty
      return ← withLocalDecl nm bi ctx fun ctx_var => do
        let univ ← getLevel (fn.instantiate1 ctx_var)
        return mkApp2 (.const (sortLemma prim) [clvl, univ]) ctx f
    | .lit (.natVal _) =>
      assert! args.isEmpty
      return mkApp2 (.const (natLitLemma prim) [clvl]) ctx fn
    | .lit (.strVal _) =>
      assert! args.isEmpty
      return mkApp2 (.const (strLitLemma prim) [clvl]) ctx fn
    | .lam .. =>
      assert! args.isEmpty
      return ← handleUnderApplication prim q($f)
    | .letE nm' t v b _ =>
      let tlvl ← withLocalDecl nm bi ctx fun var => getLevel (t.instantiate1 var)
      have letTyLam : Q($ctx → Sort tlvl) := .lam nm ctx t bi
      have letTy : Q(Sort imax clvl tlvl) := .forallE nm ctx t bi
      have : $letTy =Q ∀ c : $ctx, $letTyLam c := ⟨⟩
      have letVal : Q($letTy) := .lam nm ctx v bi
      -- add the variable
      return ← withLetDeclQ nm' q($letVal) fun (var : Q($letTy)) _ => do
        have b := mkAppN (b.instantiate1 (.app var (.bvar 0))) args
        have f' : Q((a : $ctx) → $res a) := .lam nm ctx b bi
        have : $f' =Q $f := ⟨⟩
        if let .defEq _ := isAlwaysZeroQ tlvl then
          let res ← solveDPrimGoal prim q($f')
          return ← mkLetFVars #[var] (generalizeNondepLet := false) res
        let valcomp ← solveDPrimGoal prim q($letVal)
        have valcomp : Q($(mkPred prim q($var))) := valcomp
        -- add a computability/primrec proof
        withHaveDeclQ (nm'.appendAfter "_comp") q($valcomp) fun var_comp => do
        withBasicLocalThm prim (val := q($var)) q($var_comp) do
          let res ← solveDPrimGoal prim q($f')
          mkLetFVars #[var, var, var_comp] (generalizeNondepLet := false) res
    | .const nm us =>
      let state := otherDPrimExt.getState (← getEnv)
      let thms := if prim then state.primTheorems else state.compTheorems
      let some thm := thms.get? nm |
        throwError "no {if prim then "primrec" else "computability"} theorem available for {nm}"
      pure ⟨.const thm.thmName (.param (← read).contextUniv :: us), thm.paramInfos⟩
    | .fvar var =>
      let thms ← if prim then pure (← read).localPrimThms else pure (← read).localCompThms
      let some thm := thms.get? var |
        throwError "no local {if prim then "primrec" else "computability"} \
          theorem available for {fn}"
      pure thm
    | .bvar idx =>
      assert! idx == 0
      pure ⟨.const (idLemma prim) [.param (← read).contextUniv], #[]⟩
    | .mvar _ => throwError "expression has metavariables"
    | .proj .. | .app _ _ | .mdata _ _ => unreachable!
  if args.isEmpty && thm.paramInfos.isEmpty then
    -- fast path
    return thm.instantiate (← read).contextUniv clvl ctx
  if args.size < thm.paramInfos.size then
    -- under-application
    return ← handleUnderApplication prim q($f)
  let mut val := thm.instantiate (← read).contextUniv clvl q($ctx)
  for arg in args, param in thm.paramInfos do
    let (argT, arglvl) ← withLocalDecl nm bi ctx fun var => do
      let argT ← inferType (arg.instantiate1 var)
      let arglvl ← getLevel argT
      return (.lam nm ctx (argT.abstract #[var]) bi, arglvl)
    have argT : Q($ctx → Sort arglvl) := argT
    have argLambda : Q((c : $ctx) → $argT c) := .lam nm ctx arg bi
    val := val.app argLambda
    match param with
    | .always => continue
    | .prim =>
      let .forallE _ ty _ _ ← inferType val | throwError "invalid lemma"
      let q(@DPrim.{_u, _v} $_α $_β $g) := ty | throwError "invalid lemma"
      let subgoal ← solveDPrimGoal true q($g)
      val := val.app subgoal
    | .computable =>
      let subgoal ← solveDPrimGoal false q($argLambda)
      val := val.app subgoal
  if args.size = thm.paramInfos.size then
    return val
  let b := mkAppN fn (args.take thm.paramInfos.size)
  handleOverApplication prim q($f) b val args[thm.paramInfos.size...*]

end

initialize recAutoDCompDepsRef : IO.Ref (Expr → CoreM Unit) ← IO.mkRef (fun _ => pure ())

elab "other_dcomp_tac" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
  let type ← withReducible <| goal.getType'
  let mkApp3 (.const nm [clvl, rlvl]) ctx res f := type |
    throwError "invalid goal for other_dcomp_tac: {type}"
  let prim ←
    if nm = ``DComp then pure false
    else if nm = ``DPrim then pure true
    else throwError "invalid goal for other_dcomp_tac: {type}"
  have ctx : Q(Sort clvl) := ctx
  have res : Q($ctx → Sort rlvl) := res
  have f : Q((c : $ctx) → $res c) := f
  have f := if f.isLambda then f else q(fun c : $ctx => $f c)
  let ctxUniv := mkFreshLevelName (← getLevelNames)
  let mut context := {
    contextUniv := ctxUniv
    localPrimThms := {}
    localCompThms := {}
    zeta := false
  }
  for decl in (← getLCtx) do
    let type ← whnfR decl.type
    if let q(@DComp.{tlvl, blvl} $_t $_b $f) := type then
      if f.isFVar then
        have e : Q(DComp $f) := decl.toExpr
        context := withBasicLocalThm.newContext false q($e) context
        continue
    if let q(@DPrim.{tlvl, blvl} $_t $_b $f) := type then
      if f.isFVar then
        have e : Q(DPrim $f) := decl.toExpr
        context := withBasicLocalThm.newContext true q($e) context
        continue
    let .forallE nm t b bi := id type | continue
    context ← withLocalDecl nm bi t fun var => do
      let some ⟨v, irrel⟩ ← isTriviallyIrrelevant (b.instantiate1 var) |
        return context
      let ⟨u, t⟩ ← getLevelQ t
      have blam : Q($t → Sort v) := .lam nm t b bi
      let _irrel : Q((x : $t) → Irrel ($blam x)) ← mkLambdaFVars #[var] irrel
      have f : Q((a : $t) → $blam a) := decl.toExpr
      have e : Q(DPrim $f) := q(.irrel)
      return withBasicLocalThm.newContext true q($e) context
  (← recAutoDCompDepsRef.get) f
  let res ← (solveDPrimGoal prim q($f)).run context
  goal.assign res

end DPrimrec.Tactic.Other
