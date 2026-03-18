import DependentComputability.Defs

namespace DPrimrec.Tactic

open Lean Meta Elab Term Tactic Qq

structure RelationInstanceInfo where
  declName : Name
  instName : Name
  arity : Nat
deriving Inhabited

initialize encodingRelationExt :
    SimplePersistentEnvExtension RelationInstanceInfo (NameMap RelationInstanceInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn map entry := map.insert entry.declName entry
    addImportedFn xss :=
      xss.foldl (init := {}) fun acc xs => xs.foldl (init := acc)
        fun acc x => acc.insert x.declName x
  }

/-
initialize
  registerBuiltinAttribute {
    name := `dprim
    descr := "Attribute for `EncodingRelation` instances"
    add nm stx kind := do
      let entry ← MetaM.run' (mkThmEntry nm)
      modifyEnv (encodingRelationExt.addEntry · entry)
  }
-/

def projToFn (x : Expr) : MetaM Expr := do
  if let .proj t i e := x then
    let info := getStructureInfo (← getEnv) t
    let some name := info.getProjFn? i |
      throwError "bad projection: field index {i} out of bounds for type {t}"
    let type ← inferType e
    let type ← whnfD type
    type.withApp fun c args => do
      unless c.isConstOf t do
        throwError "bad projection: structure type name mismatch"
      return .app (mkAppN (.const name c.constLevels!) args) e
  else
    return x

structure TheoremInfo where
  prim : Bool
  declName : Name
  thmName : Name
  arity : Nat

structure DPrimTheorems where
  primTheorems : NameMap TheoremInfo := {}
  compTheorems : NameMap TheoremInfo := {}
deriving Inhabited

def DPrimTheorems.add (ths : DPrimTheorems) (th : TheoremInfo) : DPrimTheorems :=
  if th.prim then
    { ths with primTheorems := ths.primTheorems.insert th.declName th }
  else
    { ths with compTheorems := ths.compTheorems.insert th.declName th }

initialize dprimExt : SimplePersistentEnvExtension TheoremInfo DPrimTheorems ←
  registerSimplePersistentEnvExtension {
    addEntryFn := DPrimTheorems.add
    addImportedFn xss :=
      xss.foldl (init := {}) fun acc xs => xs.foldl (init := acc)
        fun acc x => acc.add x
  }

def mkThmEntry (thm : Name) : MetaM TheoremInfo := do
  let val ← getConstVal thm
  forallTelescope val.type fun xs body => do
    let mkApp5 (.const thing [clvl, rlvl]) ctx res inst inst' f := body |
      throwError "invalid `dprim` attribute, conclusion is not DPrimrec or DComputable"
    let prim ← match thing with
      | ``DPrimrec => pure true
      | ``DComputable => pure false
      | _ => throwError "invalid `dprim` attribute, conclusion is not DPrimrec or DComputable"
    let .lam nm _ b bi ← whnfR f |
      throwError "invalid `dprim` attribute, conclusion doesn't have a lambda"
    b.withApp fun x args => do
      let .const cnm lvls := x |
        throwError "invalid `dprim` attribute, conclusion must be a const"
      unless lvls == val.levelParams.tail.map Level.param do
        throwError "invalid `dprim` attribute, bad level parameters"
      unless args.size < xs.size do
        throwError "invalid `dprim` attribute, not enough parameters"
      unless ctx == xs[0]! do
        throwError "expected context parameter {ctx} but found {xs[0]!}"
      for h : i in *...args.size do
        let arg := args[i]
        let var := xs[i + 1]!
        unless arg.eta == var.app (.bvar 0) do
          throwError "invalid `dprim` attribute, parameter #{i} is \
            {Expr.lam nm ctx arg bi} and not {var} as expected"
      unless inst == xs[args.size + 1]! do
        throwError "expected context EncodingRelation instance parameter \
          {inst} but found {xs[args.size + 1]!}"
      return {
        prim
        declName := cnm
        thmName := thm
        arity := args.size
      }

initialize
  registerBuiltinAttribute {
    name := `dprim
    descr := "Attribute for `dprim_step`"
    add nm stx kind := do
      let entry ← MetaM.run' (mkThmEntry nm)
      modifyEnv (dprimExt.addEntry · entry)
  }

def finish (e : Expr) (proof : Expr) (goal : MVarId)
    (vars : Array Expr := #[]) (newGoals : Array MVarId := #[]) : MetaM (Array MVarId) := do
  match e with
  | .forallE _ t b bi =>
    let t := t.instantiateRev vars
    if bi matches .instImplicit then
      let inst ← synthInstance t
      finish b (proof.app inst) goal (vars.push inst) newGoals
    else
      let mvar ← mkFreshExprSyntheticOpaqueMVar t
      finish b (proof.app mvar) goal (vars.push mvar) (newGoals.push mvar.mvarId!)
  | _ =>
    goal.assignIfDefEq proof
    return newGoals

@[match_pattern]
def mkPSigmaExpr (u v : Level) (nm : Name) (t tt b : Expr) (bi : BinderInfo) : Expr :=
  mkApp2 (.const ``PSigma [u, v]) t (.lam nm tt b bi)

inductive IsPSigmaExpr : Expr → Nat → Prop where
  | zero : IsPSigmaExpr e 0
  | succ {b tt : Expr} {nm : Name} {bi : BinderInfo} (h : IsPSigmaExpr b n) :
    IsPSigmaExpr (mkPSigmaExpr u v nm t tt b bi) (n + 1)

theorem IsPSigmaExpr.isApp₁ (h : IsPSigmaExpr e n) (hn : n ≠ 0) :
    e.isApp := by cases h <;> trivial
theorem IsPSigmaExpr.isApp₂ (h : IsPSigmaExpr e n) (hn : n ≠ 0) :
    (e.appFn (h.isApp₁ hn)).isApp := by cases h <;> trivial
theorem IsPSigmaExpr.isConst (h : IsPSigmaExpr e n) (hn : n ≠ 0) :
    ((e.appFn (h.isApp₁ hn)).appFn (h.isApp₂ hn)).isConst := by cases h <;> trivial
theorem IsPSigmaExpr.name (h : IsPSigmaExpr e n) (hn : n ≠ 0) :
    ((e.appFn (h.isApp₁ hn)).appFn (h.isApp₂ hn)).constName! = ``PSigma := by cases h <;> trivial
theorem IsPSigmaExpr.length (h : IsPSigmaExpr e n) (hn : n ≠ 0) :
    ((e.appFn (h.isApp₁ hn)).appFn (h.isApp₂ hn)).constLevels!.length = 2 := by cases h <;> trivial
theorem IsPSigmaExpr.isLambda (h : IsPSigmaExpr e n) (hn : n ≠ 0) :
    (e.appArg (h.isApp₁ hn)).isLambda := by cases h <;> trivial

@[implemented_by Expr.instantiate1]
def _root_.Lean.Expr.instantiate1' (e subst : @& Expr) : Expr :=
  go e subst 0
where
  go (e subst : Expr) (depth : Nat) : Expr :=
    match e with
    | .bvar n => if n = depth then subst else if n < depth then e else .bvar (n - 1)
    | .proj nm i e => .proj nm i (go e subst depth)
    | .mdata d e => .mdata d (go e subst depth)
    | .lit _ | .const _ _ | .sort _ | .mvar _ | .fvar _ => e
    | .letE nm t b v nd =>
      .letE nm (go t subst depth) (go b subst depth) (go v subst (depth + 1)) nd
    | .forallE nm t b bi => .forallE nm (go t subst depth) (go b subst depth) bi
    | .lam nm t b bi => .lam nm (go t subst depth) (go b subst (depth + 1)) bi
    | .app f a => .app (go f subst depth) (go a subst depth)

@[inline]
def IsPSigmaExpr.getInner (h : IsPSigmaExpr e n) (inst : Expr) (hn : n ≠ 0) : Expr :=
  have := h.isApp₁ hn
  have := h.isApp₂ hn
  let f := e.appFn ‹_› |>.appFn ‹_›
  let l := e.appArg ‹_›
  have hf : f.isConst := h.isConst hn
  have : l.isLambda := h.isLambda hn
  let .const _ lvls := f
  let .lam nm t b bi := l
  b.instantiate1' inst

theorem IsPSigmaExpr.instantiate1'.go (h : IsPSigmaExpr e n) (inst : Expr) (depth : Nat) :
    IsPSigmaExpr (Expr.instantiate1'.go e inst depth) n := by
  cases h
  · constructor
  · constructor
    exact go ‹_› inst (depth + 1)

theorem IsPSigmaExpr.instantiate1' (h : IsPSigmaExpr e n) (inst : Expr) :
    IsPSigmaExpr (e.instantiate1' inst) n := instantiate1'.go h inst 0

theorem IsPSigmaExpr.inner (h : IsPSigmaExpr e n) (inst : Expr) (hn : n ≠ 0) :
    IsPSigmaExpr (h.getInner inst hn) (n - 1) := by
  cases h
  · constructor
  · apply instantiate1'
    assumption

@[inline]
def IsPSigmaExpr.fstExpr (x : Expr) (h : IsPSigmaExpr e n) (hn : n ≠ 0) : Expr :=
  have := h.isApp₁ hn
  have := h.isApp₂ hn
  let f := e.appFn ‹_› |>.appFn ‹_›
  let l := e.appArg ‹_›
  have hf : f.isConst := h.isConst hn
  have : l.isLambda := h.isLambda hn
  let .const _ lvls := f
  let .lam nm t b bi := l
  mkApp3 (.const ``PSigma.fst lvls) t l x

@[inline]
def IsPSigmaExpr.sndExpr (x : Expr) (h : IsPSigmaExpr e n) (hn : n ≠ 0) : Expr :=
  have := h.isApp₁ hn
  have := h.isApp₂ hn
  let f := e.appFn ‹_› |>.appFn ‹_›
  let l := e.appArg ‹_›
  have hf : f.isConst := h.isConst hn
  have : l.isLambda := h.isLambda hn
  let .const _ lvls := f
  let .lam nm t b bi := l
  mkApp3 (.const ``PSigma.snd lvls) t l x

@[inline]
def IsPSigmaExpr.mkExpr (x y : Expr) (h : IsPSigmaExpr e n) (hn : n ≠ 0) : Expr :=
  have := h.isApp₁ hn
  have := h.isApp₂ hn
  let f := e.appFn ‹_› |>.appFn ‹_›
  let l := e.appArg ‹_›
  have hf : f.isConst := h.isConst hn
  have : l.isLambda := h.isLambda hn
  let .const _ lvls := f
  let .lam nm t b bi := l
  mkApp4 (.const ``PSigma.mk lvls) t l x y

open Qq in
partial def mkSigmaType (type : Expr) (n : Nat) (vars : Array Expr := #[]) :
    MetaM ((u : Level) × { x : Q(Sort u) // IsPSigmaExpr x n } × Expr) := do
  let cont (nm : Name) (t t' b : Expr) (bi : BinderInfo) :=
    withLocalDecl nm bi t' fun var => do
      let l ← getLevel t'
      match n with
      | 0 => return ⟨l, ⟨t, .zero⟩, b⟩
      | k + 1 =>
        let ⟨u, newT, body⟩ ← mkSigmaType b k (vars.push var)
        let e := mkPSigmaExpr l u nm t t newT bi
        return ⟨(levelOne.max l).max u |>.normalize, ⟨e, newT.2.succ⟩, body⟩
  match type with
  | .forallE nm t b bi =>
    let t' := t.instantiateRev vars
    cont nm t t' b bi
  | _ =>
    let .forallE nm t' b bi ← whnf (type.instantiateRev vars) |
      throwError "invalid type"
    let t := t'.abstract vars
    cont nm t t' b bi

partial def mkUncurriedAppArgs (sigma : Expr) (var : Expr) (n : Nat)
    (hsigma : IsPSigmaExpr sigma n) (args : Array Expr := #[]) : Array Expr :=
  match n with
  | 0 => args.push var
  | k + 1 =>
    let fst := hsigma.fstExpr var nofun
    let snd := hsigma.sndExpr var nofun
    let b := hsigma.getInner fst nofun
    mkUncurriedAppArgs b snd k (hsigma.inner fst nofun) (args.push fst)

partial def mkUncurriedApp (sigma : Expr) (e var : Expr) (n : Nat)
    (hsigma : IsPSigmaExpr sigma n) : Expr :=
  match n with
  | 0 => .app e var
  | k + 1 =>
    let fst := hsigma.fstExpr var nofun
    let snd := hsigma.sndExpr var nofun
    let b := hsigma.getInner fst nofun
    mkUncurriedApp b (.app e fst) snd k (hsigma.inner fst nofun)

partial def mkUncurriedArg (sigma : Expr) (args : Array Expr) (i : Nat := 0)
    (hi : i < args.size := by grind) (hsigma : IsPSigmaExpr sigma (args.size - i - 1) := by grind) :
    Expr :=
  let arg := args[i]
  if h : i + 1 < args.size then
    have := by grind
    let b := hsigma.getInner arg this
    have _ : IsPSigmaExpr b _ := hsigma.inner arg this
    let arg2 := mkUncurriedArg b args (i + 1)
    hsigma.mkExpr arg arg2 this
  else
    arg

def idLemma (prim : Bool) : Name :=
  if prim then ``DPrimrec.id else ``DComputable.id

def constLemma (prim : Bool) : Name :=
  if prim then ``DPrimrec.const else ``DComputable.const

def constCurryLemma (prim : Bool) : Name :=
  if prim then ``DPrimrec.constCurry else ``DComputable.constCurry

def compLemma (prim : Bool) : Name :=
  if prim then ``DPrimrec.comp else ``DComputable.comp

def proofIrrelLemma (prim : Bool) : Name :=
  if prim then ``DPrimrec.irrel else ``DComputable.irrel

def curryLemma (prim : Bool) : Name :=
  if prim then ``DPrimrec.curry else ``DComputable.curry

def predName (prim : Bool) : Name :=
  if prim then ``DPrimrec else ``DComputable

partial def whnfFast (e : Expr) (argsRev : Array Expr := #[]) : MetaM Expr := do
  match e with
  | .app f a => whnfFast f (argsRev.push a)
  | .proj .. => return argsRev.foldr (fun a f => f.app a) (← projToFn e)
  | .mdata _ e => whnfFast e argsRev
  | .lam .. => if argsRev.isEmpty then return e else whnfFast (e.betaRev argsRev)
  | .letE _ _ v b _ => whnfFast (b.instantiate1 v)
  | _ => return argsRev.foldr (fun a f => f.app a) e

def matchFunctionType (e : Expr) : MetaM (Level × Expr × Level × Expr) := do
  let fty ← whnfD e
  let .forallE nm tt bb bi := fty | throwFunctionExpected e
  withLocalDeclD `x tt fun x => do
    let bb' := bb.instantiate1 x
    return (← getLevel tt, tt, ← getLevel bb', .lam nm tt bb bi)

elab "dprim_step" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
  let type ← withReducible goal.getType'
  let mkApp5 (.const thing [clvl, rlvl]) ctx res inst rinst f := type |
    throwError "invalid dprim_step goal{indentExpr type}"
  let prim ← match thing with
    | ``DPrimrec => pure true
    | ``DComputable => pure false
    | _ => throwError "invalid dprim_step goal{indentExpr type}"
  if rlvl.isAlwaysZero then
    let synth ← synthInstance (.forallE `c ctx (mkApp2 (.const ``Irrelevant [rlvl])
      (res.beta #[.bvar 0]) (rinst.beta #[.bvar 0])) .default)
    goal.assignIfDefEq (mkApp6 (.const (proofIrrelLemma prim) [clvl, rlvl])
      ctx res inst rinst synth f)
    return
  let f ← whnfR f
  let .lam nm _ b bi := f |
    throwError "invalid dprim_step goal, expected function at{indentExpr f}"
  let b ← whnfFast b
  if b matches .bvar 0 then
    goal.assign (mkApp2 (.const (idLemma prim) [clvl]) ctx inst)
    return
  let rec handleUnderApp : TacticM Unit := do
    let (ty, tlvl, bty, blvl) ← withLocalDecl nm bi ctx fun c => do
      let res := res.app c
      let res ← whnfD res
      let .forallE _ tt bb _ := res |
        throwError "ill-typed goal"
      withLocalDeclD `x tt fun x => do
        pure (tt.abstract #[c], ← getLevel tt, bb.abstract #[c, x], ← getLevel (bb.instantiate1 x))
    let mut b := b
    unless b matches .lam .. do
      b := .lam `x ty (.app (b.liftLooseBVars 0 1) (.bvar 0)) .default
    let .lam nm' t b' bi' := b | unreachable!
    let proof : Expr := .const (curryLemma prim) [clvl, tlvl, blvl]
    let bty := .lam nm ctx (.lam nm' t bty bi') bi
    let b' := .lam nm ctx (.lam nm' t b' bi') bi
    let proof := mkApp5 proof ctx (.lam nm ctx t bi) bty b' inst
    let proofType ← inferType proof
    let goals ← finish proofType proof goal
    replaceMainGoal goals.toList
  let rec handleOverApp : TacticM Unit := do
    let .app f a := b | unreachable!
    let (tt, tlvl, bb, blvl) ← withLocalDecl nm bi ctx fun c => do
      let fty ← whnfD (← inferType (f.instantiate1 c))
      let .forallE _ tt bb _ := fty | throwFunctionExpected b
      withLocalDeclD `x tt fun x => do
        pure (tt.abstract #[c], ← getLevel tt, bb.abstract #[c, x], ← getLevel (bb.instantiate1 x))
    let bty := .lam nm ctx (.lam `x tt bb .default) bi
    let proof : Expr := .const ``DComputable.app [clvl, tlvl, blvl]
    let proof := mkApp6 proof ctx (.lam nm ctx tt bi) bty (.lam nm ctx f bi) (.lam nm ctx a bi) inst
    let proofType ← inferType proof
    let goals ← finish proofType proof goal
    replaceMainGoal goals.toList
  if b matches .lam .. then
    return ← handleUnderApp
  b.withApp fun x args => do
    let .const cnm lvls := x |
      if x.hasLooseBVars then
        throwError "unexpected application, bound variables in {f}"
      let type ← inferType x
      if args.size = 0 ∧ type.isForall then
        let (alvl, aty, blvl, bty) ← matchFunctionType type
        let proof : Expr := .const (constCurryLemma prim) [clvl, alvl, blvl]
        let proof := mkApp5 proof ctx aty bty x inst
        let proofType ← inferType proof
        let goals ← finish proofType proof goal
        replaceMainGoal goals.toList
        return
      else if !prim then
        if args.size > 0 then
          return ← handleOverApp
      if h : args.size = 0 then
        throwError "no"
      else
      let type ← inferType x
      let ⟨u, ⟨sigma, hsigma⟩, body⟩ ← mkSigmaType type (args.size - 1)
      let appArgs := mkUncurriedAppArgs sigma (.bvar 0) _ hsigma
      let app : Expr := .lam `c sigma (mkAppN x appArgs) .default
      let arg : Expr := mkUncurriedArg sigma args 0
      let arg := .lam nm ctx arg bi
      let out : Expr := .lam `c sigma (body.instantiateRev appArgs) .default
      let proof : Expr := .const (compLemma prim) [clvl, u, rlvl]
      let proof := mkApp6 proof ctx sigma out app arg inst
      let proofType ← inferType proof
      let goals ← finish proofType proof goal
      let firstGoal :: moreGoals := goals.toList | unreachable!
      firstGoal.assumption
      replaceMainGoal moreGoals
    let thms := dprimExt.getState (← getEnv)
    let map := if prim then thms.primTheorems else thms.compTheorems
    let some entry := map.find? cnm |
      if !b.hasLooseBVars then
        let res ← inferType b
        let rinst ← synthInstance (.app (.const ``EncodingRelation [rlvl]) res)
        let repr ← synthInstance (mkApp2 (.const ``FullyRepresentable [rlvl]) res rinst)
        goal.assign (mkApp6 (.const (constLemma prim) [clvl, rlvl]) ctx res inst rinst repr b)
        return
      if args.size > 0 ∧ prim = false then
        return ← handleOverApp
      throwTacticEx `dprim_step goal m!"don't know what to do with {x}"
    if args.size != entry.arity then
      if args.size < entry.arity then
        return ← handleUnderApp
      unless prim do
        return ← handleOverApp
      throwTacticEx `dprim_step goal
        m!"unexpected over-application: expected {entry.arity} arguments \
          but found {args.size} in{indentExpr f}"
    let mut proof : Expr := .const entry.thmName (clvl :: lvls)
    proof := proof.app ctx
    for a in args do
      proof := proof.app (.lam nm ctx a bi)
    proof := proof.app inst
    let proofType ← inferType proof
    let goals ← finish proofType proof goal
    replaceMainGoal goals.toList

macro "dprim_tac " "[" is:ident,+ "]" : tactic =>
  `(tactic| (delta $(is.getElems):ident*; repeat first | assumption | dprim_step))

macro "dprim_tac" : tactic =>
  `(tactic| repeat first | assumption | dprim_step)

syntax declModifiers "dprim_decl " ident "for " ident ("with " num)?
  (&" unfolding " ident,*)? : command
syntax declModifiers "dcomp_decl " ident "for " ident ("with " num)?
  (&" unfolding " ident,*)? : command

open Command

def insertContextType (e : Expr) (ctx : Expr) (max : Nat) (insts : Array Expr := #[]) : Expr :=
  match max, e with
  | max + 1, .forallE nm t b bi =>
    let t := t.instantiate insts
    let newInst := .app (.bvar (insts.size + 1)) (.bvar 0)
    .lam nm (.forallE `c ctx t .default) (insertContextType b ctx max (insts.push newInst)) bi
  | _, t =>
    let t := t.instantiate insts
    .forallE `c ctx t .default

def elabDPrimDecl (mod : Modifiers) (arity : Option Nat) (prim : Bool) (thm decl : Ident)
    (unfold : Array Ident) : MetaM Unit := do
  let declName ← realizeGlobalConstNoOverloadWithInfo decl
  let val ← getConstVal declName
  let levels := val.levelParams
  let l := mkFreshLevelName levels
  let clvl := .param l
  withLocalDecl `ctx .implicit (.sort clvl) fun ctx => do
  let e ← forallBoundedTelescope val.type arity mkForallFVars
  let e := insertContextType e ctx (arity.getD e.getForallArity)
  lambdaTelescope e fun params body => do
  withLocalDecl (← mkFreshUserName `inst) .instImplicit
    (.app (.const ``EncodingRelation [clvl]) ctx) fun cinst =>
  let rec addRequirements (i : Nat := 0) (newVars : Array Expr := #[]) :
      MetaM Unit := do
    if h : i < params.size then
      let param := params[i]
      let paramType ← inferType param
      let req ← forallTelescopeReducing paramType fun xs x => do
        if let .sort u := x then
          let instType := .app (.const ``EncodingRelation [u]) (mkAppN param xs)
          return some (← mkForallFVars xs instType, .instImplicit)
        if ← isProp x then
          return none
        if prim then
          let .forallE _ _ b _ := paramType | unreachable!
          let lvl ← getLevel (b.instantiate1 xs[0]!)
          let instType := .forallE `c ctx (.app (.const ``EncodingRelation [lvl]) b) .default
          let inst ← synthInstance? instType
          return inst.map fun inst =>
            (mkApp5 (.const ``DPrimrec [clvl, lvl]) ctx
              (.lam `c ctx b .default) cinst inst param, .default)
        else
          let .forallE _ _ b _ := paramType | unreachable!
          let lvl ← getLevel (b.instantiate1 xs[0]!)
          let instType := .forallE `c ctx (.app (.const ``EncodingRelation [lvl]) b) .default
          let inst ← synthInstance? instType
          return inst.map fun inst =>
            (mkApp5 (.const ``DComputable [clvl, lvl]) ctx
              (.lam `c ctx b .default) cinst inst param, .default)
      if let some (e, bi) := req then
        withLocalDecl (← mkFreshUserName `x) bi e fun var => do
          addRequirements (i + 1) (newVars.push var)
      else
        addRequirements (i + 1) newVars
    else
      let .forallE _ _ b _ := body | unreachable!
      let blvl ← withLocalDeclD `c ctx fun ctx => getLevel (b.instantiate1 ctx)
      let inst ← synthInstance
        (.forallE `c ctx (.app (.const ``EncodingRelation [blvl]) b) .default)
      let f := .lam `c ctx (mkAppN (.const declName (levels.map Level.param))
        (params.map fun x => x.app (.bvar 0))) .default
      let goalType : Expr := .const (predName prim) [clvl, blvl]
      let goalType := mkApp5 goalType ctx (.lam `c ctx b .default) cinst inst f
      let goal ← mkFreshExprSyntheticOpaqueMVar goalType
      let unfold := #[decl] ++ unfold
      let tac ← `(tactic| dprim_tac [$unfold,*])
      let tactic : TacticM Unit := do
        evalTactic tac *> done
      tactic.run { elaborator := .anonymous } |>.run' ⟨[goal.mvarId!]⟩
        |>.run' {} { levelNames := l :: levels }
      let type ← mkForallFVars ((#[ctx] ++ params).push cinst ++ newVars) goalType
      let value ← mkLambdaFVars ((#[ctx] ++ params).push cinst ++ newVars) (← instantiateMVars goal)
      let (thmName, _) ← mkDeclName (← getCurrNamespace) mod thm.getId
      addDecl <| .thmDecl {
        name := thmName
        levelParams := l :: levels
        type, value
      }
      addTermInfo' (isBinder := true) thm (.const thmName (clvl :: levels.map Level.param))
        |>.run' |>.run'
      let entry := {
        prim, declName, thmName
        arity := params.size
      }
      modifyEnv (dprimExt.addEntry · entry)
  addRequirements

elab_rules : command
  | `($mod:declModifiers dprim_decl $i for $x $[with $n]? $[unfolding $xs,*]?) => do
    liftTermElabM <| elabDPrimDecl (← elabModifiers mod) (n.map (·.getNat)) true i x
      (xs.elim #[] (·.getElems))
  | `($mod:declModifiers dcomp_decl $i for $x $[with $n]? $[unfolding $xs,*]?) => do
    liftTermElabM <| elabDPrimDecl (← elabModifiers mod) (n.map (·.getNat)) false i x
      (xs.elim #[] (·.getElems))

end DPrimrec.Tactic
