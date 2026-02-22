import DependentComputability.SortExtra
import Batteries
namespace DPrimrec.Tactic

open Lean Meta Elab Term Tactic Qq

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
    let mkApp6 (.const thing [clvl, rlvl]) ctx_base ctx α_base α f_base f := body |
      throwError "invalid `dprim` attribute, conclusion is not DPrimrec or DComputable"
    let prim ← match thing with
      | ``DPrimrec => pure true
      | ``DComputable => pure false
      | _ => throwError "invalid `dprim` attribute, conclusion is not DPrimrec or DComputable"
    let .lam nm _ b bi ← whnfR f_base |
      throwError "invalid `dprim` attribute, conclusion doesn't have a lambda"
    b.withApp fun x args => do
      let .const cnm lvls := x |
        throwError "invalid `dprim` attribute, conclusion must be a const"
      unless lvls == val.levelParams.tail.map Level.param do
        throwError "invalid `dprim` attribute, bad level parameters"
      unless ctx_base == xs[0]! do
        throwError "expected context parameter {ctx_base} but found {xs[0]!}"
      unless ctx == xs[1]! do
        throwError "expected context extra parameter {ctx} but found {xs[1]!}"
      let mut map : Array ParamComputability := #[]
      let mut j := 2
      for h : i in *...args.size do
        let arg := args[i]
        if h : j + 1 < xs.size then
          let var_base := xs[j]
          unless arg.eta == var_base.app (.bvar 0) do
            throwError "invalid `dprim` attribute, parameter #{i} is \
              {Expr.lam nm ctx arg bi} and not {var_base} as expected"
          if h : j + 2 < xs.size then
            let x := xs[j + 2]
            let ty ← inferType x
            if ty.isAppOf ``DComputable then
              map := map.push .computable
              j := j + 3
            else if ty.isAppOf ``DPrimrec then
              map := map.push .prim
              j := j + 3
            else
              map := map.push .always
              j := j + 2
        else
          throwError "invalid `dprim` attribute, parameter #{i} out of range"
      return {
        prim
        declName := cnm
        thmName := thm
        paramInfos := map
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

def proofIrrelLemma (prim : Bool) : Name :=
  if prim then ``DPrimrec.proof else ``DComputable.proof

def curryLemma (prim : Bool) : Name :=
  if prim then ``DPrimrec.curry else ``DComputable.curry

def sortLemma (prim : Bool) : Name :=
  if prim then ``DPrimrec.sort else ``DComputable.sort

def natLitLemma (prim : Bool) : Name :=
  if prim then `DPrimrec.natLit else `DComputable.natLit

def strLitLemma (prim : Bool) : Name :=
  if prim then `DPrimrec.strLit else `DComputable.strLit

def predName (prim : Bool) : Name :=
  if prim then ``DPrimrec else ``DComputable

def mkPred (prim : Bool) {u v : Level}
    {α_base : Q(Sort u)} {α : Q(convert_to_new_type% $α_base)}
    {β_base : Q($α_base → Sort v)} {β : Q(convert_to_new_type% $β_base)}
    {f_base : Q((a : $α_base) → $β_base a)} (f : Q(convert_to_new_type% $f_base)) :
    Q(Prop) :=
  if prim then
    q(DPrimrec $f)
  else
    q(DComputable $f)

/-set_option linter.unusedVariables false in
def constCurryLemma (prim : Bool) (ulvl clvl rlvl : Level) :
    Q(∀ {β_base : Sort clvl} {β : convert_to_new_type% β_base}
      {γ_base : β_base → Sort rlvl} {γ : convert_to_new_type% γ_base}
      {f_base : (a : β_base) → γ_base a} {f : convert_to_new_type% f_base}
      (hf : DComputable f)
      {α_base : Sort ulvl} {α : convert_to_new_type% α_base},
      $(mkPred prim q(convert_to_new% fun _ : α_base => f_base)))= :=
  match prim with
  | true => q(@DPrimrec.constCurry.{ulvl, clvl, rlvl})
  | false => q(@DComputable.constCurry.{ulvl, clvl, rlvl})-/

/-set_option linter.unusedVariables false in
def compLemma (prim : Bool) (ulvl clvl rlvl : Level) :
    Q(∀ {β_base : Sort clvl} {β : convert_to_new_type% β_base}
      {γ_base : β_base → Sort rlvl} {γ : convert_to_new_type% γ_base}
      {f_base : (a : β_base) → γ_base a} {f : convert_to_new_type% f_base}
      (hf : DComputable f)
      {α_base : Sort ulvl} {α : convert_to_new_type% α_base},
      $(mkPred prim _ _) (convert_to_new% fun _ : α_base => f_base)) :=
  match prim with
  | true => q(@DPrimrec.comp.{ulvl, clvl, rlvl})
  | false => q(@DComputable.comp.{ulvl, clvl, rlvl})-/

partial def whnfFast (e : Expr) (zeta : Bool) (argsRev : Array Expr := #[]) : MetaM Expr := do
  match e with
  | .app f a => whnfFast f zeta (argsRev.push a)
  | .proj .. => return argsRev.foldr (fun a f => f.app a) (← projToFn e)
  | .mdata _ e => whnfFast e zeta argsRev
  | .lam .. => if argsRev.isEmpty then return e else whnfFast (e.betaRev argsRev) zeta
  | .letE _ _ v b _ =>
    if zeta then
      whnfFast (b.instantiate1 v) zeta argsRev
    else
      return argsRev.foldr (fun a f => f.app a) e
  | _ => return argsRev.foldr (fun a f => f.app a) e

def matchFunctionType (e : Expr) : MetaM (Level × Expr × Level × Expr) := do
  let fty ← whnfD e
  let .forallE nm tt bb bi := fty | throwFunctionExpected e
  withLocalDeclD `x tt fun x => do
    let bb' := bb.instantiate1 x
    return (← getLevel tt, tt, ← getLevel bb', .lam nm tt bb bi)

structure LocalThm where
  value : Expr
  paramInfos : Array ParamComputability

def LocalThm.instantiate (thm : LocalThm) (univ : Name) (clvl : Level)
    (ctx_base ctx : Expr) : Expr :=
  let repl (lvl : Name) : Option Level := if lvl = univ then clvl else none
  mkApp2 (thm.value.instantiateLevelParamsCore repl) ctx_base ctx

structure Context where
  contextUniv : Name
  localPrimThms : FVarIdMap LocalThm
  localCompThms : FVarIdMap LocalThm
  zeta : Bool

abbrev M := ReaderT Context <| ReaderT (FVarIdMap Expr) <| MonadCacheT ExprStructEq Expr MetaM

instance : Inhabited (M α) := ⟨(default : MetaM _)⟩

@[inline]
def convertToNew (e : Expr) : M Expr := do
  conversionStepNew.visit e (← readThe _)

@[inline]
def convertToNewType (ty e : Expr) : M Expr := do
  return .app (.proj ``SortExtra 0 (← convertToNew ty)) e

@[inline]
def withNewCtxVar (var_base var : Expr) (act : M α) : M α := do
  withTheReader (FVarIdMap Expr) (·.insert var_base.fvarId! var) act

@[inline]
def withBasicLocalThm (prim : Bool) {clvl tlvl : Level}
    {ctx_base : Q(Sort clvl)} {ctx : Q(convert_to_new_type% $ctx_base)}
    {res_lam_base : Q($ctx_base → Sort tlvl)} {res_lam : Q(convert_to_new_type% $res_lam_base)}
    {val_base : Q((a : $ctx_base) → $res_lam_base a)}
    (val : Q(convert_to_new_type% $val_base))
    (val_comp : Q($(mkPred prim val)))
    (act : M α) : M α := do
  withReader newContext act
where
  newContext (c : Context) : Context :=
    have u := Level.param c.contextUniv
    match prim with
    | true =>
      let value1 := q(@DPrimrec.comp.{u} _ _ _ _ _ _ $val_comp)
      let value2 := q(@DPrimrec.compComputable.{u} _ _ _ _ _ _ $val_comp)
      let thm1 : LocalThm := { value := by exact value1, paramInfos := #[.prim] }
      let thm2 : LocalThm := { value := by exact value2, paramInfos := #[.computable] }
      { c with localPrimThms := c.localPrimThms.insert val_base.fvarId! thm1,
               localCompThms := c.localCompThms.insert val_base.fvarId! thm2 }
    | false =>
      let value := q(@DComputable.comp.{u} _ _ _ _ _ _ $val_comp)
      let thm : LocalThm := { value := by exact value, paramInfos := #[.computable] }
      { c with localCompThms := c.localCompThms.insert val_base.fvarId! thm }

@[inline]
def isAlwaysZeroQ (lvl : Level) : MaybeLevelDefEq lvl Level.zero :=
  if lvl.isAlwaysZero then
    .defEq ⟨⟩
  else
    .notDefEq

@[inline]
def withLetDeclQ [MonadControlT MetaM n] [Monad n]
    (name : Name) {type : Q(Sort u)} (val : Q($type))
    (k : (var : Q($type)) → $var =Q $val → n α) : n α :=
  withLetDecl name type val (fun e => k e ⟨⟩)

@[inline]
def withHaveDeclQ [MonadControlT MetaM n] [Monad n]
    (name : Name) {type : Q(Sort u)} (val : Q($type))
    (k : (var : Q($type)) → n α) : n α :=
  withLetDecl name type val k (nondep := true)

mutual
partial def handleUnderApplication (prim : Bool) {clvl rlvl : Level}
    {ctx_base : Q(Sort clvl)} {ctx : Q(convert_to_new_type% $ctx_base)}
    {res_base : Q($ctx_base → Sort rlvl)} {res : Q(convert_to_new_type% $res_base)}
    (f_base : Q((a : $ctx_base) → $res_base a)) (f : Q(convert_to_new_type% $f_base)) :
    M Q($(mkPred prim f)) := do
  let .lam nm _ b bi := id f_base | unreachable!
  let (t', t'lvl, b', b'lvl) ← withLocalDeclQ nm bi q($ctx_base) fun ctx_var => do
    let ty ← inferType (b.instantiate1 ctx_var)
    let .forallE nm' t' b' bi' ← whnf ty |
      throwError "function expected for type {ty} but we have {b.instantiate1 ctx_var}"
    let t'lvl ← getLevel t'
    trace[debug] "under-application: {b.instantiate1 ctx_var} has type {ty} : Sort {t'lvl}"
    let b'lvl ← withLocalDecl nm' bi' t' (getLevel <| b'.instantiate1 ·)
    let t'lam := Expr.lam nm ctx_base (t'.abstract #[ctx_var]) bi
    let b'lam := Expr.lam nm ctx_base ((Expr.lam nm' t' b' bi').abstract #[ctx_var]) bi
    pure (t'lam.abstract #[ctx_var], t'lvl, b'lam, b'lvl)
  have t' : Q($ctx_base → Sort t'lvl) := t'
  let _newt' : Q(convert_to_new_type% $t') ← convertToNew t'
  have b' : Q((c : $ctx_base) → $t' c → Sort b'lvl) := b'
  let _newb' : Q(convert_to_new_type% $b') ← convertToNew b'
  have : rlvl =QL imax t'lvl b'lvl := ⟨⟩
  have : $res_base =Q fun c => (x : $t' c) → $b' c x := ⟨⟩
  have : $res =Q convert_to_new% fun c => (x : $t' c) → $b' c x := ⟨⟩
  let proof ← solveDPrimGoal false q(fun x : PSigma $t' => $f_base x.1 x.2)
    q(convert_to_new% fun x : PSigma $t' => $f_base x.1 x.2)
  match prim with
  | true => return q(DPrimrec.curry (f := convert_to_new% $f_base) $proof)
  | false => return q(DComputable.curry (f := convert_to_new% $f_base) $proof)

-- assumes that `f_base` is a lambda
partial def solveDPrimGoal (prim : Bool) {clvl rlvl : Level}
    {ctx_base : Q(Sort clvl)} {ctx : Q(convert_to_new_type% $ctx_base)}
    {res_base : Q($ctx_base → Sort rlvl)} {res : Q(convert_to_new_type% $res_base)}
    (f_base : Q((a : $ctx_base) → $res_base a)) (f : Q(convert_to_new_type% $f_base)) :
    M Q($(mkPred prim f)) := withIncRecDepth do
  withTraceNode `debug (return m!"{exceptEmoji ·} trying to solve goal{indentExpr f}\n\
    with{indentExpr f_base}") do
  if let .defEq _ := isAlwaysZeroQ rlvl then
    match prim with
    | true => return q((DPrimrec.proof))
    | false => return q((DComputable.proof))
  let .lam nm _ b bi := id f_base | unreachable!
  let b ← whnfFast b (← read).zeta
  b.withApp fun fn args => do
  let thm ← match fn with
    | .sort u =>
      assert! args.isEmpty
      return mkApp4 (.const (sortLemma prim) [clvl, u.succ]) ctx_base ctx f_base f
    | .forallE .. =>
      assert! args.isEmpty
      return ← withLocalDecl nm bi ctx_base fun ctx_var => do
        let univ ← getLevel (fn.instantiate1 ctx_var)
        return mkApp4 (.const (sortLemma prim) [clvl, univ]) ctx_base ctx f_base f
    | .lit (.natVal _) =>
      assert! args.isEmpty
      return mkApp3 (.const (natLitLemma prim) [clvl]) ctx_base ctx fn
    | .lit (.strVal _) =>
      assert! args.isEmpty
      return mkApp3 (.const (strLitLemma prim) [clvl]) ctx_base ctx fn
    | .lam .. =>
      assert! args.isEmpty
      return ← handleUnderApplication prim q($f_base) q($f)
    | .letE nm' t v b _ =>
      let tlvl ← withLocalDecl nm bi ctx_base fun var => getLevel (t.instantiate1 var)
      have letTy : Q(Sort imax clvl tlvl) := .forallE nm ctx_base t bi
      let newLetTy : Q(convert_to_new_type% $letTy) ← convertToNew letTy
      have letVal : Q($letTy) := .lam nm ctx_base v bi
      let newLetVal : Q(convert_to_new_type% $letVal) ← convertToNew letVal
      -- add a base variable
      return ← withLetDeclQ (nm'.appendAfter "_base") q($letVal) fun var_base _ => do
        -- add a converted variable
        withLetDeclQ nm' (type := q($newLetTy.1 $letVal)) q($newLetVal)
          fun (var : Q($newLetTy.1 $letVal)) _ => do
        withNewCtxVar var_base var do
          have b := mkAppN (b.instantiate1 (.app var (.bvar 0))) args
          have f_base' : Q((a : $ctx_base) → $res_base a) := .lam nm ctx_base b bi
          have : $f_base' =Q $f_base := ⟨⟩
          let f : Q(convert_to_new_type% $f_base') ← convertToNew f_base'
          if let .defEq _ := isAlwaysZeroQ tlvl then
            let res ← solveDPrimGoal prim q($f_base) q($f)
            return ← mkLetFVars #[var_base, var] res
          have letTyLam : Q($ctx_base → Sort tlvl) := .lam nm ctx_base t bi
          let _newLetTyLam : Q(convert_to_new_type% $letTyLam) ← convertToNew letTyLam
          have : $letTy =Q ∀ c : $ctx_base, $letTyLam c := ⟨⟩
          have : $newLetTy =Q convert_to_new% ∀ c : $ctx_base, $letTyLam c := ⟨⟩
          let valcomp ← solveDPrimGoal prim q($letVal) q($newLetVal)
          have valcomp : Q($(mkPred prim q($var))) := valcomp
          -- add a computability/primrec proof
          withHaveDeclQ (nm'.appendAfter "_comp") q($valcomp) fun var_comp => do
          withBasicLocalThm prim q($var) q($var_comp) do
            let res ← solveDPrimGoal prim q($f_base') q($f)
            mkLetFVars #[var_base, var, var_comp] (generalizeNondepLet := false) res
    | .const nm us =>
      let state := dprimExt.getState (← getEnv)
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
    return thm.instantiate (← read).contextUniv clvl ctx_base ctx
  if args.size < thm.paramInfos.size then
    -- under-application
    return ← handleUnderApplication prim q($f_base) q($f)
  let mut val := thm.instantiate (← read).contextUniv clvl q($ctx_base) q($ctx)
  for arg in args, param in thm.paramInfos do
    let (argT, arglvl) ← withLocalDecl nm bi ctx_base fun var => do
      let argT ← inferType (arg.instantiate1 var)
      let arglvl ← getLevel argT
      return (.lam nm ctx_base (argT.abstract #[var]) bi, arglvl)
    have argT : Q($ctx_base → Sort arglvl) := argT
    let _newargT : Q(convert_to_new_type% $argT) ← convertToNew argT
    have argLambda : Q((c : $ctx_base) → $argT c) := .lam nm ctx_base arg bi
    let newArgLambda : Q(convert_to_new_type% $argLambda) ← convertToNew argLambda
    val := mkApp2 val argLambda newArgLambda
    match param with
    | .always => continue
    | .prim =>
      let .forallE _ (mkApp6 (.const ``DPrimrec [u, v]) α_base α β_base β g_base g) _ _ ←
          inferType val | throwError "invalid lemma"
      let subgoal ← @solveDPrimGoal true u v α_base α β_base β g_base g
      val := val.app subgoal
    | .computable =>
      let subgoal ← solveDPrimGoal false q($argLambda) q($newArgLambda)
      val := val.app subgoal
  if args.size = thm.paramInfos.size then
    return val
  -- over-application (ensure we are in computable territory)
  let false := prim |
    try
      return ← handleUnderApplication prim q($f_base) q($f)
    catch _ =>
      withLocalDecl nm bi ctx_base fun var => do
        throwError "invalid over-application in primrec goal: \
          expected at most {thm.paramInfos.size} arguments but found {args.size} in\
          {indentExpr <| b.instantiate1 var}"
  let mut (type, newType) ←
    withLocalDeclQ nm bi q($ctx_base) fun var_base => do
    withLocalDeclQ nm bi q($ctx.1 $var_base) fun var => do
    withNewCtxVar var_base var do
      let mut type ← inferType ((mkAppN fn (args.take thm.paramInfos.size)).instantiate1 var_base)
      if type.getForallArity < args.size - thm.paramInfos.size then
        type ← liftM <| forallBoundedTelescope type (some (args.size - thm.paramInfos.size))
            mkForallFVars
      return (type.abstract #[var_base], (← convertToNew type).abstract #[var_base, var])
  let mut b := mkAppN fn (args.take thm.paramInfos.size)
  let mut newB ←
    withLocalDeclQ nm bi q($ctx_base) fun var_base => do
    withLocalDeclQ nm bi q($ctx.1 $var_base) fun var => do
    withNewCtxVar var_base var do
      let res ← convertToNew (b.instantiate1 var_base)
      return res.abstract #[var_base, var]
  for arg in args[thm.paramInfos.size...*] do
    let wrapInNewLam (e : Expr) : Expr :=
      .lam (nm.appendAfter "_base") ctx_base (.lam nm (mkExtraApp ctx (.bvar 0)) e bi) bi
    let .forallE nnn ttt bbb bbbiii := id type | throwError "error"
    let mkApp4 (.const ``New.Forall [t'lvl, b'lvl]) _ t' _ b' := id newType | unreachable!
    have t'lam : Q($ctx_base → Sort t'lvl) := .lam nm ctx_base ttt bi
    have b'lam : Q((c : $ctx_base) → $t'lam c → Sort b'lvl) :=
      .lam nm ctx_base (.lam nnn ttt bbb bbbiii) bi
    have bLambda : Q((c : $ctx_base) → (a : $t'lam c) → $b'lam c a) := .lam nm ctx_base b bi
    have argLambda : Q((c : $ctx_base) → $t'lam c) := .lam nm ctx_base arg bi
    have _newt'lam : Q(convert_to_new_type% $t'lam) := wrapInNewLam t'
    have _newb'lam : Q(convert_to_new_type% $b'lam) := wrapInNewLam b'
    have newBLambda : Q(convert_to_new_type% $bLambda) := wrapInNewLam newB
    let newArgLambda : Q(convert_to_new_type% $argLambda) ← convertToNew argLambda
    have val' : Q(DComputable (convert_to_new% $bLambda)) := val
    let argProof ← solveDPrimGoal false q($argLambda) q($newArgLambda)
    val := q(DComputable.app $val' $argProof)
    newType := b'.beta #[arg.liftLooseBVars 0 1, newArgLambda.bindingBody!.bindingBody!]
    type := bbb.instantiate1 arg
    b := b.app arg
    newB := mkApp2 newB (arg.liftLooseBVars 0 1) newArgLambda.bindingBody!.bindingBody!
  return val

end

partial def isTriviallyIrrelevant (e : Expr) : Option Expr := do
  if let .const ``New.Sort [u] := e then
    return q(instIrrelevantSort.{u})
  else if let mkApp4 (.const ``New.Forall [u, v]) α_base α β_base β := e then
    let .lam nm t (.lam nm' t' b' bi') bi := β | none
    have α_base : Q(Sort u) := α_base
    have α : Q(convert_to_new_type% $α_base) := α
    have β_base : Q($α_base → Sort v) := β_base
    have β : Q(convert_to_new_type% $β_base) := β
    let _inst : Q(∀ ⦃a_base : $α_base⦄ (a : $α.1 a_base), Irrelevant ($β a)) ←
      (isTriviallyIrrelevant b').map fun x =>
        .lam nm t (.lam nm' t' x bi') bi
    return q(instIrrelevantForall $α $β)
  else
    none

elab "dcomp_tac" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
  let type ← withReducible <| goal.getType'
  let mkApp6 (.const nm [clvl, rlvl]) ctx_base ctx res_base res f_base f := type |
    throwError "invalid goal for dcomp_tac: {type}"
  let prim ←
    if nm = ``DComputable then pure false
    else if nm = ``DPrimrec then pure true
    else throwError "invalid goal for dcomp_tac: {type}"
  have ctx_base : Q(Sort clvl) := ctx_base
  have _ctx : Q(convert_to_new_type% $ctx_base) := ctx
  have res_base : Q($ctx_base → Sort rlvl) := res_base
  have _res : Q(convert_to_new_type% $res_base) := res
  have f_base : Q((c : $ctx_base) → $res_base c) := f_base
  have f : Q(convert_to_new_type% $f_base) := f
  let ctxUniv := mkFreshLevelName (← getLevelNames)
  let mut context := {
    contextUniv := ctxUniv
    localPrimThms := {}
    localCompThms := {}
    zeta := false
  }
  for decl in (← getLCtx) do
    let type ← whnfR decl.type
    if let mkApp6 (.const ``DComputable [tlvl, blvl])
        t_base t b_base b f_base@(.fvar _) f := type then
      --Lean.logInfo decl.toExpr
      have t_base : Q(Sort tlvl) := t_base
      have _t : Q(convert_to_new_type% $t_base) := t
      have b_base : Q($t_base → Sort blvl) := b_base
      have _b : Q(convert_to_new_type% $b_base) := b
      have f_base : Q((x : $t_base) → $b_base x) := f_base
      have f : Q(convert_to_new_type% $f_base) := f
      have e : Q(DComputable $f) := decl.toExpr
      context := withBasicLocalThm.newContext false q($f) q($e) context
    else if let mkExtraApp ty x@(.fvar _) := type then
      let mkApp4 (.const ``New.Forall [u, v]) α_base α β_base β := ty | continue
      let .lam nm t (.lam nm' t' b' bi') bi := β | continue
      have α_base : Q(Sort u) := α_base
      have α : Q(convert_to_new_type% $α_base) := α
      have β_base : Q($α_base → Sort v) := β_base
      have β : Q(convert_to_new_type% $β_base) := β
      let some b'irrel := isTriviallyIrrelevant b' | continue
      have _inst : Q(∀ ⦃a_base : $α_base⦄ (a : $α.1 a_base), Irrelevant ($β a)) :=
        .lam nm t (.lam nm' t' b'irrel bi') bi
      have x : Q((a : $α_base) → $β_base a) := x
      have f : Q((New.Forall $α $β).1 $x) := decl.toExpr
      have e : Q(DPrimrec $f) := q((DPrimrec.irrelevant))
      context := withBasicLocalThm.newContext true q($f) q($e) context
  let baseMap ← populateBaseMap
  let res ← (solveDPrimGoal prim q($f_base) q($f)).run context |>.run baseMap |>.run
  goal.assign res

end DPrimrec.Tactic
