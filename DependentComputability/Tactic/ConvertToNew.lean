import DependentComputability.SortExtra
import DependentComputability.Tactic.Delab

open Lean Meta Qq
@[inline]
def withNewVars (vars : Array Expr)
    (step : (expr type : Expr) → (extraMap : FVarIdMap Expr) →
      MonadCacheT ExprStructEq Expr MetaM Expr)
    (k : Array Expr → FVarIdMap Expr → MonadCacheT ExprStructEq Expr MetaM α) : MetaM α := do
  (go 0 {} #[]).run
where
  go (i : Nat := 0) (extraMap : FVarIdMap Expr) (newVars : Array Expr := #[]) :
      MonadCacheT ExprStructEq Expr MetaM α := do
    if h : i < vars.size then
      let varExpr := vars[i]
      let var := varExpr.fvarId!
      let decl ← var.getDecl
      let nm := decl.userName
      let type := decl.type
      let bi := decl.binderInfo
      let newType ← step varExpr type extraMap
      withLocalDecl (nm.appendAfter "_extra") bi newType fun newVar => do
        go (i + 1) (extraMap.insert var newVar) (newVars.push newVar)
    else
      k newVars extraMap
  termination_by vars.size - i

def Array.interleave (as bs : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (acc : Array α) : Array α :=
    if h : i < as.size ∧ i < bs.size then
      go (i + 1) (acc.push as[i] |>.push bs[i])
    else
      acc
  termination_by as.size - i

/--
Given `xss : Array (Array α)` as an array of length `n` where all elements have size `m`,
returns `#[xss[0][0], ..., xs[m - 1][0], xs[1][0], ..., xs[m - 1][n - 1]]`.
-/
partial def Array.flattenSideways (xss : Array (Array α)) : Array α :=
  go 0 0 #[]
where
  go (i j : Nat) (acc : Array α) : Array α :=
    if h : j < xss.size then
      if h : i < xss[j].size then
        go i (j + 1) (acc.push xss[j][i])
      else
        acc
    else
      go (i + 1) 0 acc

def Array.steps (as : Array α) (start step : Nat) : Array α :=
  if h : step = 0 then
    #[]
  else
    go start #[] h
where
  go (i : Nat) (acc : Array α) (h : step ≠ 0) : Array α :=
    if h' : i < as.size then
      go (i + step) (acc.push as[i]) h
    else
      acc
  termination_by as.size - i

def convertTypeSimpleNew (e ty : Expr) (extraMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM Expr := do
  return mkExtraApp (← conversionStepNew.visit ty extraMap) e

def convertInductType (all : List Name) (e ty : Expr) (extraMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM Expr := do
  if ty.find? (fun | .const nm _ => all.contains nm | _ => false) |>.isSome then
    forallTelescopeReducing (whnfType := true) ty fun vars body => do
    withNewVars.go vars convertTypeSimpleNew
        (i := 0) (newVars := #[]) (extraMap := extraMap) fun newVars extraMap => do
    withImplicitBinderInfos vars do
      body.withApp fun fn args => do
        let .const nm us := fn | throwError "unsupported {fn}"
        unless all.contains nm do
          throwError "unsupported {nm} (2)"
        let newArgs ← args.mapM (fun arg => conversionStepNew.visit arg extraMap)
        let fullArgs := args.interleave newArgs
        let eapp := mkAppN e vars
        let body := .app (mkAppN (.const (mkNewInductName nm) us) fullArgs) eapp
        mkForallFVars (vars.interleave newVars) body
  else
    convertTypeSimpleNew e ty extraMap

def mkNewInductEncodingName (nm : Name) : Name :=
  .str (mkNewName nm) "_encoding"

def transformNewTypeToEncoding (e : Expr) (newVar nat : Expr) : MetaM Expr := do
  if let mkExtraApp ty base := e then
    return mkApp3 (.proj ``SortExtra 1 ty) base newVar nat
  else
    e.withApp fun fn args => do
      let .const (.str nm "_induct") us := fn |
        throwError "Invalid type {e}, reflexive inductives are not supported yet"
      return mkApp2 (mkAppN (.const (.str nm "_encoding") us) args) newVar nat

def toNewEncodingInductiveType (info : InductiveVal) : MetaM InductiveType := do
  let ind := info.name
  let levels := info.levelParams.map Level.param
  let newInductName := mkNewInductName info.name
  let newEncodingName := mkNewInductEncodingName info.name
  let mut ctors : Array Constructor := #[]
  let indType ← forallTelescopeReducing info.type fun vars _ => do
    withNewVars vars convertTypeSimpleNew fun newVars _ => do
    withImplicitBinderInfos vars do
      let allVars := vars.interleave newVars
      let body := .forallE `n Nat.mkType (.sort levelZero) .default
      let extra := .app (mkAppN (.const newInductName levels) allVars) (.bvar 0)
      let body := .forallE `t_extra extra body .default
      let body := .forallE `t (mkAppN (.const ind levels) vars) body .strictImplicit
      mkForallFVars (vars.interleave newVars) body
  let ctorCount := info.numCtors
  for h : ctorIdx in *...ctorCount do
    let ctor := info.ctors[ctorIdx]
    let newCtorName := newInductName ++ ctor.replacePrefix ind .anonymous
    let newCtorVal ← getConstInfoCtor newCtorName
    let newCtor ← forallTelescope newCtorVal.type fun vars body => do
      let rec go (i : Nat) (nats : Array Q(Nat)) (allVars : Array Expr) : MetaM Constructor := do
        if h : i + 1 < vars.size then
          let baseVar := vars[i]
          let newVar := vars[i + 1]
          let allVars := allVars.push baseVar |>.push newVar
          if ← isProof baseVar then
            return ← go (i + 2) nats allVars
          let nm ← newVar.fvarId!.getUserName
          withImplicitBinderInfos #[newVar] do
          withLocalDecl (nm.appendAfter "_n") .implicit Nat.mkType fun natVar => do
            let encType ← transformNewTypeToEncoding (← inferType newVar) newVar natVar
            withLocalDeclD (nm.appendAfter "_enc") encType fun encVar =>
              go (i + 2) (nats.push natVar) (allVars.push natVar |>.push encVar)
        else
          body.withApp fun fn args => do
          assert! fn.isConst
          let newCtorApp := mkAppN (.const newCtorName levels) vars
          let encoding := if nats.isEmpty then
              mkApp2 (mkConst ``Nat.pair) (mkRawNatLit 0) (mkRawNatLit (ctorIdx + 1))
            else
              let nats := nats.push (mkRawNatLit (ctorIdx + 1))
              let first := nats[0]!
              nats.foldl (mkApp2 (mkConst ``Nat.pair)) first (start := 1)
          let ctorType := mkApp2 (mkAppN (.const newEncodingName levels) args) newCtorApp encoding
          let ctorType ← mkForallFVars allVars ctorType
          return {
            name := newEncodingName ++ ctor.replacePrefix ind .anonymous
            type := ctorType
          }
      termination_by vars.size - i
      let nparams := newCtorVal.numParams
      go nparams #[] (vars.take nparams)
    ctors := ctors.push newCtor
  return {
    name := newEncodingName
    type := indType
    ctors := ctors.toList
  }

def mkNewStructEncodingInductiveType (info : InductiveVal) : MetaM InductiveType := do
  let ind := info.name
  let levels := info.levelParams.map Level.param
  let newInductName := mkNewInductName info.name
  let newEncodingName := mkNewInductEncodingName info.name
  let indType ← forallTelescopeReducing info.type fun vars _ => do
    withNewVars vars convertTypeSimpleNew fun newVars _ => do
    withImplicitBinderInfos vars do
      let allVars := vars.interleave newVars
      let body := .forallE `n Nat.mkType (.sort levelZero) .default
      let extra := .app (mkAppN (.const newInductName levels) allVars) (.bvar 0)
      let body := .forallE `t_extra extra body .default
      let body := .forallE `t (mkAppN (.const ind levels) vars) body .strictImplicit
      mkForallFVars (vars.interleave newVars) body
  let [ctor] := info.ctors | throwError "internal error"
  let newCtorName := newInductName ++ ctor.replacePrefix ind .anonymous
  let newCtorVal ← getConstInfoCtor newCtorName
  let newCtor ← forallTelescope newCtorVal.type fun vars body => do
    let extra := mkAppN (.const newInductName levels) (vars.take newCtorVal.numParams)
    withLocalDecl `t .implicit extra fun textra => do
    let fields := vars.drop newCtorVal.numParams
    let substs : Array Expr := Array.ofFn fun i : Fin newCtorVal.numFields =>
      .proj newInductName i textra
    let rec go (i : Nat) (nats : Array Q(Nat)) (allVars : Array Expr) : MetaM Constructor := do
      if h : i < vars.size then
        let newVar := vars[i]
        if ← isProof newVar then
          return ← go (i + 1) nats allVars
        let nm ← newVar.fvarId!.getUserName
        withLocalDecl (nm.appendAfter "_n") .implicit Nat.mkType fun natVar => do
          let projIdx := i - newCtorVal.numParams
          let newType ← inferType newVar
          let newType := newType.replaceFVars fields substs
          let encType ← transformNewTypeToEncoding newType
            (.proj newInductName projIdx textra) natVar
          withLocalDeclD (nm.appendAfter "_enc") encType fun encVar =>
            go (i + 1) (nats.push natVar) (allVars.push natVar |>.push encVar)
      else
        body.withApp fun fn args => do
        assert! fn.isConst
        let encoding ← if nats.isEmpty then
            pure (mkRawNatLit 0)
          else
            let first := nats[0]!
            pure <| nats.foldl (mkApp2 (mkConst ``Nat.pair)) first (start := 1)
        let ctorType := mkApp2 (mkAppN (.const newEncodingName levels) args) textra encoding
        let ctorType ← mkForallFVars allVars ctorType
        let ctorName := newEncodingName ++ ctor.replacePrefix ind .anonymous
        return {
          name := ctorName
          type := ctorType
        }
    termination_by vars.size - i
    let nparams := newCtorVal.numParams
    go nparams #[] (vars.take nparams |>.push textra)
  return {
    name := newEncodingName
    type := indType
    ctors := [newCtor]
  }

partial def addNewTypeDecl (info : InductiveVal) (isIrrel : Bool) : MetaM Unit := do
  let ind := info.name
  let lparams' := info.levelParams.map Level.param
  let const := .const ind lparams'
  let newType ← conversionStepNew info.type
  let newType' : Expr := mkExtraApp newType const
  let newValue ← forallTelescopeReducing info.type fun vars _body => do
    withNewVars vars convertTypeSimpleNew fun newVars _extraMap => do
    withImplicitBinderInfos vars do
      let allVars := vars.interleave newVars
      let indTy := mkAppN const vars
      let u ← getLevel indTy
      let extra := mkAppN (.const (mkNewInductName ind) lparams') allVars
      if isIrrel then
        let encoding := mkApp2 (.const ``TrivialEncoding [u]) indTy extra
        let propElim := mkApp2 (.const ``IsPropEncodingTrivial.trivialEncoding [u]) indTy extra
        let constructor := mkApp4 (.const ``SortExtra.mk [u]) indTy extra encoding propElim
        mkLambdaFVars allVars constructor
      else
        let encName := mkNewInductEncodingName info.name
        let encoding := mkAppN (.const encName lparams') allVars
        let propElim := mkApp3 (.const ``IsPropEncodingTrivial.univElim [u]) indTy extra encoding
        let constructor := mkApp4 (.const ``SortExtra.mk [u]) indTy extra encoding propElim
        mkLambdaFVars allVars constructor
  addDecl <| .defnDecl {
    name := mkNewName ind
    levelParams := info.levelParams
    type := newType'
    value := newValue
    hints := .abbrev
    safety := .safe
  }

partial def addNewCtorDecls (info : InductiveVal) : MetaM Unit := do
  let ind := info.name
  let lparams' := info.levelParams.map Level.param
  let newName := mkNewInductName ind
  for ctor in info.ctors do
    let newCtorName := newName ++ ctor.replacePrefix ind .anonymous
    let ctor ← getConstInfoCtor ctor
    let const := .const ctor.name lparams'
    let newType ← conversionStepNew ctor.type
    let newType' : Expr := mkExtraApp newType const
    let newValue : Expr := .const newCtorName lparams'
    addDecl <| .defnDecl {
      name := `New ++ ctor.name
      levelParams := info.levelParams
      type := newType'
      value := newValue
      hints := .abbrev
      safety := if info.isUnsafe then .unsafe else .safe
    }

partial def addNewRecursor (ind : Name) (info : RecursorVal) (recNames : Array Name) :
    MetaM Unit := do
  let nparams := info.numParams
  let lparams' := info.levelParams.map Level.param
  let const := .const info.name lparams'
  let newType ← conversionStepNew info.type
  let newType' : Expr := mkExtraApp newType const
  let newValue ← forallTelescope info.type fun vars _ => do
    withNewVars vars convertTypeSimpleNew fun newVars extraMap => do
    withImplicitBinderInfos vars do
      let allVars := vars.interleave newVars
      let recConst : Expr := .const (mkRecName (mkNewInductName ind)) lparams'
      let params := allVars.extract 0 (nparams * 2)
      let baseMotives := vars.extract nparams (nparams + info.numMotives)
      let motives := newVars.extract nparams (nparams + info.numMotives)
      let baseMinors := vars.extract (nparams + info.numMotives)
        (nparams + info.numMotives + info.numMinors)
      let minors := newVars.extract (nparams + info.numMotives)
        (nparams + info.numMotives + info.numMinors)
      let recBaseParams := vars.extract 0 info.getFirstIndexIdx
      let mut newMotives := #[]
      for motive in motives, recName in recNames do
        let type ← inferType motive
        let newMotive ← forallTelescopeReducing type fun vars _ => do
          let sortExtra := mkAppN motive vars
          let recApp : Expr := mkAppN (.const recName lparams') recBaseParams
          let recApp := mkAppN recApp (vars.steps 0 2)
          let res := mkExtraApp sortExtra recApp
          mkLambdaFVars vars res
        newMotives := newMotives.push newMotive
      let mut newMinors := #[]
      for baseMinor in baseMinors, minor in minors do
        let type ← inferType baseMinor
        let newMinor ← forallTelescopeReducing type fun vars _ => do
          let nonIHVars ← vars.filterM (fun var =>
            return !baseMotives.contains (← inferType var).getForallBody.getAppFn)
          if nonIHVars.size = vars.size then
            -- non-recursive
            return minor
          withNewVars.go nonIHVars convertTypeSimpleNew
              (i := 0) (extraMap := extraMap) (newVars := #[]) fun newVars extraMap => do
            let allNonIHVars := nonIHVars.interleave newVars
            let res := mkAppN minor allNonIHVars
            let ihVars := vars.drop nonIHVars.size
            let rec mkRecGo (i : Nat) (vars : Array Expr) (res : Expr) :
                MonadCacheT ExprStructEq Expr MetaM Expr := do
              if h : i < ihVars.size then
                let ihVar := ihVars[i].fvarId!
                let decl ← ihVar.getDecl
                let type := decl.type
                let name := decl.userName
                let val ← forallTelescope type fun vars body => do
                  body.withApp fun fn args => do
                    let idx := baseMotives.idxOf fn
                    let recName := recNames[idx]!
                    let recApp := mkAppN (.const recName lparams') recBaseParams
                    let recApp := mkAppN recApp args
                    mkLambdaFVars vars recApp
                let newType ← convertTypeSimpleNew val type extraMap
                withLocalDeclD name newType fun newVar => do
                  mkRecGo (i + 1) (vars.push newVar) (mkApp2 res val newVar)
              else
                mkLambdaFVars vars res
            mkRecGo 0 allNonIHVars res
        newMinors := newMinors.push newMinor
      let majors := allVars.extract
        (nparams * 2 + info.numMotives * 2 + info.numMinors * 2)
      let recArgs := params ++ newMotives ++ newMinors ++ majors
      let value := mkAppN recConst recArgs
      mkLambdaFVars allVars value
  addDecl <| .defnDecl {
    name := mkNewName info.name
    levelParams := info.levelParams
    type := newType'
    value := newValue
    hints := .abbrev
    safety := if info.isUnsafe then .unsafe else .safe
  }

def convertStructCtorType (ind : Name) (e : Expr) (ctorType : Expr) (extraMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM Expr := do
  forallTelescope ctorType fun vars body => do
    withNewVars.go vars convertTypeSimpleNew
        (i := 0) (extraMap := extraMap) (newVars := #[]) fun newVars extraMap => do
    withImplicitBinderInfos vars do
      body.withApp fun indConst indArgs => do
        assert! indConst.isConstOf ind
        let newArgs ← indArgs.mapM (fun arg => conversionStepNew.visit arg extraMap)
        let fullArgs := indArgs.interleave newArgs
        let newIndApp := .app (mkAppN
          (.const (mkNewInductName ind) indConst.constLevels!) fullArgs) e
        let res ← mkForallFVars newVars newIndApp
        return res.replaceFVars vars (Array.ofFn fun i : Fin vars.size => .proj ind i e)

def mkNewStructRecursor (rec : RecursorVal) (ctor : ConstructorVal) : MetaM Unit := do
  let levels := rec.levelParams.map Level.param
  let newRecType := mkExtraApp (← conversionStepNew rec.type) (.const rec.name levels)
  forallTelescope rec.type fun vars _body => do
  withNewVars vars convertTypeSimpleNew fun newVars _extraMap => do
  withImplicitBinderInfos vars do
    let params := vars.take rec.numParams
    let newMotive := newVars[rec.numParams]!
    let minor := vars[rec.numParams + 1]!
    let newMinor := newVars[rec.numParams + 1]!
    let major := vars[rec.numParams + 2]!
    let newMajor := newVars[rec.numParams + 2]!
    let recApp := mkAppN (.const rec.name levels) vars
    let newResultType := mkExtraApp (mkApp2 newMotive major newMajor) recApp
    let ourMotive ← mkLambdaFVars #[major] (← mkForallFVars #[newMajor] newResultType)
    let lvl ← getLevel (← inferType major)
    let ourRecApp := .const rec.name (levels.modifyHead lvl.imax)
    let ourRecApp := mkAppN ourRecApp params
    let ourRecApp := ourRecApp.app ourMotive
    let ourMinor ← forallTelescope (← inferType minor) fun fields body => do
      let .app _motive motiveArg := body | throwError "internal error"
      let newMajorType := (← inferType newMajor).replaceFVar major motiveArg
      withLocalDeclD `t newMajorType fun newMajor => do
        let newFields := Array.ofFn fun n : Fin fields.size =>
          .proj (mkNewInductName ctor.induct) n newMajor
        let value := mkAppN newMinor (fields.interleave newFields)
        mkLambdaFVars (fields.push newMajor) value
    let ourRecApp := ourRecApp.app ourMinor
    let vars := (vars.interleave newVars).take ((vars.size - 1) * 2)
    let value ← mkLambdaFVars vars ourRecApp
    addDecl <| .defnDecl {
      name := mkNewName rec.name
      levelParams := rec.levelParams
      type := newRecType
      value := value
      hints := .abbrev
      safety := if rec.isUnsafe then .unsafe else .safe
    }

def convertStructureType (info : InductiveVal) (isIrrel : Bool) : MetaM Unit := do
  let ind := info.name
  let lparams' := info.levelParams.map Level.param
  let indType ← forallTelescopeReducing info.type fun vars body => do
    withNewVars vars convertTypeSimpleNew fun newVars _ => do
    withImplicitBinderInfos vars do
      let body := .forallE `t (mkAppN (.const ind lparams') vars) body .default
      mkForallFVars (vars.interleave newVars) body
  let newName := mkNewInductName info.name
  let ctor := info.ctors[0]!
  let newCtorName := newName ++ ctor.replacePrefix ind .anonymous
  let ctor ← getConstInfoCtor ctor
  let ctorType ← forallTelescopeReducing info.type fun vars _ => do
    withNewVars vars convertTypeSimpleNew fun newVars extraMap => do
    withImplicitBinderInfos vars do
      let indVarType := mkAppN (.const ind lparams') vars
      withLocalDeclD `t indVarType fun indVar => do
        let ctorType ← instantiateForall ctor.type vars
        let ctorType ← convertStructCtorType ind indVar ctorType extraMap
        mkForallFVars (vars.interleave newVars |>.push indVar) ctorType
  let indType := {
    name := newName
    type := indType
    ctors := [{
      name := newCtorName
      type := ctorType
    }]
  }
  addDecl <| .inductDecl info.levelParams (info.numParams * 2 + 1) [indType] info.isUnsafe
  mkCasesOn newName
  unless isIrrel do
    let ty ← mkNewStructEncodingInductiveType info
    addDecl <| .inductDecl info.levelParams (info.numParams * 2 + 2) [ty] info.isUnsafe
    mkCasesOn (mkNewInductEncodingName info.name)
  addNewTypeDecl info isIrrel
  let const := .const ctor.name lparams'
  let newType ← conversionStepNew ctor.type
  let newType' : Expr := mkExtraApp newType const
  let newValue : Expr ← forallTelescope ctor.type fun vars _ => do
    withNewVars vars convertTypeSimpleNew fun newVars _ => do
    withImplicitBinderInfos vars do
      let allVars := vars.interleave newVars
      let allParams := allVars.take (info.numParams * 2)
      let newFields := newVars.drop info.numParams
      let ctorApp := mkAppN const vars
      let res := mkAppN (.app (mkAppN (.const newCtorName lparams') allParams) ctorApp) newFields
      mkLambdaFVars allVars res
  addDecl <| .defnDecl {
    name := `New ++ ctor.name
    levelParams := info.levelParams
    type := newType'
    value := newValue
    hints := .abbrev
    safety := if info.isUnsafe then .unsafe else .safe
  }
  let rec ← getConstInfoRec (mkRecName info.name)
  mkNewStructRecursor rec ctor

def toNewInductiveType (info : InductiveVal) : MetaM InductiveType := do
  if info.isNested then
    throwError "nested {info.name} not supported"
  let ind := info.name
  let all := info.all
  let lparams' := info.levelParams.map Level.param
  let indType ← forallTelescopeReducing info.type fun vars body => do
    withNewVars vars convertTypeSimpleNew fun newVars _ => do
    withImplicitBinderInfos vars do
      let body := .forallE `t (mkAppN (.const ind lparams') vars) body .default
      mkForallFVars (vars.interleave newVars) body
  let newName := mkNewInductName info.name
  let mut ctors : Array Constructor := #[]
  for ctor in info.ctors do
    let newCtorName := newName ++ ctor.replacePrefix ind .anonymous
    let ctor ← getConstInfoCtor ctor
    let ctorType ← forallTelescopeReducing ctor.type fun vars body => do
      withNewVars vars (convertInductType all) fun newVars extraMap => do
      withImplicitBinderInfos vars do
        let ctorApp := mkAppN (.const ctor.name lparams') vars
        let body ← convertInductType all ctorApp body extraMap
        mkForallFVars (vars.interleave newVars) body
    let newCtor : Constructor := {
      name := newCtorName
      type := ctorType
    }
    ctors := ctors.push newCtor
  return {
    name := newName
    type := indType
    ctors := ctors.toList
  }

mutual

partial def convertInductToNew (val : InductiveVal) : MetaM Unit := do
  let all := val.all
  let lparams := val.levelParams
  let nparams := val.numParams
  let recNames := all.toArray.map mkRecName
  let mut types : Array InductiveType := #[]
  for ind in all do
    let info ← getConstInfoInduct ind
    for c in info.type.getUsedConstantsAsSet do
      recConvertToNew c
    for ctor in info.ctors do
      let ctor ← getConstInfoCtor ctor
      for c in ctor.type.getUsedConstantsAsSet do
        unless all.contains c do
          recConvertToNew c
  let lvl ← forallTelescopeReducing (whnfType := true) val.type fun _ body => do
    let .sort u := body | throwTypeExpected body
    pure u
  if let [_] := val.ctors then
    unless val.isRec do
      if val.numIndices = 0 then
        let recVal ← getConstInfoRec (mkRecName val.name)
        if val.levelParams.length < recVal.levelParams.length then
          convertStructureType val (!lvl.isNeverZero)
          return
  for ind in all do
    types := types.push (← toNewInductiveType (← getConstInfoInduct ind))
  let decl : Declaration := .inductDecl lparams (nparams * 2) types.toList val.isUnsafe
  addDecl decl
  if lvl.isNeverZero then
    let mut encTypes : Array InductiveType := #[]
    for ind in all do
      encTypes := encTypes.push (← toNewEncodingInductiveType (← getConstInfoInduct ind))
    let decl : Declaration := .inductDecl lparams (nparams * 2) encTypes.toList val.isUnsafe
    addDecl decl
  for ind in all do
    mkCasesOn (mkNewInductName ind)
    if lvl.isNeverZero then
      mkCasesOn (mkNewInductEncodingName ind)
    let info ← getConstInfoInduct ind
    addNewTypeDecl info (!lvl.isNeverZero)
  for ind in all do
    let info ← getConstInfoInduct ind
    addNewCtorDecls info
    let info ← getConstInfoRec (mkRecName ind)
    addNewRecursor ind info recNames

partial def recConvertToNew (nm : Name) : CoreM Unit := do
  try
    if (← getEnv).contains (mkNewName nm) then
      return
    let info ← getConstInfo nm
    match info with
    | .defnInfo val =>
      let type := val.type
      let value := val.value
      Meta.MetaM.run' do
        let consts := type.getUsedConstantsAsSet.merge value.getUsedConstantsAsSet
        for c in consts do
          recConvertToNew c
        let newType ← conversionStepNew type
        let newValue ← conversionStepNew value
        let newType' : Expr := mkExtraApp newType
          (.const val.name (val.levelParams.map Level.param))
        Lean.addDecl <| .defnDecl {
          name := mkNewName nm
          levelParams := val.levelParams
          type := newType'
          value := newValue
          hints := val.hints
          safety := val.safety
        }
    | .thmInfo val =>
      let type := val.type
      for c in type.getUsedConstantsAsSet do
        recConvertToNew c
      Meta.MetaM.run' do
        let newType ← conversionStepNew type
        let const := .const val.name (val.levelParams.map Level.param)
        let newType' : Expr := mkExtraApp newType const
        -- attempt transfer
        let instType := mkApp2 (.const ``InhabitedExtra [.zero]) type newType
        let mut newValue := default
        if let some inst ← synthInstance? instType then
          newValue := mkApp4 (.const ``InhabitedExtra.default [.zero]) type newType inst const
        else
          let value := val.value
          let consts := value.getUsedConstantsAsSet
          for c in consts do
            recConvertToNew c
          newValue ← conversionStepNew value
        Lean.addDecl <| .thmDecl {
          name := mkNewName nm
          levelParams := val.levelParams
          type := newType'
          value := newValue
        }
    | .opaqueInfo val =>
      let type := val.type
      for c in type.getUsedConstantsAsSet do
        recConvertToNew c
      Meta.MetaM.run' do
        let newType ← conversionStepNew type
        let lvl ← getLevel type
        let const := .const val.name (val.levelParams.map Level.param)
        let newType' : Expr := mkExtraApp newType const
        -- attempt transfer
        let instType := mkApp2 (.const ``InhabitedExtra [lvl]) type newType
        try
          let inst ← synthInstance instType
          let newValue := mkApp4 (.const ``InhabitedExtra.default [lvl]) type newType inst const
          Lean.addDecl <| .opaqueDecl {
            name := mkNewName nm
            levelParams := val.levelParams
            type := newType'
            value := newValue
            isUnsafe := val.isUnsafe
          }
        catch ex =>
          throwError "Failed to translate opaque {.ofConstName nm}\n{ex.toMessageData}"
    | .inductInfo val => (convertInductToNew val).run'
    | .ctorInfo val => recConvertToNew val.induct
    | _ => throwError "unhandled const info {.ofConstName nm}"
  catch ex =>
    let msg := ex.toMessageData ++ m!"\nin {.ofConstName nm}"
    throwError msg

end

initialize
  declConverterRef.set recConvertToNew

elab "convert_to_new " ids:ident+ : command => do
  Lean.Elab.Command.liftCoreM do
    for id in ids do
      let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
      if (← getEnv).contains (mkNewName name) then
        logWarningAt id m!"{name} has already been translated"
      else
        recConvertToNew name
