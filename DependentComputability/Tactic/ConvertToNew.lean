import DependentComputability.SortExtra
import DependentComputability.Tactic.Delab

open Lean Meta
@[inline]
def withNonBaseVars (baseVars : Array Expr)
    (step : (expr type : Expr) → (baseMap : FVarIdMap Expr) →
      MonadCacheT ExprStructEq Expr MetaM Expr)
    (k : Array Expr → FVarIdMap Expr → MonadCacheT ExprStructEq Expr MetaM α) : MetaM α := do
  (go 0 {} #[]).run
where
  go (i : Nat) (baseMap : FVarIdMap Expr) (newVars : Array Expr) :
      MonadCacheT ExprStructEq Expr MetaM α := do
    if h : i < baseVars.size then
      let varExpr := baseVars[i]
      let var := varExpr.fvarId!
      let decl ← var.getDecl
      let nm := decl.userName
      let type := decl.type
      let bi := decl.binderInfo
      let lctx ← getLCtx
      let lctx := lctx.setUserName var (nm.appendAfter "_base")
      let lctx := lctx.setBinderInfo var .implicit
      withLCtx' lctx do
        let newType ← step varExpr type baseMap
        withLocalDecl nm bi newType fun newVar => do
          go (i + 1) (baseMap.insert var newVar) (newVars.push newVar)
    else
      k newVars baseMap
  termination_by baseVars.size - i

def Array.interleave (as bs : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (acc : Array α) : Array α :=
    if h : i < as.size ∧ i < bs.size then
      go (i + 1) (acc.push as[i] |>.push bs[i])
    else
      acc
  termination_by as.size - i

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

def convertTypeSimpleNew (e ty : Expr) (baseMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM Expr := do
  return .app (.proj ``SortExtra 0 (← conversionStepNew.visit ty baseMap)) e

def convertInductType (all : List Name) (e ty : Expr) (baseMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM Expr := do
  if ty.find? (fun | .const nm _ => all.contains nm | _ => false) |>.isSome then
    forallTelescopeReducing (whnfType := true) ty fun baseVars body => do
      withNonBaseVars.go baseVars convertTypeSimpleNew
          (i := 0) (newVars := #[]) (baseMap := baseMap) fun newVars baseMap => do
        body.withApp fun fn args => do
          let .const nm us := fn | throwError "unsupported {fn}"
          unless all.contains nm do
            throwError "unsupported {nm} (2)"
          let newArgs ← args.mapM (fun arg => conversionStepNew.visit arg baseMap)
          let fullArgs := args.interleave newArgs
          let eapp := mkAppN e baseVars
          let body := .app (mkAppN (.const (mkNewInductName nm) us) fullArgs) eapp
          mkForallFVars (baseVars.interleave newVars) body
  else
    convertTypeSimpleNew e ty baseMap

partial def addNewTypeDecl (info : InductiveVal) : MetaM Unit := do
  let ind := info.name
  let lparams' := info.levelParams.map Level.param
  let const := .const ind lparams'
  let newType ← conversionStepNew info.type
  let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
  let newValue ← forallTelescopeReducing info.type fun baseVars _body => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars _baseMap => do
      let allVars := baseVars.interleave newVars
      let indTy := mkAppN const baseVars
      let u ← getLevel indTy
      let extra := mkAppN (.const (mkNewInductName ind) lparams') allVars
      let encoding := mkApp2 (.const ``TrivialEncoding [u]) indTy extra
      let propElim := mkApp2 (.const ``IsPropEncodingTrivial.trivialEncoding [u]) indTy extra
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
    let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
    let newValue : Expr := .const newCtorName lparams'
    addDecl <| .defnDecl {
      name := `New ++ ctor.name
      levelParams := info.levelParams
      type := newType'
      value := newValue
      hints := .abbrev
      safety := .safe
    }

partial def addNewRecursor (ind : Name) (info : RecursorVal) (recNames : Array Name) :
    MetaM Unit := do
  let nparams := info.numParams
  let lparams' := info.levelParams.map Level.param
  let const := .const info.name lparams'
  let newType ← conversionStepNew info.type
  let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
  let newValue ← forallTelescope info.type fun baseVars _ => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars baseMap => do
      let allVars := baseVars.interleave newVars
      let recConst : Expr := .const (mkRecName (mkNewInductName ind)) lparams'
      let params := allVars.extract 0 (nparams * 2)
      let baseMotives := baseVars.extract nparams (nparams + info.numMotives)
      let motives := newVars.extract nparams (nparams + info.numMotives)
      let baseMinors := baseVars.extract (nparams + info.numMotives)
        (nparams + info.numMotives + info.numMinors)
      let minors := newVars.extract (nparams + info.numMotives)
        (nparams + info.numMotives + info.numMinors)
      let recBaseParams := baseVars.extract 0 info.getFirstIndexIdx
      let mut newMotives := #[]
      for motive in motives, recName in recNames do
        let type ← inferType motive
        let newMotive ← forallTelescopeReducing type fun vars _ => do
          let sortExtra := mkAppN motive vars
          let recApp : Expr := mkAppN (.const recName lparams') recBaseParams
          let recApp := mkAppN recApp (vars.steps 0 2)
          let res := .app (.proj ``SortExtra 0 sortExtra) recApp
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
          withNonBaseVars.go nonIHVars convertTypeSimpleNew
              (i := 0) (baseMap := baseMap) (newVars := #[]) fun newVars baseMap => do
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
                let newType ← convertTypeSimpleNew val type baseMap
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
    safety := .safe
  }

def convertStructCtorType (ind : Name) (e : Expr) (ctorType : Expr) (baseMap : FVarIdMap Expr) :
    MonadCacheT ExprStructEq Expr MetaM Expr := do
  forallTelescope ctorType fun baseVars body => do
    withNonBaseVars.go baseVars convertTypeSimpleNew
        (i := 0) (baseMap := baseMap) (newVars := #[]) fun newVars baseMap => do
      body.withApp fun indConst indArgs => do
        assert! indConst.isConstOf ind
        let newArgs ← indArgs.mapM (fun arg => conversionStepNew.visit arg baseMap)
        let fullArgs := indArgs.interleave newArgs
        let newIndApp := .app (mkAppN
          (.const (mkNewInductName ind) indConst.constLevels!) fullArgs) e
        let res ← mkForallFVars newVars newIndApp
        return res.replaceFVars baseVars (Array.ofFn fun i : Fin baseVars.size => .proj ind i e)

def mkNewStructRecursor (rec : RecursorVal) (ctor : ConstructorVal) : MetaM Unit := do
  let levels := rec.levelParams.map Level.param
  let newRecType := mkExtraApp (← conversionStepNew rec.type) (.const rec.name levels)
  forallTelescope rec.type fun vars _body => do
  withNonBaseVars vars convertTypeSimpleNew fun newVars _baseMap => do
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
      safety := .safe
    }

mutual

partial def convertStructureType (info : InductiveVal) : MetaM Unit := do
  let ind := info.name
  let lparams' := info.levelParams.map Level.param
  for c in info.type.getUsedConstantsAsSet do
    recConvertToNew c
  let indType ← forallTelescopeReducing info.type fun baseVars body => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars _ => do
      let body := .forallE `t (mkAppN (.const ind lparams') baseVars) body .default
      mkForallFVars (baseVars.interleave newVars) body
  let newName := mkNewInductName info.name
  let ctor := info.ctors[0]!
  let newCtorName := newName ++ ctor.replacePrefix ind .anonymous
  let ctor ← getConstInfoCtor ctor
  for c in ctor.type.getUsedConstantsAsSet do
    if c != ind then
      recConvertToNew c
  let ctorType ← forallTelescopeReducing info.type fun baseVars _ => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars baseMap => do
      let indVarType := mkAppN (.const ind lparams') baseVars
      withLocalDeclD `t indVarType fun indVar => do
        let ctorType ← instantiateForall ctor.type baseVars
        let ctorType ← convertStructCtorType ind indVar ctorType baseMap
        mkForallFVars (baseVars.interleave newVars |>.push indVar) ctorType
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
  addNewTypeDecl info
  let const := .const ctor.name lparams'
  let newType ← conversionStepNew ctor.type
  let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
  let newValue : Expr ← forallTelescope ctor.type fun baseVars _ => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars _ => do
      let allVars := baseVars.interleave newVars
      let allParams := allVars.take (info.numParams * 2)
      let newFields := newVars.drop info.numParams
      let ctorApp := mkAppN const baseVars
      let res := mkAppN (.app (mkAppN (.const newCtorName lparams') allParams) ctorApp) newFields
      mkLambdaFVars allVars res
  addDecl <| .defnDecl {
    name := `New ++ ctor.name
    levelParams := info.levelParams
    type := newType'
    value := newValue
    hints := .abbrev
    safety := .safe
  }
  let rec ← getConstInfoRec (mkRecName info.name)
  mkNewStructRecursor rec ctor

partial def toNewInductiveType (info : InductiveVal) : MetaM InductiveType := do
  if info.isNested then
    throwError "nested {info.name} not supported"
  let ind := info.name
  let all := info.all
  let lparams' := info.levelParams.map Level.param
  for c in info.type.getUsedConstantsAsSet do
    recConvertToNew c
  let indType ← forallTelescopeReducing info.type fun baseVars body => do
    withNonBaseVars baseVars convertTypeSimpleNew fun newVars _ => do
      let body := .forallE `t (mkAppN (.const ind lparams') baseVars) body .default
      mkForallFVars (baseVars.interleave newVars) body
  let newName := mkNewInductName info.name
  let mut ctors : Array Constructor := #[]
  for ctor in info.ctors do
    let newCtorName := newName ++ ctor.replacePrefix ind .anonymous
    let ctor ← getConstInfoCtor ctor
    for c in ctor.type.getUsedConstantsAsSet do
      unless all.contains c do
        recConvertToNew c
    let ctorType ← forallTelescopeReducing ctor.type fun baseVars body => do
      withNonBaseVars baseVars (convertInductType all) fun newVars baseMap => do
        let ctorApp := mkAppN (.const ctor.name lparams') baseVars
        let body ← convertInductType all ctorApp body baseMap
        mkForallFVars (baseVars.interleave newVars) body
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

partial def convertInductToNew (val : InductiveVal) : MetaM Unit := do
  if let [_] := val.ctors then
    unless val.isRec do
      if val.numIndices = 0 then
        let recVal ← getConstInfoRec (mkRecName val.name)
        if recVal.levelParams.length > val.levelParams.length then
          convertStructureType val
          return
  let all := val.all
  let lparams := val.levelParams
  let nparams := val.numParams
  let recNames := all.toArray.map mkRecName
  let mut types : Array InductiveType := #[]
  for ind in all do
    types := types.push (← toNewInductiveType (← getConstInfoInduct ind))
  let decl : Declaration := .inductDecl lparams (nparams * 2) types.toList val.isUnsafe
  addDecl decl
  for ind in all do
    mkCasesOn (mkNewInductName ind)
    let info ← getConstInfoInduct ind
    addNewTypeDecl info
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
        let newType' : Expr := .app (.proj ``SortExtra 0 newType)
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
        let newType' : Expr := .app (.proj ``SortExtra 0 newType) const
        -- attempt transfer
        let instType := mkApp2 (.const ``NonemptyExtra [levelZero]) type newType
        let mut newValue := default
        if let some inst ← synthInstance? instType then
          newValue := mkApp4 (.const ``NonemptyExtra.transfer []) type newType inst const
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
