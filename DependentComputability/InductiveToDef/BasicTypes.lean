import Lean

/-!
# Basic types that can be used to build all others
-/

section RawInductive

open Lean Elab Parser Command

syntax rawCtor := "\n| " ident Term.typeSpec

syntax rawInductiveType := "\n| " ident Term.typeSpec

syntax rawInductive := atomic(declModifiers "raw_inductive ") declId Term.typeSpec rawCtor*

def elabRawInductiveDecl (nparams : Nat) (inducts : TSyntaxArray ``rawInductive) (addInductDecl : Declaration → TermElabM Unit) :
    TermElabM Unit := do
  let mut inductMods : Array (Name × Name × Modifiers) := #[]
  let mut lvls : List Name := []
  for induct in inducts do
    let `(rawInductive| $mod:declModifiers raw_inductive $id:declId : $_:term $_:rawCtor*) := induct |
      throwUnsupportedSyntax
    let modifiers ← Elab.elabModifiers mod
    let res ← Elab.expandDeclId (← getCurrNamespace) [] id modifiers
    let theLvls := res.levelNames.reverse
    if lvls.isEmpty then
      lvls := theLvls
    else if !theLvls.isEmpty && lvls != theLvls then
      throwError "level name mismatch: {lvls} vs {theLvls}"
    inductMods := inductMods.push (res.declName, res.shortName, modifiers)
  Term.withLevelNames lvls do
    let mut inductTypes : Array Expr := #[]
    for induct in inducts do
      let `(rawInductive| $_ raw_inductive $_:declId : $ty:term $_:rawCtor*) := induct |
        throwUnsupportedSyntax
      let type ← Term.elabType ty
      Term.synthesizeSyntheticMVarsNoPostponing
      inductTypes := inductTypes.push type
    let rec addAuxDecls (i : Nat) (vars : Array Expr) : TermElabM Unit := do
      if h : i < inductTypes.size then
        Meta.withAuxDecl inductMods[i]!.1 inductTypes[i] inductMods[i]!.2.1 fun var =>
          addAuxDecls (i + 1) (vars.push var)
      else
        let mut inductiveTypes : Array InductiveType := #[]
        let levelParams := lvls.map Level.param
        let replacements : Array Expr := inductMods.map (.const ·.1 levelParams)
        for induct in inducts, (nm, _, _) in inductMods, ty in inductTypes do
          let `(rawInductive| $_ raw_inductive $_:declId : $_:term $ctors:rawCtor*) := induct |
            throwUnsupportedSyntax
          let mut constructors : Array Constructor := #[]
          for ctor in ctors do
            let `(rawCtor| | $id : $ty:term) := ctor | throwUnsupportedSyntax
            let type ← Term.elabType ty
            Term.synthesizeSyntheticMVarsNoPostponing
            let type := type.replaceFVars vars replacements
            let type ← eraseRecAppSyntaxExpr type
            constructors := constructors.push {
              name := id.getId
              type := ← instantiateMVars type
            }
          inductiveTypes := inductiveTypes.push {
            name := nm
            type := ← instantiateMVars ty
            ctors := constructors.toList
          }
        let decl : Declaration := .inductDecl lvls nparams inductiveTypes.toList (inductMods.any (·.2.2.isUnsafe))
        Term.ensureNoUnassignedMVars decl
        addInductDecl decl
    termination_by inductTypes.size - i
    addAuxDecls 0 #[]
    let levelParams := lvls.map Level.param
    for induct in inducts, (nm, _, _) in inductMods do
      let `(rawInductive| $_ raw_inductive $id:declId : $_:term $ctors:rawCtor*) := induct |
        throwUnsupportedSyntax
      addDeclarationRangesFromSyntax nm id
      Term.addTermInfo' (isBinder := true) id (.const nm levelParams)
      for ctor in ctors do
        let `(rawCtor| | $id : $ty:term) := ctor | throwUnsupportedSyntax
        addDeclarationRangesFromSyntax id.getId id
        Term.addTermInfo' (isBinder := true) id (.const id.getId levelParams)

elab "raw_inductive_decl " params:num inducts:rawInductive* : command => do
  liftTermElabM do
    elabRawInductiveDecl params.getNat inducts fun decl => do
      addDecl decl

end RawInductive

/-
raw_inductive_decl 2
  raw_inductive RawSigma.{u, v} : (α : Sort u) → (β : (x : α) → Sort v) → Sort (max u v)
    | RawSigma.mk : {α : Sort u} → {β : (x : α) → Sort v} → (a : α) → (b : β a) → RawSigma α β

raw_inductive_decl 2
  raw_inductive RawWType.{u, v} : (α : Sort u) → (β : (x : α) → Sort v) → Sort (max u v)
    | RawWType.mk : {α : Sort u} → {β : (x : α) → Sort v} → (a : α) → (f : β a → RawWType α β) → RawWType α β
-/

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
set_option genInjectivity false in
inductive RawSigma (α : Sort u) (β : α → Sort v) : Sort (max u v) where
  | mk (a : α) (b : β a)

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
set_option genInjectivity false in
inductive RawULift.{v, u} (α : Sort u) : Sort (max u v) where
  | up (down : α)

inductive PWType (α : Sort u) (β : α → Sort v) : Sort (max 1 u v) where
  | mk (a : α) (f : β a → PWType α β)
