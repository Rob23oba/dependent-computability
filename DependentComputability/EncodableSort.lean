import DependentComputability.Defs

namespace EncodableSort

protected def «Sort».{u} : EncodableSort.{u + 1} where
  ToType := EncodableSort.{u}

protected def Forall (α : EncodableSort.{u}) (β : α → EncodableSort.{v}) :
    EncodableSort.{imax u v} where
  ToType := (a : α) → β a

protected def Nat : EncodableSort where
  ToType := Nat

protected def Nat.zero : EncodableSort.Nat := _root_.Nat.zero
protected def Nat.succ : EncodableSort.Forall EncodableSort.Nat fun _ => EncodableSort.Nat :=
  _root_.Nat.succ

end EncodableSort

open Lean Meta in
partial def conversionStep (e : Expr) : MetaM Expr := do
  let rec visit (e : Expr) : MonadCacheT ExprStructEq Expr MetaM Expr :=
    withTraceNode `debug (fun err => return m!"{exceptEmoji err} Transforming {e}") do
    checkCache { val := e : ExprStructEq } fun _ => Meta.withIncRecDepth do
      match e with
      | .lit _ | .fvar _ | .bvar _ | .mvar _ => return e
      | .mdata m e => return .mdata m (← visit e)
      | .proj t i e => return .proj t i (← visit e)
      | .app f a => return .app (← visit f) (← visit a)
      | .letE nm t v b nd =>
        let newT ← visit t
        let newT' := .proj ``EncodableSort 0 newT
        let v ← visit v
        withLetDecl nm t v (nondep := nd) fun var => do
          let b ← visit (b.instantiate1 var)
          return .letE nm newT' v (b.abstract #[var]) nd
      | .sort u => return .const ``EncodableSort.Sort [u]
      | .const nm us => return .const (`EncodableSort ++ nm) us
      | .forallE nm t b bi =>
        let u ← getLevel t
        let v ← withLocalDecl nm bi t fun a => getLevel (b.instantiate1 a)
        let newT ← visit t
        let newT' := .proj ``EncodableSort 0 newT
        withLocalDecl nm bi t fun var => do
          let b ← visit (b.instantiate1 var)
          return mkApp2 (.const ``EncodableSort.Forall [u, v]) newT
            (.lam nm newT' (b.abstract #[var]) bi)
      | .lam nm t b bi =>
        let newT ← visit t
        let newT' := .proj ``EncodableSort 0 newT
        withLocalDecl nm bi t fun var => do
          let b ← visit (b.instantiate1 var)
          return .lam nm newT' (b.abstract #[var]) bi
  (visit e).run {}

open Lean Elab Term in
elab "convert_to_esort% " t:term : term => do
  let expr ← elabTerm t none
  let expr ← instantiateMVars expr
  conversionStep expr

open Lean Elab Term in
elab "convert_to_esort_type% " t:term : term => do
  let expr ← elabTerm t none
  let expr ← instantiateMVars expr
  let newExpr ← conversionStep expr
  return .proj ``EncodableSort 0 newExpr

open Lean Elab Term in
elab "value_of_new% " t:term : term => do
  let expr ← elabTerm t none
  let .const nm us := expr | throwError "invalid use of value_of_new%"
  let info ← getConstInfo nm
  return info.instantiateValueLevelParams! us

open Lean Meta in
partial def recConvertToESort (nm : Name) : CoreM Unit := do
  if (← getEnv).contains (`EncodableSort ++ nm) then
    return
  let info ← getConstInfo nm
  match info with
  | .defnInfo val =>
    let type := val.type
    let value := val.value
    Meta.MetaM.run' do
      let consts := type.getUsedConstantsAsSet.merge value.getUsedConstantsAsSet
      for c in consts do
        recConvertToESort c
      let newType ← conversionStep type
      let newValue ← conversionStep value
      let newType' : Expr := .proj ``EncodableSort 0 newType
      Lean.addDecl <| .defnDecl {
        name := `EncodableSort ++ nm
        levelParams := val.levelParams
        type := newType'
        value := newValue
        hints := val.hints
        safety := val.safety
      }
  | .opaqueInfo val =>
    let type := val.type
    let value := val.value
    Meta.MetaM.run' do
      let consts := type.getUsedConstantsAsSet.merge value.getUsedConstantsAsSet
      for c in consts do
        recConvertToESort c
      let newType ← conversionStep type
      let newValue ← conversionStep value
      let newType' : Expr := .proj ``EncodableSort 0 newType
      Lean.addDecl <| .opaqueDecl {
        name := `EncodableSort ++ nm
        levelParams := val.levelParams
        type := newType'
        value := newValue
        isUnsafe := val.isUnsafe
      }
  | .thmInfo val =>
    -- TODO: avoid reconstructing the proof (transfer?)
    let type := val.type
    let value := val.value
    Meta.MetaM.run' do
      let consts := type.getUsedConstantsAsSet.merge value.getUsedConstantsAsSet
      for c in consts do
        recConvertToESort c
      let newType ← conversionStep type
      let newValue ← conversionStep value
      let newType' : Expr := .proj ``EncodableSort 0 newType
      Lean.addDecl <| .thmDecl {
        name := `EncodableSort ++ nm
        levelParams := val.levelParams
        type := newType'
        value := newValue
      }
  | .inductInfo _ =>
    throwError "unhandled const info {.ofConstName nm}"
  | _ => throwError "unhandled const info {.ofConstName nm}"

elab "convert_to_esort " id:ident : command => do
  Lean.Elab.Command.liftCoreM do
    let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    recConvertToESort name

namespace EncodableSort

protected def Nat.rec.{u} : convert_to_esort_type% (type_of% @Nat.rec.{u}) :=
  fun motive zero succ t => @_root_.Nat.rec (fun n => (motive n).ToType) zero succ t

protected def PProd.{u, v} : convert_to_esort_type% (type_of% @PProd.{u, v}) :=
  fun α β => {
    ToType := PProd.{u, v} α.ToType β.ToType
  }

protected def PProd.mk.{u, v} : convert_to_esort_type% (type_of% @PProd.mk.{u, v}) :=
  fun α β => @_root_.PProd.mk.{u, v} α.ToType β.ToType

protected def PSigma.{u, v} : convert_to_esort_type% (type_of% @PSigma.{u, v}) :=
  fun α β => {
    ToType := PSigma.{u, v} fun a : α.ToType => (β a).ToType
  }

protected def PSigma.mk.{u, v} : convert_to_esort_type% (type_of% @PSigma.mk.{u, v}) :=
  fun α β => @_root_.PSigma.mk.{u, v} α.ToType fun a => (β a).ToType

protected def PUnit.{u} : convert_to_esort_type% (type_of% @PUnit.{u}) where
  ToType := PUnit.{u}

protected def PUnit.unit.{u} : convert_to_esort_type% (type_of% @PUnit.unit.{u}) :=
  @_root_.PUnit.unit.{u}

protected def OfNat.{u} : convert_to_esort_type% (type_of% @OfNat.{u}) :=
  fun α n => {
    ToType := OfNat.{u} α.ToType n
    Encoding := {
      Encodes n val := EncodingRelation.Encodes n val.ofNat
    }
  }

protected def OfNat.mk.{u} : convert_to_esort_type% (type_of% @OfNat.mk.{u}) :=
  fun α => @_root_.OfNat.mk α.ToType

protected def Eq.{u} : convert_to_esort_type% (type_of% @Eq.{u}) :=
  fun _ a b => {
    ToType := a = b
  }

protected def Eq.refl.{u} : convert_to_esort_type% (type_of% @Eq.refl.{u}) :=
  fun α => @_root_.Eq.refl.{u} α.ToType

protected def Eq.rec.{u, v} : convert_to_esort_type% (type_of% @Eq.rec.{u, v}) :=
  fun α a motive => @_root_.Eq.rec α.ToType a (fun x h => (motive x h).ToType)

convert_to_esort Nat.add
convert_to_esort Nat.mul
convert_to_esort Nat.sub

protected def Iff : convert_to_esort_type% (type_of% @Iff) :=
  fun a b => {
    ToType := Iff a.ToType b.ToType
    Encoding := instEncodingRelationProof
  }

protected def Iff.intro : convert_to_esort_type% (type_of% @Iff.intro) :=
  fun a b => @_root_.Iff.intro a.ToType b.ToType

protected def True : convert_to_esort_type% (type_of% @True) where
  ToType := True
  Encoding := instEncodingRelationProof

protected def True.intro : convert_to_esort_type% (type_of% @True.intro) := ⟨⟩

protected def Nonempty.{u} : convert_to_esort_type% (type_of% @Nonempty.{u}) := fun α => {
  ToType := _root_.Nonempty α.ToType
  Encoding := instEncodingRelationProof
}

protected def Nonempty.intro.{u} : convert_to_esort_type% (type_of% @Nonempty.intro.{u}) :=
  fun _ x => ⟨x⟩

protected def False : convert_to_esort_type% (type_of% @False) where
  ToType := False
  Encoding := instEncodingRelationProof

protected theorem propext : convert_to_esort_type% (type_of% @propext) := by
  intro p q ⟨h, h'⟩
  change p = q
  rcases p with @⟨p, hp, hp'⟩
  rcases q with @⟨q, hq, hq'⟩
  simp only [isProp_prop, forall_const] at hp' hq'
  cases propext ⟨h, h'⟩
  simp +instances only [funext fun a => funext fun b => propext (hp' a b)]
  simp +instances only [funext fun a => funext fun b => propext (hq' a b)]

convert_to_esort eq_comm
convert_to_esort eq_self

protected noncomputable def Classical.choice.{u} :
    convert_to_esort_type% (type_of% @Classical.choice.{u}) := by
  intro α h
  exact _root_.Classical.choice h

protected def Quot.{u} : convert_to_esort_type% (type_of% @Quot.{u}) :=
  fun α r => {
    ToType := @_root_.Quot α.ToType (fun a b => (r a b).ToType)
  }

protected def Quot.mk.{u} : convert_to_esort_type% (type_of% @Quot.mk.{u}) :=
  fun α r => @_root_.Quot.mk α.ToType (fun a b => (r a b).ToType)

protected def Quot.lift.{u, v} : convert_to_esort_type% (type_of% @Quot.lift.{u, v}) :=
  fun α r β => @_root_.Quot.lift α.ToType (fun a b => (r a b).ToType) β.ToType

protected theorem Quot.ind.{u} : convert_to_esort_type% (type_of% @Quot.ind.{u}) :=
  fun α r motive =>
    @_root_.Quot.ind α.ToType (fun a b => (r a b).ToType) (fun q => (motive q).ToType)

protected theorem Quot.sound.{u} : convert_to_esort_type% (type_of% @Quot.sound.{u}) :=
  fun α r => @_root_.Quot.sound α.ToType (fun a b => (r a b).ToType)

convert_to_esort funext
convert_to_esort Quot.rec

end EncodableSort

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
set_option genInjectivity false in
inductive RawSubtype.{u} {α : Sort u} (p : α → Prop) : Sort u where
  | mk (x : α) (h : p x)

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive LiftProp.{u} (p : Prop) : Sort u where
  | intro (h : p)

@[simp]
theorem nonempty_liftProp : Nonempty (LiftProp p) ↔ p := ⟨fun ⟨⟨h⟩⟩ => h, fun h => ⟨⟨h⟩⟩⟩

structure ValidRel.{u} {α : EncodableSort.{u}} {β : Sort u} (r : α.ToType → β → Sort u) : Prop where
  left_total : ∀ a, ∃ b, Nonempty (r a b)
  right_total : ∀ b, ∃ a, Nonempty (r a b)
  square_law : ∀ a b c d, r a c → r b c → r a d → Nonempty (r b d)

noncomputable def ValidRel.leftToRight {α : EncodableSort.{u}} {β : Sort u}
    {r : α.ToType → β → Sort u} (h : ValidRel r) (x : α.ToType) : β :=
  (h.left_total x).choose

noncomputable def ValidRel.rightToLeft {α : EncodableSort.{u}} {β : Sort u}
    {r : α.ToType → β → Sort u} (h : ValidRel r) (x : β) : α.ToType :=
  (h.right_total x).choose

noncomputable def ValidRel.rel_leftToRight {α : EncodableSort.{u}} {β : Sort u}
    {r : α.ToType → β → Sort u} (h : ValidRel r) (x : α.ToType) :
    r x (h.leftToRight x) := (h.left_total x).choose_spec.some

noncomputable def ValidRel.rel_rightToLeft {α : EncodableSort.{u}} {β : Sort u}
    {r : α.ToType → β → Sort u} (h : ValidRel r) (x : β) :
    r (h.rightToLeft x) x := (h.right_total x).choose_spec.some

noncomputable def ValidRel.square {α : EncodableSort.{u}} {β : Sort u}
    {r : α.ToType → β → Sort u} {a b : α} {c d : β}
    (h : ValidRel r) (h₁ : r a c) (h₂ : r b c) (h₃ : r a d) : r b d :=
  (h.square_law a b c d h₁ h₂ h₃).some

theorem ValidRel.eq (α : EncodableSort.{u}) : ValidRel (fun a b : α => LiftProp (a = b)) := by
  constructor
  · intro a
    use a
    simp
  · intro a
    use a
    simp
  · rintro a b c d ⟨rfl⟩ ⟨rfl⟩ ⟨rfl⟩
    simp

/-set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
set_option genInjectivity false in
inductive Sort.Rel.{u} (α : convert_to_esort_type% Sort u) (β : Sort u) : Sort u where
  | mk (f : )-/
  --RawSubtype fun r : α.ToType → β → Sort u => ValidRel r


def Sort.Rel.{u} (α : convert_to_esort_type% Sort u) (β : Sort u) :=
  RawSubtype fun r : α.ToType → β → Sort u => ValidRel r

def Rel.Sort : Sort.Rel EncodableSort.Sort.{u} (Sort u) := .mk Sort.Rel <| by
  constructor
  · intro x
    use x.ToType
    exact ⟨fun a b => LiftProp (a = b), .eq x⟩
  · intro x
    refine ⟨@EncodableSort.mk x ⟨fun n _ => n = 0, by simp⟩, ?_⟩
    constructor
    exact ⟨fun a b => LiftProp (a = b), .eq _⟩
  · intro a b c d h₁ h₂ h₃
    constructor
    refine ⟨?_, ?_⟩
    · sorry
    · sorry

def Rel.Nat : Rel.Sort.1 EncodableSort.Nat Nat := .mk (fun a b => LiftProp (a = b)) <| by simp

def Rel.Forall {α : EncodableSort.Sort.{u}} {α' : Sort u} (αrel : Rel.Sort.1 α α')
    {β : α.ToType → EncodableSort.Sort.{v}} {β' : α' → Sort v}
    (βrel : ∀ {b b'}, αrel.1 b b' → Rel.Sort.1 (β b) (β' b')) :
    Rel.Sort.1 (EncodableSort.Forall α β) ((a : α') → β' a) :=
  .mk (fun x y => ∀ {a a'}, (rel : αrel.1 a a') → (βrel rel).1 (x a) (y a')) <| by
    constructor
    · intro ff
      let gg (x : α') : β' x := (βrel (αrel.2.rel_rightToLeft x)).2.leftToRight (ff _)
      use gg
      constructor
      intro a b hrel
      have := @αrel.2.square
      have rel1 := αrel.2.rel_rightToLeft b
      sorry
    · sorry
    · sorry

#check (convert_to_esort% Sort 3 : convert_to_esort_type% Sort 4)

def Rel.Nonempty : Rel.Forall Rel.Sort.{u} (fun _ => Rel.Sort.{0}) |>.1
    EncodableSort.Nonempty Nonempty := by
  intro α α' rel
  dsimp only
  refine ⟨fun _ _ => True, ?_, ?_, by simp⟩
  · intro ⟨x⟩
    use ⟨rel.2.leftToRight x⟩
    simp
  · intro ⟨x⟩
    use ⟨rel.2.rightToLeft x⟩
    simp

def Rel.Eq : Rel.Forall Rel.Sort.{u} (fun α => Rel.Forall α fun a => Rel.Forall α fun b => Rel.Sort.{0}) |>.1
    EncodableSort.Eq @Eq := by
  intro α α' αrel a a' arel b b' brel
  dsimp only
  refine ⟨fun _ _ => True, ?_, ?_, by simp⟩
  · intro rfl
    simp only [nonempty_prop, exists_prop, and_true]
  · intro rfl
    simp only [nonempty_prop, exists_prop, and_true]
    change a = b
