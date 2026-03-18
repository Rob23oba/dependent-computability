import DependentComputability.Tactic.Computability

namespace RecursorModel

inductive FieldInfo where
  | irrelevant
  | nonRec
  | recursive (ind : ℕ)
deriving Inhabited, Repr

open Lean
structure CtorDescr where
  arm : ℕ → ℕ
  primrec_arm : Nat.Primrec arm
  args : List FieldInfo

structure MutualInductDescr where
  numInducts : Nat
  inducts : RArray (RArray CtorDescr)

def pairAll (x : ℕ) (l : List ℕ) : ℕ :=
  match l with
  | [] => x
  | a :: l => Nat.pair x (pairAll a l)

def pairAllInv (l : List ℕ) : ℕ :=
  l.rec 0 fun x xs _ => List.rec (fun x => x) (fun a _ ih x => ih (Nat.pair x a)) xs x

def countNonIrrelevant (args : List FieldInfo) : ℕ :=
  match args with
  | [] => 0
  | .irrelevant :: args => countNonIrrelevant args
  | _ :: args => countNonIrrelevant args + 1

def unpackN (val : ℕ) (n : ℕ) : List ℕ :=
  match n with
  | 0 => []
  | 1 => [val]
  | k + 1 => (unpackN val k).casesOn [] fun a b => a.unpair.1 :: a.unpair.2 :: b

def addIrrelevant (l : List ℕ) (args : List FieldInfo) : List ℕ :=
  match args with
  | .irrelevant :: args => 0 :: addIrrelevant l args
  | _ :: args => l.casesOn [] fun x xs => x :: addIrrelevant xs args
  | [] => []

theorem le_of_mem_unpackN {x val n : ℕ} (h : x ∈ unpackN val n) : x ≤ val := by
  fun_induction unpackN generalizing x with
  | case1 => contradiction
  | case2 => simp_all
  | case3 k hk heq ih => simp [heq] at h
  | case4 k hk a b heq ih =>
    simp only [heq, List.mem_cons] at h ih
    rcases h with rfl | rfl | h
    · exact a.unpair_left_le.trans (ih (.inl rfl))
    · exact a.unpair_right_le.trans (ih (.inl rfl))
    · exact ih (.inr h)

theorem of_mem_addIrrelevant {x l args} (h : x ∈ addIrrelevant l args) : x ∈ l ∨ x = 0 := by
  fun_induction addIrrelevant with grind

section
variable (a b c d e : ℕ)
example : pairAll a [] = a := rfl
example : pairAll a [b, c, d] = Nat.pair a (Nat.pair b (Nat.pair c d)) := rfl
example : pairAllInv [] = 0 := rfl
example : pairAllInv [a] = a := rfl
example : pairAllInv [a, b, c, d, e] = (((Nat.pair a b).pair c).pair d).pair e := rfl
end

theorem Primrec.rarrayGet [Primcodable β] [Primcodable γ]
    (arr : RArray α) (f : α → β → γ)
    (hf : ∀ a, Primrec (f a)) :
    Primrec₂ fun x y => f (arr.get x) y := by
  rw [RArray.get_eq_getImpl, Primrec₂]
  induction arr with
  | leaf a => simpa [RArray.getImpl] using (hf a).comp .snd
  | branch p l r lih rih =>
    simp only [RArray.getImpl, apply_ite f, ite_apply]
    refine .ite ?_ lih rih
    exact Primrec.nat_lt.comp .fst (.const p)

def addIHs (args : List FieldInfo) (vals : List ℕ)
    (f : (ind : ℕ) → (val : ℕ) → val ∈ vals → ℕ) : List ℕ :=
  match args, vals with
  | .irrelevant :: as, vs => addIHs as vs f
  | .nonRec :: as, v :: vs =>
    addIHs as vs (fun a b h => f a b (.tail v h))
  | .recursive ind :: as, v :: vs =>
    f ind v (.head vs) :: addIHs as vs (fun a b h => f a b (.tail v h))
  | _, _ => []

@[congr]
theorem addIHs_congr {args args' : List FieldInfo} {vals vals' : List ℕ}
    {f : (ind : ℕ) → (val : ℕ) → val ∈ vals → ℕ}
    {f' : (ind : ℕ) → (val : ℕ) → val ∈ vals' → ℕ}
    (hargs : args = args') (hvals : vals = vals')
    (hf : ∀ ind val hval, f ind val (hvals ▸ hval) = f' ind val hval) :
    addIHs args vals f = addIHs args' vals' f' := by
  cases hargs; cases hvals
  cases funext fun a => funext fun b => funext (hf a b)
  rfl

def recursorModel (descr : MutualInductDescr) (ctx : ℕ) (ind : ℕ) (val : ℕ) : ℕ :=
  if ind ≥ descr.numInducts then 0 else
  let cidx := val.unpair.2
  let val := val.unpair.1
  match _ : cidx with
  | 0 => 0
  | cidx + 1 =>
    let cdescr := descr.inducts.get ind |>.get cidx
    let vals := unpackN val (countNonIrrelevant cdescr.args)
    let res := addIrrelevant vals cdescr.args ++
      addIHs cdescr.args vals fun ind val _ => recursorModel descr ctx ind val
    cdescr.arm (pairAll ctx res)
termination_by val
decreasing_by
  rename_i val' _ _ _ _ h'
  have h₁ := le_of_mem_unpackN h'
  simp +zetaDelta only at h₁
  have h₂ := Nat.unpair_lt (n := val') <| Nat.pos_of_ne_zero <| by
    intro; simp_all +zetaDelta
  exact Nat.lt_of_le_of_lt h₁ h₂

def structRecursorModel (descr : CtorDescr) (ctx : ℕ) (val : ℕ) : ℕ :=
  descr.arm (pairAll ctx (addIrrelevant (unpackN val (countNonIrrelevant descr.args)) descr.args))

theorem primrec_unpackN {n : ℕ} : Primrec (unpackN (n := n)) := by
  induction n with
  | zero => simpa [unpackN] using .const []
  | succ k ih =>
    rcases k with _ | k
    · simpa [unpackN] using Primrec.list_cons.comp .id (.const [])
    · refine Primrec.list_casesOn (h := fun _ (x : ℕ × List ℕ) =>
        x.1.unpair.1 :: x.1.unpair.2 :: x.2) ih (.const []) ?_
      have : Primrec fun p : ℕ × ℕ × List ℕ => Nat.unpair p.2.1 :=
        .comp .unpair (.comp .fst .snd)
      refine Primrec.list_cons.comp (.comp .fst this) ?_
      exact Primrec.list_cons.comp (.comp .snd this) (.comp .snd .snd)

theorem primrec_addIrrelevant {args : List FieldInfo} :
    Primrec (addIrrelevant (args := args)) := by
  induction args with
  | nil => simpa [unpackN] using .const []
  | cons head tail ih =>
    rcases head with _ | _ | _
    · simpa [addIrrelevant] using Primrec.list_cons.comp (.const 0) ih
    · simp only [addIrrelevant]
      refine .list_casesOn (h := fun _ x => x.1 :: addIrrelevant x.2 tail) .id (.const []) ?_
      exact Primrec.list_cons.comp (.comp .fst .snd) (ih.comp (.comp .snd .snd))
    · simp only [addIrrelevant]
      refine .list_casesOn (h := fun _ x => x.1 :: addIrrelevant x.2 tail) .id (.const []) ?_
      exact Primrec.list_cons.comp (.comp .fst .snd) (ih.comp (.comp .snd .snd))

theorem primrec_pairAll : Primrec₂ pairAll := by
  let g (x : ℕ) (acc : Option ℕ) : Option ℕ :=
    acc.casesOn (some x) fun a => some (Nat.pair x a)
  have this (x l) : pairAll x l = ((x :: l).foldr g none).get! := by
    induction l generalizing x with
    | nil => simp [pairAll, g]
    | cons head tail ih =>
      simp only [pairAll, ih, List.foldr_cons]
      cases List.foldr _ _ _ <;> simp [g]
  rw [funext fun a => funext (this a)]
  refine Primrec.comp .option_getD_default ?_
  refine Primrec.list_foldr (h := fun (_ : ℕ × List ℕ) (x, (acc : Option ℕ)) => g x acc) ?_ ?_ ?_
  · exact .list_cons
  · exact .const none
  · refine .option_casesOn (.comp .snd .snd) (.comp .option_some (.comp .fst .snd)) ?_
    exact Primrec.comp .option_some (Primrec₂.natPair.comp (.comp .fst (.comp .snd .fst)) .snd)

theorem primrec_addIHs (args : List FieldInfo) :
    Primrec₂ (fun (vals : List ℕ) (ihs : List (List ℕ)) =>
      addIHs args vals fun ind val _ => ihs.getI val |>.getI ind) := by
  induction args with
  | nil => simpa [addIHs] using .const []
  | cons a t ih =>
    rcases a with _ | _ | ind
    · exact ih
    · have (vals : List ℕ) (ihs : List (List ℕ)) :
          addIHs (.nonRec :: t) vals (fun ind val _ => ihs.getI val |>.getI ind) =
            vals.casesOn [] fun v vs =>
              addIHs t vs (fun ind val _ => ihs.getI val |>.getI ind) := by
        cases vals <;> simp [addIHs]
      simp only [*]
      refine .list_casesOn (α := List ℕ × List (List ℕ)) (β := ℕ) (σ := List ℕ)
          (h := fun p (v, vs) => addIHs t vs fun ind val x ↦ (p.2.getI val).getI ind)
          .fst (.const []) ?_
      exact ih.comp (.comp .snd .snd) (.comp .snd .fst)
    · have (vals : List ℕ) (ihs : List (List ℕ)) :
          addIHs (.recursive ind :: t) vals (fun ind val _ => ihs.getI val |>.getI ind) =
            vals.casesOn [] fun v vs =>
              (ihs.getI v |>.getI ind) ::
                addIHs t vs (fun ind val _ => ihs.getI val |>.getI ind) := by
        cases vals <;> simp [addIHs]
      simp only [this]
      refine .list_casesOn (α := List ℕ × List (List ℕ)) (β := ℕ) (σ := List ℕ)
          (h := fun p (v, vs) =>
            (p.2.getI v |>.getI ind) :: addIHs t vs fun ind val x ↦ (p.2.getI val).getI ind)
          .fst (.const []) ?_
      refine Primrec.list_cons.comp ?_ ?_
      · refine Primrec.list_getI.comp ?_ (.const ind)
        exact Primrec.list_getI.comp (.comp .snd .fst) (.comp .fst .snd)
      · exact ih.comp (.comp .snd .snd) (.comp .snd .fst)

theorem primrec_recursorModel (descr : MutualInductDescr) (ind : ℕ)
    (f : ℕ → ℕ) (hf : Nat.Primrec f) :
    Nat.Primrec (fun ctx => recursorModel descr ctx ind (f ctx)) := by
  rw [← Primrec.nat_iff]
  let f₁ (cdescr : CtorDescr) (ihs : List (List ℕ)) (ctx val : ℕ) : ℕ :=
    let vals := unpackN val (countNonIrrelevant cdescr.args)
    let a := addIrrelevant vals cdescr.args ++
      addIHs cdescr.args vals fun ind val _ => ihs.getI val |>.getI ind
    cdescr.arm (pairAll ctx a)
  have hf₁ (cdescr : CtorDescr) : Primrec fun x : List (List ℕ) × ℕ × ℕ =>
      f₁ cdescr x.1 x.2.1 x.2.2 := by
    refine (Primrec.nat_iff.mpr (cdescr.primrec_arm)).comp ?_
    refine primrec_pairAll.comp (.comp .fst .snd) ?_
    refine Primrec.list_append.comp (primrec_addIrrelevant.comp ?hh) ?_
    · exact primrec_unpackN.comp (.comp .snd .snd)
    · exact (primrec_addIHs cdescr.args).comp ?hh .fst
  let f₂ (ihs : List (List ℕ)) (ctx : ℕ) (ind : ℕ) (val : ℕ) : ℕ :=
    if descr.numInducts ≤ ind then 0 else
    if val.unpair.2 = 0 then 0 else
    let cidx := val.unpair.2 - 1
    f₁ (descr.inducts.get ind |>.get cidx) ihs ctx val.unpair.1
  have hf₂ : Primrec fun x : List (List ℕ) × ℕ × ℕ × ℕ =>
      f₂ x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    refine .ite ?_ (.const 0) ?_
    · exact Primrec.nat_le.comp (.const _) (.comp .fst (.comp .snd .snd))
    refine .ite ?_ (.const 0) ?_
    · exact Primrec.eq.comp (.comp .snd (.comp .unpair (.comp .snd (.comp .snd .snd)))) (.const 0)
    · let post (a : RArray CtorDescr) (x : List (List ℕ) × ℕ × ℕ × ℕ) : ℕ :=
        f₁ (a.get (x.2.2.2.unpair.2 - 1)) x.1 x.2.1 x.2.2.2.unpair.1
      refine (Primrec.rarrayGet descr.inducts post ?_).comp (.comp .fst (.comp .snd .snd)) .id
      let post' (a : CtorDescr) (x : List (List ℕ) × ℕ × ℕ × ℕ) : ℕ :=
        f₁ a x.1 x.2.1 x.2.2.2.unpair.1
      intro a
      refine (Primrec.rarrayGet a post' ?_).comp ?_ .id
      · intro a
        refine (hf₁ a).comp (.pair .fst (.pair (.comp .fst .snd) ?_))
        exact .comp .fst (.comp .unpair (.comp .snd (.comp .snd .snd)))
      · refine Primrec.nat_sub.comp ?_ (.const 1)
        exact .comp .snd (.comp .unpair (.comp .snd (.comp .snd .snd)))
  have model_eq (ctx ind val : ℕ) :
      recursorModel descr ctx ind val =
        f₂ (List.range val |>.map fun i => List.range descr.numInducts
          |>.map fun j => recursorModel descr ctx j i) ctx ind val := by
    fun_cases recursorModel with
    | case1 => simp [f₂, *]
    | case2 => simp +zetaDelta [*]
    | case3 hind cidx val' cidx' hcidx' cdescr vals ihs =>
      have hcidx'' : cidx' = cidx - 1 := by simp [hcidx']
      simp +zetaDelta only [↓reduceIte, Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, add_tsub_cancel_right, hind, hcidx']
      rw [hcidx'']; congr; funext ind2 val2 h
      replace h := le_of_mem_unpackN h
      have h₂ := Nat.unpair_lt (n := val) <| Nat.pos_of_ne_zero <| by
        intro; simp_all +zetaDelta
      replace h := h.trans_lt h₂
      simp only [List.getI, List.getD_eq_getElem?_getD, List.length_map, List.length_range, h,
        getElem?_pos, List.getElem_map, List.getElem_range, Option.getD_some, Nat.default_eq_zero,
        List.getElem?_map]
      by_cases hind2 : ind2 < descr.numInducts
      · simp [hind2]
      · unfold recursorModel
        simp [hind2]
  let f₃ (x : ℕ) (l : List (List ℕ)) : Option (List ℕ) :=
    some <| List.range descr.numInducts |>.map fun ind => f₂ l x ind l.length
  let f₄ (x : ℕ) (val : ℕ) : List ℕ :=
    List.range descr.numInducts |>.map fun ind => recursorModel descr x ind val
  have := Primrec.nat_strong_rec (f := f₄) (g := f₃) ?_ ?_
  · replace this := Primrec.list_getI.comp (this.comp .id (Primrec.nat_iff.mpr hf)) (.const ind)
    simp only [List.getI, id_eq, Nat.default_eq_zero, List.getD_eq_getElem?_getD,
      List.getElem?_map, f₄] at this
    by_cases h : ind < descr.numInducts
    · simpa [h] using this
    · simp +singlePass only [recursorModel]
      simpa [not_lt.mp h] using .const 0
  · refine Primrec.comp .option_some ?_
    refine Primrec.list_map (.const _) ?_
    refine hf₂.comp (.pair (.comp .snd .fst) (.pair ?_ (.pair .snd ?_)))
    · exact .comp .fst .fst
    · exact .comp .list_length (.comp .snd .fst)
  · intro ctx val
    simp only [List.length_map, List.length_range, Option.some.injEq, List.map_inj_left,
      List.mem_range, f₃, f₄]
    intro _ _
    rw [model_eq]

theorem primrec_structRecursorModel (descr : CtorDescr)
    (f : ℕ → ℕ) (hf : Nat.Primrec f) :
    Nat.Primrec (fun ctx => structRecursorModel descr ctx (f ctx)) := by
  refine descr.primrec_arm.comp ?_
  rw [← Primrec.nat_iff]
  refine primrec_pairAll.comp .id ?_
  refine primrec_addIrrelevant.comp ?_
  exact primrec_unpackN.comp (Primrec.nat_iff.mpr hf)

def myDescr : MutualInductDescr :=
  ⟨1, .ofArray #[.ofArray #[{
    arm x := x.unpair.2 + 2
    primrec_arm := by
      simpa using Nat.Primrec.comp .add (.pair .right (.const 2))
    args := [.nonRec]
  }, {
    arm x := x.unpair.2 + 42
    primrec_arm := by
      simpa using Nat.Primrec.comp .add (.pair .right (.const _))
    args := [.nonRec]
  }] (by decide)] (by decide)⟩

@[simp]
theorem unpackN_pairAllInv (vals : List ℕ) : unpackN (pairAllInv vals) vals.length = vals := by
  rcases vals with _ | ⟨head, tail⟩
  · simp [pairAllInv, unpackN]
  induction tail generalizing head with
  | nil => simp [unpackN, pairAllInv]
  | cons head' tail ih =>
    simp only [pairAllInv, List.length_cons] at ih ⊢
    simp [unpackN, ih]

theorem recursorModel_pair_pairAllInv (descr : MutualInductDescr) (ctx cidx ind : ℕ)
    (vals : List ℕ) (args : List FieldInfo)
    (h : descr.numInducts.ble ind = false)
    (hargs : ((descr.inducts.get ind).get cidx).args = args)
    (h' : vals.length = countNonIrrelevant args) :
    recursorModel descr ctx ind ((pairAllInv vals).pair cidx.succ) =
      ((descr.inducts.get ind).get cidx).arm
        (pairAll ctx (addIrrelevant vals args ++
          addIHs args vals fun ind val _ => recursorModel descr ctx ind val)) := by
  rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq] at h
  rw [recursorModel, if_neg h, Nat.unpair_pair]
  simp [hargs, ← h']

theorem structRecursorModel_pairAllInv (descr : CtorDescr) (ctx : ℕ) (vals : List ℕ)
    (h' : vals.length = countNonIrrelevant descr.args) :
    structRecursorModel descr ctx (pairAllInv vals) =
      descr.arm (pairAll ctx (addIrrelevant vals descr.args)) := by
  simp [structRecursorModel, ← h']

theorem subst_encoding {α_base : Sort u} {α : new_type% α_base}
    {a_base : α_base} {a : new_type% a_base}
    {n m : ℕ} (h : n = m) : α.2 a m → α.2 a n := by
  subst h; exact id

set_option backward.do.legacy false

open Lean Meta Qq

abbrev M := MonadCacheT ExprStructEq Expr MetaM

set_option backward.do.legacy false in
def withDestructPrimrec (goalType : Q(Prop)) (prims : Array Expr)
    (k : Array ((f : Q(ℕ → ℕ)) × Q(Nat.Primrec $f) × Expr) → M Q($goalType)) :
    M Q($goalType) := do
  go 0 #[]
where
  go (i : Nat) (acc : Array ((f : Q(ℕ → ℕ)) × Q(Nat.Primrec $f) × Expr)) : M Q($goalType) := do
    if h : i < prims.size then
      let decl ← prims[i].fvarId!.getDecl
      let mkExtraApp prim _ := decl.type | unreachable!
      let q(@New.DPrim.{u, v} $α $α' $β $β' $f $f') := prim | unreachable!
      have e : Q(DPrimrec $f') := decl.toExpr
      withLocalDeclDQ (decl.userName.appendAfter "_f") q(ℕ → ℕ) fun fn => do
      withLocalDeclDQ (decl.userName.appendAfter "_fprim") q(Nat.Primrec $fn) fun fnprim => do
      withLocalDeclDQ (decl.userName.appendAfter "_fenc")
        q(∀ ⦃a a_extra n⦄, @($α').2 a a_extra n → (new% $β a).2 (new% $f a) ($fn n))
        fun fnenc => do
      let result ← go (i + 1) (acc.push ⟨fn, fnprim, fnenc⟩)
      let result ← mkLambdaFVars #[fn, fnprim, fnenc] result
      have result : Q((g : ℕ → ℕ) → Nat.Primrec g →
        (∀ ⦃a a_extra n⦄, @($α').2 a a_extra n →
          (new% $β a).2 (new% $f a) (g n)) → $goalType) := result
      return q(($e).casesOn $result)
    else
      k acc

def _root_.Lean.RArray.toExprQ {α : Q(Type u)} {β : Type v} (f : β → Q($α)) (a : RArray β) :
    Q(RArray $α) :=
  let leaf := q(@RArray.leaf.{u} $α)
  let branch := q(@RArray.branch.{u} $α)
  let rec go (a : RArray β) : Q(RArray $α) :=
    match a with
    | .leaf x  => .app leaf (f x)
    | .branch p l r => mkApp3 branch (mkRawNatLit p) (go l) (go r)
  go a

def _root_.Lean.RArray.ofArray! [Inhabited α] (xs : Array α) : RArray α :=
  if h : 0 < xs.size then
    .ofArray xs h
  else
    .leaf default

instance : ToExpr FieldInfo where
  toExpr
    | .irrelevant => q(FieldInfo.irrelevant)
    | .nonRec => q(FieldInfo.nonRec)
    | .recursive n =>
      have lit : Q(ℕ) := mkRawNatLit n
      q(FieldInfo.recursive $lit)
  toTypeExpr := q(FieldInfo)

def infoToModelDescr (info : Array (Array (Nat × List FieldInfo)))
    (minorsPrimData : Array ((f : Q(ℕ → ℕ)) × Q(Nat.Primrec $f) × Expr)) :
    Q(MutualInductDescr) :=
  let resArray : Q(RArray (RArray CtorDescr)) :=
    (RArray.ofArray! info).toExprQ fun entry =>
      (RArray.ofArray! entry).toExprQ fun (n, info) =>
        if h : n < minorsPrimData.size then
          have ⟨f, hf, _⟩ := minorsPrimData[n]
          q(CtorDescr.mk $f $hf $info)
        else
          q(CtorDescr.mk (fun _ => 0) .zero []) -- happens when there are no constructors
  have n : Q(ℕ) := mkRawNatLit info.size
  q(MutualInductDescr.mk $n $resArray)

def mkRecursorModelDescrInfo (motives minors : Array Expr) :
    MetaM (Array (Array (Nat × List FieldInfo))) := do
  let mut byMotive : Array (Array (Nat × List FieldInfo)) := #[]
  let mut minorIdx := 0
  for motive in motives do
    let mut minorsForMotive : Array (Nat × List FieldInfo) := #[]
    while h : minorIdx < minors.size do
      let type ← inferType minors[minorIdx]
      if type.getForallBody.getAppFn != motive then
        break
      let infos ← forallTelescope type fun vars body => do
        let mut infos : Array FieldInfo := #[]
        for var in vars[1...*] do
          let varType ← inferType var
          if let e@(.fvar f) := varType.getForallBody.getAppFn then
            if let some i := motives.idxOf? e then
              let arg := varType.getForallBody.appArg!.getAppFn
              infos := infos.set! (vars.idxOf arg - 1) (.recursive i)
              continue
          if ← isProof var then
            infos := infos.push .irrelevant
          else
            infos := infos.push .nonRec
        return infos.toList
      minorsForMotive := minorsForMotive.push (minorIdx, infos)
      minorIdx := minorIdx + 1
    byMotive := byMotive.push minorsForMotive
  return byMotive

def addIrrelevantToExpr (l : List Q(ℕ)) (args : List FieldInfo) : List Q(ℕ) :=
  match args with
  | .irrelevant :: args => q(nat_lit 0) :: addIrrelevantToExpr l args
  | _ :: args => l.casesOn [] fun x xs => x :: addIrrelevantToExpr xs args
  | [] => []

def addIHsToExpr (args : List FieldInfo) (vals : List Q(ℕ))
    (f : (ind : Q(ℕ)) → (val : Q(ℕ)) → Q(ℕ)) : List Q(ℕ) :=
  match args, vals with
  | .irrelevant :: as, vs => addIHsToExpr as vs f
  | .nonRec :: as, _ :: vs => addIHsToExpr as vs f
  | .recursive ind :: as, v :: vs =>
    f (mkRawNatLit ind) v :: addIHsToExpr as vs f
  | _, _ => []

def pairAllExprs (x : Q(ℕ)) (l : List Q(ℕ)) : Q(ℕ) :=
  match l with
  | [] => x
  | a :: l => q(Nat.pair $x $(pairAllExprs a l))

def createNewEncoding (descr : Q(MutualInductDescr)) (ctx : Q(ℕ))
    (args : List FieldInfo) (nums : List Q(ℕ)) : Q(ℕ) :=
  pairAllExprs ctx (addIrrelevantToExpr nums args ++
    addIHsToExpr args nums fun ind val => q(recursorModel $descr $ctx $ind $val))

def createNewStructEncoding (ctx : Q(ℕ)) (args : List FieldInfo) (nums : List Q(ℕ)) : Q(ℕ) :=
  pairAllExprs ctx (addIrrelevantToExpr nums args)

theorem encodes_proof {p : Prop} {p_extra : new_type% p} {h : p} (h_extra : new_type% h) :
    p_extra.2 h_extra (nat_lit 0) := Irrelevant.encoding _

def constructPSigma (ty : Expr) (args : List Expr) (nfields : Nat)
    (hargs : args ≠ [] := by simp_all) : Expr :=
  let a :: more := args
  match more with
  | [] => if nfields > 0 then a else mkAppN a (ty.getAppArgs.drop 1)
  | more@(b :: as) =>
    match ty with
    | q(PSigma.{u, v} $α $β) =>
      -- nfields = 0 => α is a motive application
      let fst := if nfields > 0 then a else mkAppN a (α.getAppArgs.drop 1)
      let snd := constructPSigma (β.betaRev #[fst]) more (nfields - 1)
      mkApp4 (.const ``PSigma.mk [u, v]) α β fst snd
    | _ => panic! s!"{repr ty} is"

def constructPSigmaEncoding (newSigma : Expr) (fieldInfos : List FieldInfo)
    (encs : List Expr) (encVal : Q(ℕ)) : MetaM Expr := do
  match fieldInfos with
  | .irrelevant :: infos =>
    if infos.isEmpty && encs.isEmpty then
      let mkExtraApp proofType proof ← inferType newSigma | unreachable!
      let prop : Q(Prop) ← inferType proof
      have _proofType : Q(new_type% $prop) := proofType
      have proof : Q($prop) := proof
      have newSigma : Q(new_type% $proof) := newSigma
      return q(encodes_proof $newSigma)
    else
      let q(Nat.pair $xenc $yenc) := encVal | unreachable!
      have : $xenc =Q 0 := ⟨⟩
      have : $encVal =Q Nat.pair $xenc $yenc := ⟨⟩
      let q(@New.PSigma.mk.{u, v} $α $α' $β $β' $x $x' $y $y') := newSigma | unreachable!
      have : u =QL 0 := ⟨⟩
      have xproof : Q($α'.2 $x' $xenc) := q(encodes_proof $x')
      let yproof : Q((new% $β $x).2 $y' $yenc) ← constructPSigmaEncoding y' infos encs yenc
      let proof : Q(@(new% PSigma $β).2 ⟨$x, $y⟩ ⟨$x', $y'⟩ $encVal) :=
        q(⟨$xproof, $yproof⟩)
      return proof
  | _ :: infos | infos =>
    let enc :: encs := encs | unreachable!
    if infos.isEmpty && encs.isEmpty then
      return enc
    else
      let q(Nat.pair $xenc $yenc) := encVal | unreachable!
      have : $encVal =Q Nat.pair $xenc $yenc := ⟨⟩
      let q(@New.PSigma.mk.{u, v} $α $α' $β $β' $x $x' $y $y') := newSigma | unreachable!
      have xproof : Q($α'.2 $x' $xenc) := enc
      let yproof : Q((new% $β $x).2 $y' $yenc) ← constructPSigmaEncoding y' infos encs yenc
      let proof : Q(@(new% PSigma $β).2 ⟨$x, $y⟩ ⟨$x', $y'⟩ $encVal) :=
        q(⟨$xproof, $yproof⟩)
      return proof
termination_by fieldInfos.length + encs.length

def proveEncodingByInduction (info : RecursorVal)
    (descrInfo : Array (Array (ℕ × List FieldInfo)))
    (ctxLvl elimLvl : Level) (ctx : Q(Sort ctxLvl)) (newCtx : Q(new_type% $ctx))
    (vars newVars : Array Expr)
    (minorsPrimData : Array ((f : Q(ℕ → ℕ)) × Q(Nat.Primrec «$f») × Expr))
    (majorFn majorenc : Expr)
    (c : Q($ctx)) (c' : Q(new_type% $c)) (cn : Q(ℕ)) (cenc : Q($newCtx.2 $c' $cn))
    (extraMap : FVarIdMap Expr)
    (modelFn : Q((ind : ℕ) → (val : ℕ) → ℕ))
    (newEncoding : List FieldInfo → List Q(ℕ) → Q(ℕ))
    (modelThm : (cidx : Q(ℕ)) → (ind : Q(ℕ)) → (vals : Q(List ℕ)) →
      (args : Q(List FieldInfo)) → Expr) :
    M Expr := do
  let .str inductName recSuffix := info.name | panic! "invalid recursor name"
  let encodingRecName := .str (mkNewInductEncodingName inductName) recSuffix
  let encodingRecursor ← getConstInfoRec encodingRecName
  let type := encodingRecursor.type
  assert! encodingRecursor.numMotives == info.numMotives &&
    encodingRecursor.numMinors == info.numMinors &&
    encodingRecursor.numParams == info.numParams * 2 &&
    encodingRecursor.numIndices == info.numIndices * 2 + 3
  let levels := info.levelParams.map Level.param
  let encRecLevels := if encodingRecursor.largeElim then .zero :: levels.tail else levels.tail
  let params := (vars.take info.numParams).map (·.app c)
  let newParams := (newVars.take info.numParams).map (mkApp2 · c c')
  let allParams := params.interleave newParams
  let mut type := type.getForallBodyMaxDepth (info.numParams * 2) |>.instantiateRev allParams
  let mut proof := mkAppN (.const encodingRecName encRecLevels) allParams
  let mut motives : Array Expr := #[]
  let nonMajorVars := (vars.take info.getFirstIndexIdx).map (·.app c)
  let newNonMajorVars := (newVars.take info.getFirstIndexIdx).map (mkApp2 · c c')
  let allNonMajorVars := nonMajorVars.interleave newNonMajorVars
  let allRecNames := info.allRecs
  let allRecs := allRecNames.map fun recName =>
    mkAppN (.const recName levels) nonMajorVars
  let allNewRecs := allRecNames.map fun recName =>
    mkAppN (.const (mkNewName recName) levels) allNonMajorVars
  for motiveIdx in *...info.numMotives do
    let .forallE _ motiveType moreType _ := type | unreachable!
    let motive ← forallTelescope motiveType fun motiveVars _ => do
      let numVar : Q(ℕ) := motiveVars[motiveVars.size - 2]! -- encoding number
      let allMajors := motiveVars.pop.pop -- indices and major
      let regularMajors := allMajors.steps 0 2
      let recApp := allRecs[motiveIdx]!
      let newRecApp := allNewRecs[motiveIdx]!
      let newType := mkAppN (mkApp2 newVars[info.numParams + motiveIdx]! c c') allMajors
      let recApp := mkAppN recApp regularMajors
      let newRecApp := mkAppN newRecApp allMajors
      have motiveIdxLit : Q(ℕ) := mkRawNatLit motiveIdx
      let model := q($modelFn $motiveIdxLit $numVar)
      let motive := mkApp3 (.proj ``SortExtra 1 newType) recApp newRecApp model
      mkLambdaFVars motiveVars motive
    type := moreType
    proof := proof.app motive
    motives := motives.push motive
  type := type.instantiateRev motives
  for h : motiveIdx in *...descrInfo.size do
    have motiveIdxLit : Q(ℕ) := mkRawNatLit motiveIdx
    let motiveInfo := descrInfo[motiveIdx]
    for h : cidx in *...motiveInfo.size do
      have minorIdx : Nat := motiveInfo[cidx].1
      have fieldInfos : List FieldInfo := motiveInfo[cidx].2
      let ⟨minorFn, _, minorFnEnc⟩ := minorsPrimData[minorIdx]!
      have cidxLit : Q(ℕ) := mkRawNatLit cidx
      let .forallE minorName minorType moreType _ := type | unreachable!
      let minorProof ← forallTelescope minorType fun minorVars body => do
        let mkApp3 (.proj _ _ newMotiveApp) val val' valenc := body.headBeta | unreachable!
        let mkExtraApp _ motiveApp  ← inferType newMotiveApp | unreachable!
        let mut extraMap := extraMap
        let mut fieldVars := #[]
        let mut varIdx := 0
        let mut numberVars : Array Q(ℕ) := #[]
        let mut encodingProofs := #[]
        let mut ihRecApps := #[]
        for info in fieldInfos do
          let fieldVar := minorVars[varIdx]!
          let newFieldVar := minorVars[varIdx + 1]!
          fieldVars := fieldVars.push fieldVar
          extraMap := extraMap.insert fieldVar.fvarId! newFieldVar
          match info with
          | .irrelevant => varIdx := varIdx + 2
          | _ =>
            numberVars := numberVars.push minorVars[varIdx + 2]!
            encodingProofs := encodingProofs.push minorVars[varIdx + 3]!
            varIdx := varIdx + 4
          if let .recursive i := info then
            ihRecApps := ihRecApps.push allRecs[i]!
        have ihVars := minorVars.drop varIdx
        have vals : Q(List ℕ) := numberVars.foldr (fun val acc => q($val :: $acc)) q([])
        have motiveApp : Q(Sort elimLvl) := motiveApp
        have newMotiveApp : Q(new_type% $motiveApp) := newMotiveApp
        have val : Q($motiveApp) := val
        have val' : Q(new_type% $val) := val'
        have valenc : Q(ℕ) := valenc
        have newenc : Q(ℕ) := newEncoding fieldInfos numberVars.toList
        have thm : Expr := modelThm q($cidxLit) q($motiveIdxLit) q($vals) q($fieldInfos)
        have thm : Q($valenc = $minorFn $newenc) :=
          mkExpectedPropHint thm q($valenc = $minorFn $newenc)
        let .forallE _ encType _ _ ← inferType minorFnEnc | unreachable!
        let sigmaVars := c :: (fieldVars.toList ++ ihRecApps.toList)
        let sigma := constructPSigma encType sigmaVars (fieldVars.size + 1)
        let newSigma ← conversionStepNew.visit sigma extraMap
        let sigmaEnc ← constructPSigmaEncoding newSigma (.nonRec :: fieldInfos)
          (cenc :: (encodingProofs.toList ++ ihVars.toList)) newenc
        have remaining : Q($newMotiveApp.2 $val' ($minorFn $newenc)) :=
          mkApp4 minorFnEnc sigma newSigma newenc sigmaEnc
        let res := q(subst_encoding (a := $val') $thm $remaining)
        mkLambdaFVars minorVars res
      type := moreType
      proof := proof.app minorProof
  let majorVars := (vars.drop info.getFirstIndexIdx).map (·.app c)
  let newMajorVars := (newVars.drop info.getFirstIndexIdx).map (mkApp2 · c c')
  proof := mkAppN proof (majorVars.interleave newMajorVars)
  proof := proof.app (majorFn.app cn)
  proof := proof.app (mkApp4 majorenc c c' cn cenc)
  return proof

set_option backward.do.legacy true in
def proveNewStructRecursorPrimAux (info : RecursorVal) (ctxLvl elimLvl : Level)
    (ctx : Q(Sort ctxLvl)) (newCtx : Q(new_type% $ctx))
    (vars newVars : Array Expr)
    (minorsPrim : Array Expr) (majorPrim : Expr)
    (resultType : Q($ctx → Sort elimLvl)) (extraMap : FVarIdMap Expr) :
    M Expr := do
  let levels := info.levelParams.map Level.param
  let recApp := mkAppN (.const info.name levels) (vars.map (.app · (.bvar 0)))
  have recApp : Q((c : $ctx) → $resultType c) := .lam `c ctx recApp .default
  let _newResultType : Q(new_type% $resultType) ← conversionStepNew.visit resultType extraMap
  let newRecApp : Q(new_type% $recApp) ← conversionStepNew.visit recApp extraMap
  let goalType : Q(Prop) := q(DPrimrec $newRecApp)
  withDestructPrimrec goalType (minorsPrim.push majorPrim) fun primData => do
  let minorPrimData@⟨mfn, mprim, _⟩ := primData[0]! -- minor
  let ⟨tfn, tprim, tenc⟩ := primData[1]! -- major
  let minor := vars[info.numParams + 1]!
  let minorType ← inferType minor
  let infos : List FieldInfo ← forallTelescope minorType fun vars _ => do
    let mut infos : Array FieldInfo := #[]
    for var in vars[1...*] do
      if ← isProof var then
        infos := infos.push .irrelevant
      else
        infos := infos.push .nonRec
    return infos.toList
  let descr := q(CtorDescr.mk $mfn $mprim $infos)
  mapLetDecl `descr q(CtorDescr) descr fun descr => show M Q($goalType) from do
  have descr : Q(CtorDescr) := descr
  withLocalDeclDQ `c q($ctx) fun (c : Q($ctx)) => do
  withLocalDeclDQ `c_extra q($newCtx.1 $c) fun (c' : Q(new_type% $c)) => do
  withLocalDeclDQ `c_n q(ℕ) fun (cn : Q(ℕ)) => do
  withLocalDeclDQ `c_enc q($newCtx.2 $c' $cn) fun (cenc : Q($newCtx.2 $c' $cn)) => do
  let extraMap := extraMap.insert c.fvarId! c'
  let goalType : Q(Prop) := q((new% $resultType $c).2 (new% $recApp $c)
    (structRecursorModel $descr $cn ($tfn $cn)))
  let res : Q($goalType) ← proveEncodingByInduction info #[#[(0, infos)]] ctxLvl elimLvl
    ctx newCtx vars newVars #[minorPrimData] tfn tenc c c' cn cenc extraMap
    (modelFn := q(fun _ => structRecursorModel $descr $cn))
    (newEncoding := createNewStructEncoding cn)
    (modelThm := fun _ _ vals _ =>
      have proof : Q(($vals).length = countNonIrrelevant ($descr).args) :=
        (q(rfl) : Q(($vals).length = ($vals).length))
      q(structRecursorModel_pairAllInv $descr $cn $vals $proof))
  let res : Q(∀ ⦃a : «$ctx»⦄ ⦃a_extra : new_type% a⦄ ⦃n : ℕ⦄, «$newCtx».2 a_extra n →
    (new% «$resultType» a).2 (new% «$recApp» a)
      (structRecursorModel $descr n («$tfn» n))) ←
    mkLambdaFVars #[c, c', cn, cenc] res
  return q(DPrimrec.intro _ (primrec_structRecursorModel $descr $tfn $tprim) $res)

set_option backward.do.legacy true in
def proveNewRecursorPrimAux (info : RecursorVal) (ctxLvl elimLvl : Level)
    (ctx : Q(Sort ctxLvl)) (newCtx : Q(new_type% $ctx))
    (vars newVars : Array Expr)
    (minorsPrim : Array Expr) (majorPrim : Expr)
    (resultType : Q($ctx → Sort elimLvl)) (extraMap : FVarIdMap Expr) :
    M Expr := do
  if info.numIndices = 0 ∧ info.numMinors = 1 ∧ info.numMotives = 1 ∧
      (← isStructureLikeWithLargeElim info.all[0]!) then
    return ← proveNewStructRecursorPrimAux info ctxLvl elimLvl ctx newCtx vars newVars
      minorsPrim majorPrim resultType extraMap
  let levels := info.levelParams.map Level.param
  let recApp := mkAppN (.const info.name levels) (vars.map (.app · (.bvar 0)))
  have recApp : Q((c : $ctx) → $resultType c) := .lam `c ctx recApp .default
  let _newResultType : Q(new_type% $resultType) ← conversionStepNew.visit resultType extraMap
  let newRecApp : Q(new_type% $recApp) ← conversionStepNew.visit recApp extraMap
  let goalType : Q(Prop) := q(DPrimrec $newRecApp)
  withDestructPrimrec goalType (minorsPrim.push majorPrim) fun primData => do
  let ⟨tfn, tprim, tenc⟩ := primData.back!
  let minorsPrimData := primData.pop
  let motives := vars.extract info.numParams info.getFirstMinorIdx
  let minors := vars.extract info.getFirstMinorIdx info.getFirstIndexIdx
  let descrInfo ← mkRecursorModelDescrInfo motives minors
  let descr := infoToModelDescr descrInfo minorsPrimData
  mapLetDecl `descr q(MutualInductDescr) descr fun descr => show M Q($goalType) from do
  have descr : Q(MutualInductDescr) := descr
  let ind := motives.idxOf resultType.bindingBody!.getAppFn
  have indLit : Q(ℕ) := mkRawNatLit ind
  withLocalDeclDQ `c q($ctx) fun (c : Q($ctx)) => do
  withLocalDeclDQ `c_extra q($newCtx.1 $c) fun (c' : Q(new_type% $c)) => do
  withLocalDeclDQ `c_n q(ℕ) fun (cn : Q(ℕ)) => do
  withLocalDeclDQ `c_enc q($newCtx.2 $c' $cn) fun (cenc : Q($newCtx.2 $c' $cn)) => do
  let extraMap := extraMap.insert c.fvarId! c'
  let goalType : Q(Prop) := q((new% $resultType $c).2 (new% $recApp $c)
    (recursorModel $descr $cn $indLit ($tfn $cn)))
  let res : Q($goalType) ← proveEncodingByInduction info descrInfo ctxLvl elimLvl
    ctx newCtx vars newVars minorsPrimData tfn tenc c c' cn cenc extraMap
    (modelFn := q(recursorModel $descr $cn))
    (newEncoding := createNewEncoding q($descr) q($cn))
    (modelThm := fun cidxLit motiveIdxLit vals args =>
      have proof1 : Q(($descr).numInducts.ble $motiveIdxLit = false) := reflBoolFalse
      have proof2 : Q(((($descr).inducts.get $motiveIdxLit).get $cidxLit).args = $args) :=
        (q(rfl) : Q($args = $args))
      have proof3 : Q(($vals).length = countNonIrrelevant $args) :=
        (q(rfl) : Q(($vals).length = ($vals).length))
      q(recursorModel_pair_pairAllInv $descr $cn $cidxLit $motiveIdxLit $vals $args
        $proof1 $proof2 $proof3))
  let res : Q(∀ ⦃a : «$ctx»⦄ ⦃a_extra : new_type% a⦄ ⦃n : ℕ⦄, «$newCtx».2 a_extra n →
    (new% «$resultType» a).2 (new% «$recApp» a)
      (recursorModel «$descr» n «$indLit» («$tfn» n))) ←
    mkLambdaFVars #[c, c', cn, cenc] res
  return q(DPrimrec.intro _ (primrec_recursorModel $descr $indLit $tfn $tprim) $res)

open DCompTac in
def proveNewRecursorPrim (nm : Name) (dummyOnly : Bool := false) : MetaM Unit := do
  recConvertToNew nm
  let info ← getConstInfoRec nm
  unless info.largeElim do return
  let ctxUniv := Elab.Term.mkFreshLevelName info.levelParams
  have ctxLvl := Level.param ctxUniv
  let type := info.type
  withLocalDeclQ `ctx .implicit q(Sort ctxLvl) fun ctx =>
  withLocalDeclQ `ctx_extra .implicit q(new_type% $ctx) fun ctx' =>
  let e := insertContextType type ctx type.getForallArity
  lambdaTelescope e fun vars body => do
  withImplicitBinderInfos vars do
  let extraMap : FVarIdMap Expr := .insert {} ctx.fvarId! ctx'
  MonadCacheT.run <| withNewVars.go vars convertTypeSimpleNew (extraMap := extraMap)
    fun newVars extraMap => do
  let minors := vars.extract info.getFirstMinorIdx info.getFirstIndexIdx
  let minorsPrimInfos ← minors.mapM fun minor => do
    let nm ← minor.fvarId!.getUserName
    let ty ← constructDPrim minor
    return (nm.appendAfter "_prim", ty)
  withLocalDeclsDND minorsPrimInfos fun minorsPrimDummy => do
  withNewVars.go minorsPrimDummy convertTypeSimpleNew (extraMap := extraMap)
    fun minorsPrim extraMap => do
  let major := vars[info.getMajorIdx]!
  let majorPrimType ← constructDPrim major
  withLocalDeclD `t_prim majorPrimType fun majorPrimDummy => do
  withLocalDeclD `t_prim_extra (← convertTypeSimpleNew majorPrimDummy majorPrimType extraMap)
    fun majorPrim => do
  let extraMap := extraMap.insert majorPrimDummy.fvarId! majorPrim
  let paramsAndMotives := vars.take info.getFirstMinorIdx
  let newParamsAndMotives := newVars.take info.getFirstMinorIdx
  let newMinors := newVars.extract info.getFirstMinorIdx info.getFirstIndexIdx
  let indices := vars.extract info.getFirstIndexIdx info.getMajorIdx
  let newIndices := newVars.extract info.getFirstIndexIdx info.getMajorIdx
  let newMajor := newVars[info.getMajorIdx]!
  let dummyVars := #[show Expr from ctx] ++ paramsAndMotives ++
    minors.interleave minorsPrimDummy ++ indices |>.push major |>.push majorPrimDummy
  let allVars : Array Expr := #[ctx, ctx']
  let allVars := allVars ++ paramsAndMotives.interleave newParamsAndMotives
  let allVars := allVars ++ #[minors, newMinors, minorsPrimDummy, minorsPrim].flattenSideways
  let allVars := allVars ++ indices.interleave newIndices
  let allVars := allVars.push major |>.push newMajor |>.push majorPrimDummy |>.push majorPrim
  let levels := info.levelParams.map Level.param
  let recApp := mkAppN (.const info.name levels) (vars.map (.app · (.bvar 0)))
  let recApp : Expr := .lam `c ctx recApp .default
  let .forallE _ _ bodyBody _ := body | unreachable!
  let elimLvl := (← inferType vars[info.numParams]!).getForallBody.sortLevel!
  let dummyType : Expr := mkApp3 (.const ``DPrim [ctxLvl, elimLvl]) ctx
    (.lam `c ctx bodyBody .default) recApp
  let dummyValue : Expr := mkApp3 (.const ``DPrim.unsafeIntro [ctxLvl, elimLvl]) ctx
    (.lam `c ctx bodyBody .default) recApp
  let dummyType ← mkForallFVars dummyVars dummyType
  let dummyValue ← mkLambdaFVars dummyVars dummyValue
  let dummyName := info.name ++ `dprim
  addDecl <| .thmDecl {
    name := dummyName
    levelParams := ctxUniv :: info.levelParams
    type := dummyType
    value := dummyValue
  }
  let thmInfo := {
    prim := true
    declName := info.name
    thmName := dummyName
    paramInfos :=
      Array.replicate info.getFirstMinorIdx .always ++ -- params and motives
        Array.replicate info.numMinors .prim ++ -- minors
        Array.replicate info.numIndices .always ++ -- indices
        #[.prim] -- major
  }
  modifyEnv (dcompExt.addEntry · thmInfo)
  if dummyOnly then return
  let realType ← convertTypeSimpleNew (.const dummyName (ctxLvl :: levels)) dummyType {}
  let realValue ← proveNewRecursorPrimAux info ctxLvl elimLvl ctx ctx' vars newVars
    minorsPrim majorPrim (.lam `c ctx bodyBody .default) extraMap
  let realValue ← mkLambdaFVars allVars realValue
  addDecl <| .thmDecl {
    name := mkNewName dummyName
    levelParams := ctxUniv :: info.levelParams
    type := realType
    value := realValue
  }

end RecursorModel

set_option backward.do.legacy false

open Lean Meta Qq
def constructDComp (e : Expr) : MetaM Expr := do
  let ty ← inferType e
  let some ⟨u, v, α, β⟩ ← matchForallQ ty | unreachable!
  have e : Q((a : $α) → $β a) := e
  return q(DComp $e)

def mkUnitEliminator (info : RecursorVal) (nonMajorVars : Array Expr) : MetaM Expr := do
  let mut recApp : Expr := .const info.name (info.levelParams.map Level.param)
  recApp := mkAppN recApp (nonMajorVars.take info.numParams)
  let mut recType ← inferType recApp
  let mut motiveVarSet : FVarIdSet := {}
  let mut motiveVars : Array Expr := {}
  let mut motives : Array Expr := {}
  let mut lctx ← getLCtx
  for motiveIdx in *...info.numMotives do
    let .forallE nm ty body _ := recType | unreachable!
    let var := nonMajorVars[info.numParams + motiveIdx]!
    let arg ← forallTelescope ty fun vars _ => do
      let app := mkAppN var vars
      let res := .forallE `x (mkConst ``Unit) app .default
      mkLambdaFVars vars res
    let fvar ← mkFreshFVarId
    lctx := lctx.mkLetDecl fvar nm ty arg
    motiveVars := motiveVars.push (.fvar fvar)
    motiveVarSet := motiveVarSet.insert fvar
    motives := motives.push arg
    recApp := recApp.app arg
    recType := body
  recType := recType.instantiateRev motiveVars
  withLCtx' lctx do
  let mut recApp := recApp
  let mut recType := recType
  for minorIdx in *...info.numMinors do
    let var := nonMajorVars[info.getFirstMinorIdx + minorIdx]!
    let .forallE _ ty body _ := recType | unreachable!
    let arg ← forallTelescope ty fun vars _ => do
      let mut res := var
      for var in vars do
        let type ← inferType var
        let .fvar f := type.getForallBody.getAppFn | res := res.app var
        unless motiveVarSet.contains f do
          res := res.app var
          continue
        let arg ← forallTelescope type fun vars _ => do
          mkLambdaFVars vars (.app (mkAppN var vars) (mkConst ``Unit.unit))
        res := res.app arg
      res := .lam `x (mkConst ``Unit) res .default
      mkLambdaFVars vars res
    recApp := recApp.app arg
    recType := body
  return (recApp.abstract motiveVars).instantiateBetaRevRange 0 motives.size motives

def mkFunextFVars (xs : Array Expr) (h : Expr) : MetaM Expr := do
  let q(Eq.{u} $type $lhs $rhs) ← whnfCore (← inferType h) |
    throwError "invalid mkFunExtFVars, expected equality"
  let type ← type.abstractM xs
  let lhs ← lhs.abstractM xs
  let rhs ← rhs.abstractM xs
  let proof ← h.abstractM xs
  let rec go (i : Nat) : MetaM <| (u : Level) × (α : Q(Sort u)) × (a b : Q($α)) × Q($a = $b) := do
    if h : i < xs.size then
      let ⟨v, β, a, b, h⟩ ← go (i + 1)
      let x := xs[i]
      let decl ← x.fvarId!.getDecl
      let nm := decl.userName
      let bi := decl.binderInfo
      let xTy := decl.type
      let u ← getLevel xTy
      let xTy : Q(Sort u) ← xTy.abstractRangeM i xs
      let x : Q($xTy) ← x.abstractRangeM i xs
      have β' : Q($xTy → Sort v) := .lam nm xTy β bi
      have f : Q((a : $xTy) → $β' a) := .lam nm xTy a bi
      have g : Q((a : $xTy) → $β' a) := .lam nm xTy b bi
      have h : Q((a : $xTy) → $f a = $g a) := .lam nm xTy h bi
      let proof : Q($f = $g) := q(funext $h)
      return ⟨u.imax v, .forallE nm xTy β bi, f, g, proof⟩
    else
      return ⟨u, type, lhs, rhs, proof⟩
  termination_by xs.size - i
  let ⟨_u, _α, _a, _b, h⟩ ← go 0
  return h

def mkEliminatorUnitFunEqThm (info : RecursorVal) (nonMajorVars : Array Expr) : MetaM Expr := do
  let elim ← mkUnitEliminator info nonMajorVars
  let elimArgs := elim.getAppArgs
  let levels := info.levelParams.map Level.param
  let mut recApp : Expr := .const info.name (.zero :: levels.tail)
  have elimLvl : Level := .param info.levelParams.head!
  recApp := mkAppN recApp (nonMajorVars.take info.numParams)
  let mut recType ← inferType recApp
  let mut motiveVarSet : FVarIdSet := {}
  let mut motiveVars : Array Expr := {}
  let mut motives : Array Expr := {}
  let mut lctx ← getLCtx
  for motiveIdx in *...info.numMotives, recName in info.allRecs do
    let .forallE nm ty body _ := recType | unreachable!
    let var := nonMajorVars[info.numParams + motiveIdx]!
    let arg ← forallTelescope ty fun vars _ => do
      have ty : Q(Sort elimLvl) := mkAppN var vars
      have lhs : Q($ty) := .app (mkAppN (mkAppN (.const recName levels) elimArgs) vars) q(())
      have rhs : Q($ty) := mkAppN (mkAppN (.const recName levels) nonMajorVars) vars
      mkLambdaFVars vars q($lhs = $rhs)
    let fvar ← mkFreshFVarId
    lctx := lctx.mkLetDecl fvar nm ty arg
    motiveVars := motiveVars.push (.fvar fvar)
    motiveVarSet := motiveVarSet.insert fvar
    motives := motives.push arg
    recApp := recApp.app arg
    recType := body
  recType := recType.instantiateRev motiveVars
  withLCtx' lctx do
  let mut recApp := recApp
  let mut recType := recType
  for minorIdx in *...info.numMinors do
    let var := nonMajorVars[info.getFirstMinorIdx + minorIdx]!
    let varType ← inferType var
    let .forallE _ ty body _ := recType | unreachable!
    let arg ← forallTelescope ty fun vars _ => do
      let mut type := varType
      let mut lhs := var
      let mut rhs := var
      let mut proof? : Option Expr := none
      for var in vars do
        let varType ← inferType var
        let .fvar f := varType.getForallBody.getAppFn |
          assert! proof?.isNone
          lhs := lhs.app var; rhs := lhs; type ← instantiateForall type #[var]
        unless motiveVarSet.contains f do
          assert! proof?.isNone
          lhs := lhs.app var; rhs := lhs; type ← instantiateForall type #[var]
          continue
        let .forallE _ _ bb _ := type | unreachable!
        let v ← getLevel bb
        have bb : Q(Sort v) := bb
        let res ← forallTelescope varType fun vars _ => do
          mkFunextFVars vars (mkAppN var vars)
        let q(Eq.{u} $type' $lhs' $rhs') ← whnfCore (← inferType res) | unreachable!
        have res : Q($lhs' = $rhs') := res
        have lhsQ : Q($type' → $bb) := lhs
        have _rhsQ : Q($type' → $bb) := rhs -- damn you unused variable linter
        proof? := match proof? with
          | none => q(congrArg $lhsQ $res)
          | some (h' : Q($lhsQ = $_rhsQ)) => q(congr $h' $res)
        type := bb
        lhs := lhs.app lhs'
        rhs := rhs.app rhs'
      let mut res ← match proof? with
        | some proof => pure proof
        | none => pure <| mkApp2 (.const ``rfl [← getLevel type]) type lhs
      mkLambdaFVars vars res
    recApp := recApp.app arg
    recType := body
  return (recApp.abstract motiveVars).instantiateBetaRevRange 0 motives.size motives

set_option backward.do.legacy false
open DCompTac in
def proveEliminatorDCompFromDPrim (decl : Name) : MetaM Unit := do
  let info ← getConstInfoRec decl
  unless info.largeElim do return
  let ctxUniv := Elab.Term.mkFreshLevelName info.levelParams
  have ctxLvl : Level := .param ctxUniv
  withLocalDeclQ `ctx .implicit q(Sort ctxLvl) fun (ctx : Q(Sort ctxLvl)) =>
  let e := insertContextType info.type ctx info.type.getForallArity
  lambdaTelescope e fun vars body => do
  let minors := vars.extract info.getFirstMinorIdx info.getFirstIndexIdx
  let minorsCompInfos ← minors.mapM fun minor => do
    let nm ← minor.fvarId!.getUserName
    let ty ← constructDComp minor
    return (nm.appendAfter "_comp", ty)
  withLocalDeclsDND minorsCompInfos fun minorsComp => do
  let major := vars[info.getMajorIdx]!
  let majorCompType ← constructDComp major
  withLocalDeclD `t_comp majorCompType fun majorComp => do
    let ctxUniv' := Elab.Term.mkFreshLevelName (ctxUniv :: info.levelParams)
    let mut compContext : DCompTac.Context := {
      contextUniv := ctxUniv'
      localPrimThms := {}
      localCompThms := {}
      zeta := false
    }
    for comp in minorsComp.push majorComp do
      let q(@DComp.{u, v} $_α $_β $f) ← inferType comp | unreachable!
      have comp : Q(DComp $f) := comp
      compContext := withBasicLocalThm.newContext false q($comp) compContext
    let helperThm ← withLocalDeclD `c ctx fun c => do
      let nonMajorVars := (vars.take info.getFirstIndexIdx).map (·.app c)
      let majorVars := (vars.drop info.getFirstIndexIdx).map (·.app c)
      let thm ← mkEliminatorUnitFunEqThm info nonMajorVars
      let thm := mkAppN thm majorVars
      mkFunextFVars #[c] thm
    let q(Eq.{u} $α $lhs $rhs) ← inferType helperThm | unreachable!
    have helperThm : Q($lhs = $rhs) := helperThm
    let .forallE _ _ bodyBody _ := body | unreachable!
    let elimLvl ← withLocalDeclD `c ctx fun var => getLevel (bodyBody.instantiate1 var)
    have body : Q($ctx → Sort elimLvl) := .lam `c ctx bodyBody .default
    have : u =QL imax ctxLvl elimLvl := ⟨⟩
    have : $α =Q ((c : $ctx) → $body c) := ⟨⟩
    let result : Q(DComp $lhs) ← withLocalDeclDQ `c ctx fun var => do
      let mkApp2 lhs' _ _ := lhs.betaRev #[var] | unreachable!
      let some ⟨v, w, β, γ⟩ ← matchForallQ (← inferType lhs') | unreachable!
      have : w =QL elimLvl := ⟨⟩
      let γ : Q($α → Sort w) ← withLocalDeclD `t α fun var' => do
        mkLambdaFVars #[var'] (γ.betaRev #[var']).bindingBody!
      let β : Q($ctx → Sort v) ← mkLambdaFVars #[var] β
      let γ : Q((c : $ctx) → $β c → Sort w) ← mkLambdaFVars #[var] γ
      let lhs' : Q((c : $ctx) → (a : $β c) → Unit → $γ c a) ← mkLambdaFVars #[var] lhs'
      have major : Q((c : $ctx) → $β c) := major
      have majorComp : Q(DComp $major) := majorComp
      have : $body =Q fun c => $γ c ($major c) := ⟨⟩
      have : $lhs =Q fun c => $lhs' c ($major c) () := ⟨⟩
      let result : Q(DPrim fun c : PSigma $β ↦ $lhs' c.1 c.2) ←
        (solveDPrimGoal true q(fun c : PSigma $β ↦ $lhs' c.1 c.2)).run compContext
      return q(.app (.app (.curry (.of_prim $result)) $majorComp) Unit.unit.dcomp)
    have result : Q(DComp $rhs) := q(Eq.subst $helperThm $result)
    let paramsAndMotives := vars.take info.getFirstMinorIdx
    let indices := vars.extract info.getFirstIndexIdx info.getMajorIdx
    let allVars := #[show Expr from ctx] ++ paramsAndMotives ++
      minors.interleave minorsComp ++ indices |>.push major |>.push majorComp
    let value ← mkLambdaFVars allVars result
    let type ← mkForallFVars allVars q(DComp $rhs)
    let thmName := info.name ++ `dcomp
    addDecl <| .thmDecl {
      name := thmName
      levelParams := ctxUniv :: info.levelParams
      type := type
      value := value
    }
    let thmInfo := {
      prim := false
      declName := info.name
      thmName
      paramInfos :=
        Array.replicate info.getFirstMinorIdx .always ++ -- params and motives
          Array.replicate info.numMinors .computable ++ -- minors
          Array.replicate info.numIndices .always ++ -- indices
          #[.computable] -- major
    }
    modifyEnv (dcompExt.addEntry · thmInfo)

/-!
Special cases we handled manually in SortExtra.lean
-/

set_option linter.hashCommand false

#eval! RecursorModel.proveNewRecursorPrim ``List.rec true
#eval! RecursorModel.proveNewRecursorPrim ``Lean.Syntax.rec true
#eval! RecursorModel.proveNewRecursorPrim ``Array.rec true

@[dcomp]
theorem List.nil.dprim.{c, u} {ctx : Sort c} {α : ctx → Type u} :
    DPrim fun c => @List.nil (α c) := .unsafeIntro

@[dcomp]
theorem List.nil.dcomp.{c, u} {ctx : Sort c} {α : ctx → Type u} :
    DComp fun c => @List.nil (α c) := .of_prim List.nil.dprim

set_option linter.unusedVariables false in
@[dcomp]
theorem List.cons.dprim.{c, u} {ctx : Sort c} {α : ctx → Type u}
    {head : (c : ctx) → α c} (head_prim : DPrim head)
    {tail : (c : ctx) → List (α c)} (tail_prim : DPrim tail) :
    DPrim fun c => @List.cons (α c) (head c) (tail c) := .unsafeIntro

@[dcomp]
theorem List.cons.dcomp.{c, u} {ctx : Sort c} {α : ctx → Type u}
    {head : (c : ctx) → α c} (head_comp : DComp head)
    {tail : (c : ctx) → List (α c)} (tail_comp : DComp tail) :
    DComp fun c => @List.cons (α c) (head c) (tail c) :=
  .app (.app (.curry (.curry (.of_prim <| by dcomp_tac))) head_comp) tail_comp

open RecursorModel Delab
theorem _root_.New.List.rec.dprim.{c, u_1, u} : new_type% @List.rec.dprim.{c, u_1, u} := by
  intro ctx_base ctx α_base α motive_base motive
    nil_base nil ⟨⟩ ⟨nf, hnf, hnf'⟩
    cons_base cons ⟨⟩ ⟨cf, hcf, hcf'⟩
    t_base t ⟨⟩ ⟨tf, htf, htf'⟩
  let descr : MutualInductDescr := {
    numInducts := 1
    inducts := .leaf <| .branch 1
      (.leaf {
        arm := nf
        primrec_arm := hnf
        args := []
      })
      (.leaf {
        arm := cf
        primrec_arm := hcf
        args := [.nonRec, .recursive 0]
      })
  }
  refine ⟨fun ctx => recursorModel descr ctx 0 (tf ctx), primrec_recursorModel descr 0 tf htf, ?_⟩
  intro c_base c n hcn
  replace htf' := htf' hcn
  dsimp only
  refine htf'.rec ?_ ?_
  · refine Eq.substr (recursorModel_pair_pairAllInv descr n 0 0 [] [] rfl rfl rfl) ?_
    exact hnf' hcn
  · intro head_base head head_n head_enc tail_base tail tail_n tail_enc tail_ih
    refine Eq.substr (recursorModel_pair_pairAllInv descr n 1 0 [head_n, tail_n]
      [.nonRec, .recursive 0] rfl rfl rfl) ?_
    exact @hcf' ⟨c_base, head_base, tail_base, @List.rec (α_base c_base) (motive_base c_base)
        (nil_base c_base) (cons_base c_base) tail_base⟩
      ⟨c, head, tail, New.List.rec (α c) (motive c) (nil c) (cons c) tail⟩ _
      ⟨hcn, head_enc, tail_enc, tail_ih⟩

theorem _root_.New.List.nil.dprim.{c, u} : new_type% @List.nil.dprim.{c, u} := by
  intro ctx ctx' α α'
  refine ⟨_, .const (Nat.pair 0 1), ?_⟩
  intros; exact .nil

theorem _root_.New.List.cons.dprim.{c, u} : new_type% @List.cons.dprim.{c, u} := by
  intro ctx ctx' α α' f f' ⟨⟩ ⟨ff, hff, hff'⟩ g g' ⟨⟩ ⟨fg, hfg, hfg'⟩
  refine ⟨_, .pair (.pair hff hfg) (.const 2), ?_⟩
  intro c c' cn hcn
  exact .cons (hff' hcn) (hfg' hcn)

theorem _root_.New.Array.rec.dprim.{c, u_1, u} : new_type% @Array.rec.dprim.{c, u_1, u} := by
  intro c c' α α' m m' l l' ⟨⟩ ⟨fl, hfl, hfl'⟩ t t' ⟨⟩ ⟨ft, hft, hft'⟩
  refine ⟨_, .comp hfl (.pair .id hft), ?_⟩
  intro c c' cn hcn
  exact @hfl' _ (new% ⟨c, (t c).1⟩) (Nat.pair cn (ft cn)) ⟨hcn, (hft' hcn).1⟩

set_option linter.unusedVariables false in
@[dcomp]
theorem Array.mk.dprim.{c, u} {ctx : Sort c} {α : ctx → Type u}
    {toList : (c : ctx) → List (α c)} (toList_prim : DPrim toList) :
    DPrim fun c => @Array.mk (α c) (toList c) := .unsafeIntro

@[dcomp]
theorem Array.mk.dcomp.{c, u} {ctx : Sort c} {α : ctx → Type u}
    {toList : (c : ctx) → List (α c)} (toList_comp : DComp toList) :
    DComp fun c => @Array.mk (α c) (toList c) :=
  .app (.curry (.of_prim <| by dcomp_tac)) toList_comp

@[dcomp]
theorem False.rec.dprim.{c, u} {ctx : Sort c} {motive : ctx → False → Sort u}
    {t : ctx → False} : DPrim fun c ↦ False.rec (motive c) (t c) := .unsafeIntro

@[dcomp]
theorem False.rec.dcomp.{c, u} {ctx : Sort c} {motive : ctx → False → Sort u}
    {t : ctx → False} : DComp fun c ↦ False.rec (motive c) (t c) := .of_prim False.rec.dprim

theorem _root_.New.Array.mk.dprim.{c, u} : new_type% @Array.mk.dprim.{c, u} := by
  intro ctx ctx' m m' t t' ⟨⟩ ⟨f, hf, hf'⟩
  refine ⟨f, hf, ?_⟩
  intro c c' cn hcn
  exact ⟨hf' hcn⟩

theorem _root_.New.False.rec.dprim.{c, u} : new_type% @False.rec.dprim.{c, u} := by
  intro ctx ctx' m m' t t'
  refine ⟨_, .zero, ?_⟩
  intro a
  exact (t a).elim

@[dcomp]
theorem Eq.rec.dprim.{c, u_1, u} {ctx : Sort c} {α : ctx → Sort u} {a : (c : ctx) → α c}
    {motive : (c : ctx) → (b : α c) → a c = b → Sort u_1}
    {refl : (c : ctx) → motive c (a c) (Eq.refl (a c))} (refl_prim : DPrim refl)
    {b : (c : ctx) → α c} {t : (c : ctx) → a c = b c} :
    DPrim fun c ↦ @Eq.rec (α c) (a c) (motive c) (refl c) (b c) (t c) := by
  cases funext t
  apply refl_prim

@[dcomp]
theorem Eq.rec.dcomp.{c, u_1, u} {ctx : Sort c} {α : ctx → Sort u} {a : (c : ctx) → α c}
    {motive : (c : ctx) → (b : α c) → a c = b → Sort u_1}
    {refl : (c : ctx) → motive c (a c) (Eq.refl (a c))} (refl_comp : DComp refl)
    {b : (c : ctx) → α c} {t : (c : ctx) → a c = b c} :
    DComp fun c ↦ @Eq.rec (α c) (a c) (motive c) (refl c) (b c) (t c) := by
  cases funext t
  apply refl_comp

open DCompTac (hasDCompThm hasDPrimThm) in
partial def recAutoDComp (nm : Name) : StateRefT Lean.NameSet CoreM Unit := do
  if ← hasDCompThm nm then
    return
  if (← get).contains nm then
    -- blacklisted as noncomputable
    return
  let info ← getConstInfo nm
  match info with
  | .defnInfo val =>
    handleDependencies val.value
    MetaM.run' <| autoDComp nm
  | .ctorInfo _ =>
    MetaM.run' <| proveConstructorComputable nm
  | .recInfo _ =>
    unless ← hasDPrimThm nm do
      MetaM.run' <| RecursorModel.proveNewRecursorPrim nm
    MetaM.run' <| proveEliminatorDCompFromDPrim nm
  | .thmInfo _ => pure ()
  | .axiomInfo _ => throwError "can't handle axiom {.ofConstName nm}"
  | .opaqueInfo _ => throwError "can't handle opaque {.ofConstName nm}"
  | .quotInfo _ => pure ()
  | .inductInfo _ => pure ()
where
  findDependencies (val : Expr) : MonadCacheT Expr Unit (StateRefT NameSet CoreM) Unit := do
    checkCache val fun _ => withIncRecDepth do
      match val with
      | .const nm _ => modify fun set => set.insert nm
      | .app f a => findDependencies f; findDependencies a
      | .lam _ _ b _ => findDependencies b
      | .letE _ _ v b _ => findDependencies v; findDependencies b
      | .proj t _ e => modify fun set => set.insert (mkRecName t); findDependencies e
      | .mdata _ e => findDependencies e
      | _ => pure ()
  handleDependencies (val : Expr) : StateRefT NameSet CoreM Unit := do
    let mut (_, candidates) ← (findDependencies val).run.run {}
    for c in candidates do
      let env ← getEnv
      try
        recAutoDComp c
      catch _ =>
        setEnv env
        modify fun blacklist => blacklist.insert c

def recAutoDCompMain (nm : Name) : CoreM Unit := do
  StateRefT'.run' (s := {}) do
    let env ← getEnv
    try
      recAutoDComp nm
    catch ex =>
      setEnv env
      throwError "{ex.toMessageData}\nblacklisted: {(← get).toArray}"

initialize
  DCompTac.recAutoDCompDepsRef.set fun e =>
    (recAutoDComp.handleDependencies e).run' {}
