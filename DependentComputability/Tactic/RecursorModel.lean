import DependentComputability.Tactic.Computability

namespace RecursorModel

inductive FieldInfo where
  | irrelevant
  | nonRec
  | recursive (ind : ℕ)

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

abbrev mkCtor (cidx : ℕ) (vals : List ℕ) : ℕ :=
  Nat.pair (pairAllInv vals) cidx.succ

theorem unpackN_pairAllInv (vals : List ℕ) : unpackN (pairAllInv vals) vals.length = vals := by
  rcases vals with _ | ⟨head, tail⟩
  · simp [pairAllInv, unpackN]
  induction tail generalizing head with
  | nil => simp [unpackN, pairAllInv]
  | cons head' tail ih =>
    simp only [pairAllInv, List.length_cons] at ih ⊢
    simp [unpackN, ih]

theorem recursorModel_mkCtor (descr : MutualInductDescr) (ctx cidx ind : ℕ)
    (vals : List ℕ) (args : List FieldInfo)
    (h : descr.numInducts.ble ind = false)
    (hargs : ((descr.inducts.get ind).get cidx).args = args)
    (h' : vals.length = countNonIrrelevant args) :
    recursorModel descr ctx ind (mkCtor cidx vals) =
      ((descr.inducts.get ind).get cidx).arm
        (pairAll ctx (addIrrelevant vals args ++
          addIHs args vals fun ind val _ => recursorModel descr ctx ind val)) := by
  rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq] at h
  rw [recursorModel, if_neg h, mkCtor, Nat.unpair_pair]
  simp [hargs, ← h', unpackN_pairAllInv]

end RecursorModel

set_option linter.unusedVariables false in
theorem Option.rec.dprim.{c, u_1} {ctx : Sort c}
    {α : ctx → Type u} {motive : (c : ctx) → Option (α c) → Sort u_1}
    {none : (c : ctx) → motive c none} (none_comp : DPrim none)
    {some : (c : ctx) → (a : α c) → motive c (some a)}
    (some_comp : DPrim fun x : PSigma α => some x.1 x.2)
    {t : (c : ctx) → Option (α c)} (t_comp : DPrim t) :
    DPrim (fun c => @Option.rec (α c) (motive c) (none c) (some c) (t c)) := .unsafeIntro

open RecursorModel
theorem _root_.New.Option.rec.dprim.{c, u_1, u} : new_type% @Option.rec.dprim.{c, u_1, u} := by
  intro ctx_base ctx α_base α motive_base motive
  intro none_base none ⟨⟩ ⟨nf, hnf, hnf'⟩
  intro some_base some ⟨⟩ ⟨sf, hsf, hsf'⟩
  intro t_base t ⟨⟩ ⟨tf, htf, htf'⟩
  let descr : MutualInductDescr := {
    numInducts := 1
    inducts := .leaf <| .branch 1
      (.leaf {
        arm := nf
        primrec_arm := hnf
        args := []
      })
      (.leaf {
        arm := sf
        primrec_arm := hsf
        args := [.nonRec]
      })
  }
  refine ⟨fun ctx => recursorModel descr ctx 0 (tf ctx), primrec_recursorModel descr 0 tf htf, ?_⟩
  intro c_base c n hcn
  replace htf' := htf' hcn
  dsimp only
  refine htf'.rec ?_ ?_
  · refine Eq.substr (recursorModel_mkCtor descr n 0 0 [] [] rfl rfl rfl) ?_
    exact hnf' hcn
  · intro val_base val val_n val_comp
    refine Eq.substr (recursorModel_mkCtor descr n 1 0 [val_n] [.nonRec] rfl rfl rfl) ?_
    exact @hsf' ⟨c_base, val_base⟩ ⟨c, val⟩ (Nat.pair n val_n) ⟨hcn, val_comp⟩

set_option linter.unusedVariables false in
theorem List.rec.dprim.{c, u_1} {ctx : Sort c}
    {α : ctx → Type u} {motive : (c : ctx) → List (α c) → Sort u_1}
    {nil : (c : ctx) → motive c []} (nil_comp : DPrim nil)
    {cons : (c : ctx) → (head : α c) → (tail : List (α c)) →
      (ih : motive c tail) → motive c (head :: tail)}
    (cons_comp : DPrim
      fun x : (c : ctx) ×' (head : α c) ×' (tail : List (α c)) ×'
        motive c tail => cons x.1 x.2.1 x.2.2.1 x.2.2.2)
    {t : (c : ctx) → List (α c)} (t_comp : DPrim t) :
    DPrim (fun c => @List.rec (α c) (motive c) (nil c) (cons c) (t c)) := .unsafeIntro

theorem subst_encoding {α_base : Sort u} {α : new_type% α_base}
    {a_base : α_base} {a : new_type% a_base}
    {n m : ℕ} (h : n = m) : α.2 a m → α.2 a n := by
  subst h; exact id

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
  · refine Eq.substr (recursorModel_mkCtor descr n 0 0 [] [] rfl rfl rfl) ?_
    exact hnf' hcn
  · intro head_base head head_n head_enc tail_base tail tail_n tail_enc tail_ih
    refine Eq.substr (recursorModel_mkCtor descr n 1 0 [head_n, tail_n] [.nonRec, .recursive 0] rfl rfl rfl) ?_
    exact @hcf' ⟨c_base, head_base, tail_base, @List.rec (α_base c_base) (motive_base c_base) (nil_base c_base) (cons_base c_base) tail_base⟩
      ⟨c, head, tail, New.List.rec (α c) (motive c) (nil c) (cons c) tail⟩ _
      ⟨hcn, head_enc, tail_enc, tail_ih⟩

namespace RecursorModel

open Lean Meta Qq

partial def mkUncurriedFunctionApp (fn : Expr) (n : Nat) : Expr := Id.run do
  let mut fn := fn
  let mut arg : Expr := .bvar 0
  for _ in *...(n - 1) do
    fn := fn.app (.proj ``PSigma 0 arg)
    arg := arg.proj ``PSigma 1
  return fn.app arg

partial def mkUncurriedFunctionType (ty : Expr) : MetaM <|
    (u v : Level) × (α : Q(Sort u)) × Q($α → Sort v) := do
  if let .forallE nm t e@(.forallE ..) bi := ty then
    let u ← getLevel t
    have t : Q(Sort u) := t
    withLocalDeclQ nm bi q($t) fun var => do
      let e' := e.instantiate1 var
      let ⟨v, w, α, β⟩ ← mkUncurriedFunctionType e'
      let α : Q($t → Sort v) ← mkLambdaFVars #[var] α
      let β : Q((x : $t) → $α x → Sort w) ← mkLambdaFVars #[var] β
      let .lam _ _ (.lam _ _ b _) _ := β | unreachable!
      have resUniv : Level := .normalize <| .max (.max 1 u) v
      have : resUniv =QL max (max 1 u v) := ⟨⟩
      let psigma : Q(Sort resUniv) := q(@PSigma.{u, v} $t $α)
      have bb := b.instantiateRev #[.proj ``PSigma 0 (.bvar 0), .proj ``PSigma 1 (.bvar 0)]
      let newβ : Q($psigma → Sort w) := .lam `x psigma bb .default
      return ⟨resUniv, w, q($psigma), q($newβ)⟩
  else if let .forallE nm t b bi := ty then
    let u ← getLevel t
    have t : Q(Sort u) := t
    withLocalDeclQ nm bi q($t) fun var => do
      let b' := b.instantiate1 var
      let v ← getLevel b'
      return ⟨u, v, t, .lam nm t b bi⟩
  else
    throwError "Invalid input to mkUncurriedFunctionType, expected forall:{indentExpr ty}"

def getNumForalls (e : Expr) : Nat :=
  go e 0
where
  go (e : Expr) (n : Nat) : Nat :=
    match e with
    | .forallE _ _ b _ => go b (n + 1)
    | _ => n

def constructDPrim (e : Expr) : MetaM Expr := do
  let ty ← inferType e
  let ⟨u, v, α, β⟩ ← mkUncurriedFunctionType ty
  let n := getNumForalls ty
  have fn := mkUncurriedFunctionApp e n
  have fn : Q((a : $α) → $β a) :=
    if n = 1 then e else .lam `x α fn .default
  return q(DPrim $fn)

abbrev M := MonadCacheT ExprStructEq Expr MetaM

def withDestructPrimrec (goalType : Q(Prop)) (prims : Array Expr)
    (k : Array ((f : Q(ℕ → ℕ)) × Q(Nat.Primrec $f) × Expr) → M Q($goalType)) :
    M Q($goalType) := do
  go 0 #[]
where
  go (i : Nat) (acc : Array ((f : Q(ℕ → ℕ)) × Q(Nat.Primrec $f) × Expr)) : M Q($goalType) := do
    if h : i < prims.size then
      let decl ← prims[i].fvarId!.getDecl
      let mkExtraApp (mkApp6 (.const ``New.DPrim [u, v]) α α' β β' f f') _ := decl.type |
        unreachable!
      have α : Q(Sort u) := α
      have α' : Q(new_type% $α) := α'
      have β : Q($α → Sort v) := β
      have β' : Q(new_type% $β) := β'
      have f : Q((a : $α) → $β a) := f
      have f' : Q(new_type% $f) := f'
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
        have ⟨f, hf, _⟩ := minorsPrimData[n]!
        q(CtorDescr.mk $f $hf $info)
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

def proveNewRecursorPrimAux (info : RecursorVal) (ctxLvl elimLvl : Level)
    (ctx : Q(Sort ctxLvl)) (newCtx : Q(new_type% $ctx))
    (vars newVars : Array Expr)
    (minorsPrim : Array Expr) (majorPrim : Expr)
    (resultType : Q($ctx → Sort elimLvl)) (extraMap : FVarIdMap Expr) :
    M Expr := do
  let levels := info.levelParams.map Level.param
  let recApp := mkAppN (.const info.name levels) (vars.map (.app · (.bvar 0)))
  have recApp : Q((c : $ctx) → $resultType c) := .lam `c ctx recApp .default
  let newResultType : Q(new_type% $resultType) ← conversionStepNew.visit resultType extraMap
  let newRecApp : Q(new_type% $recApp) ← conversionStepNew.visit recApp extraMap
  let goalType : Q(Prop) := q(DPrimrec $newRecApp)
  withDestructPrimrec goalType (minorsPrim.push majorPrim) fun primData => do
  let ⟨tfn, tprim, tenc⟩ := primData.back!
  let minorsPrimData := primData.pop
  let motives := vars.extract info.numParams info.getFirstMinorIdx
  let minors := vars.extract info.getFirstMinorIdx info.getFirstIndexIdx
  let descrInfo ← mkRecursorModelDescrInfo motives minors
  let descr := infoToModelDescr descrInfo minorsPrimData
  mapLetDecl `descr q(MutualInductDescr) descr fun descrVar => show M Q($goalType) from do
  have descrVar : Q(MutualInductDescr) := descrVar
  let ind := motives.idxOf resultType.bindingBody!.getAppFn
  have indLit : Q(ℕ) := mkRawNatLit ind
  return q(DPrimrec.intro _ (primrec_recursorModel $descrVar $indLit $tfn $tprim) sorry)

open DPrimrec.Tactic.Other
def proveNewRecursorPrim (info : RecursorVal) : MetaM Unit := do
  recConvertToNew info.name
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
  modifyEnv (otherDPrimExt.addEntry · thmInfo)
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
