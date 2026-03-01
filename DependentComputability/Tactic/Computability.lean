import DependentComputability.Tactic.NewDPrimStep
import DependentComputability.Tactic.OtherDPrimStep
import DependentComputability.Tactic.Delab
import DependentComputability.Tactic.LetNew
import DependentComputability.NewDecls

open scoped Delab

open Nat.Partrec Denumerable in
private def selfCallWith (x : ℕ) : Part ℕ :=
  (ofNat Code x.unpair.1).eval x

open Nat.Partrec Denumerable Encodable in
private def thing (selfCallWith : Code) (x : ℕ) : Part ℕ :=
  x.unpaired fun f x => x.unpaired fun x n =>
    (ofNat Code f).eval (Nat.pair n (encode (selfCallWith.curry x)))

open Nat.Partrec Denumerable Encodable in
private def ycomb (thing : Code) (x : ℕ) : Part ℕ :=
  x.unpaired fun f n =>
    (thing.curry f).eval (Nat.pair (encode (thing.curry f)) n)

open Nat.Partrec in
private theorem selfCallWith_part : Nat.Partrec selfCallWith := by
  rw [← Partrec.nat_iff]
  exact Code.eval_part.comp (.comp (.ofNat _) (.comp .fst .unpair)) .id

open Nat.Partrec in
private theorem thing_part (selfCallWith : Code) : Nat.Partrec (thing selfCallWith) := by
  rw [← Partrec.nat_iff]
  refine Code.eval_part.comp (.comp (.ofNat _) (.comp .fst .unpair)) ?_
  have : Computable₂ Nat.pair := by
    refine Primrec.to_comp ?_
    simpa [Primrec] using Nat.Primrec.succ
  refine this.comp ?_ ?_
  · exact .comp .snd (.comp .unpair (.comp .snd .unpair))
  · refine .comp .encode ?_
    refine Code.primrec₂_curry.to_comp.comp (.const _) ?_
    exact .comp .fst (.comp .unpair (.comp .snd .unpair))

open Nat.Partrec in
private theorem ycomb_part (thing : Code) : Nat.Partrec (ycomb thing) := by
  rw [← Partrec.nat_iff]
  have : Computable₂ Nat.pair := by
    refine Primrec.to_comp ?_
    simpa [Primrec] using Nat.Primrec.succ
  refine Code.eval_part.comp ?_ ?_
  · exact Code.primrec₂_curry.to_comp.comp (.const _) (.comp .fst .unpair)
  · refine this.comp ?_ (.comp .snd .unpair)
    refine .comp .encode ?_
    exact Code.primrec₂_curry.to_comp.comp (.const _) (.comp .fst .unpair)

attribute [dprim] New.PSigma.fst.computable New.PSigma.snd.computable New.PSigma.mk.computable
  New.PSigma.fst.primrec New.PSigma.snd.primrec New.PSigma.mk.primrec

attribute [other_dprim] PSigma.fst.dcomp PSigma.snd.dcomp PSigma.mk.dcomp
  PSigma.fst.dprim PSigma.snd.dprim PSigma.mk.dprim

@[dprim]
theorem _root_.New.Subtype.val.computable.{c, u} {ctx : Sort c} {ctx_extra : new_type% ctx}
    {α : ctx → Sort u} {α_extra : new_type% α}
    {p : (c : ctx) → α c → Prop} {p_extra : new_type% p}
    {self : (c : ctx) → Subtype (p c)} {self_extra : new_type% self}
    (self_comp : DComputable (new% self)) :
    DComputable (new% fun c => (self c).val) := by
  obtain ⟨g, hg, hg'⟩ := self_comp
  use g, hg
  simpa using hg'

@[dprim]
theorem _root_.New.Subtype.mk.computable.{c, u} {ctx : Sort c} {ctx_extra : new_type% ctx}
    {α : ctx → Sort u} {α_extra : new_type% α}
    {p : (c : ctx) → α c → Prop} {p_extra : new_type% p}
    {val : (c : ctx) → α c} {val_extra : new_type% val}
    (val_comp : DComputable (new% val))
    {property : (c : ctx) → p c (val c)}
    (property_extra : new_type% property) :
    DComputable (new% fun c => Subtype.mk (val c) (property c)) := by
  obtain ⟨g, hg, hg'⟩ := val_comp
  use g, hg
  simpa using hg'

section

set_option linter.unusedVariables.funArgs false

@[other_dprim]
lemma Subtype.mk.dprim {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Prop}
    {f : (c : ctx) → α c} (hf : DComp f) {g : (c : ctx) → β c (f c)} :
    DComp (fun c => Subtype.mk (f c) (g c)) := .unsafeIntro

@[other_dprim]
lemma Subtype.val.dprim {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Prop}
    {f : (c : ctx) → Subtype (β c)} (hf : DComp f) :
    DComp (fun c => (f c).1) := .unsafeIntro

@[other_dprim]
lemma Subtype.mk.dcomp {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Prop}
    {f : (c : ctx) → α c} (hf : DComp f) {g : (c : ctx) → β c (f c)} :
    DComp (fun c => Subtype.mk (f c) (g c)) := .unsafeIntro

@[other_dprim]
lemma Subtype.val.dcomp {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Prop}
    {f : (c : ctx) → Subtype (β c)} (hf : DComp f) :
    DComp (fun c => (f c).1) := .unsafeIntro

lemma _root_.New.Subtype.mk.dprim.{u, v} : new_type% @Subtype.mk.dprim.{u, v} :=
  fun _ _ _ _ _ _ _ _ _ hf _ _ => New.Subtype.mk.computable hf _
lemma _root_.New.Subtype.val.dprim.{u, v} : new_type% @Subtype.val.dprim.{u, v} :=
  fun _ _ _ _ _ _ _ _ _ hf => New.Subtype.val.computable hf
lemma _root_.New.Subtype.mk.dcomp.{u, v} : new_type% @Subtype.mk.dcomp.{u, v} :=
  fun _ _ _ _ _ _ _ _ _ hf _ _ => New.Subtype.mk.computable hf _
lemma _root_.New.Subtype.val.dcomp.{u, v} : new_type% @Subtype.val.dcomp.{u, v} :=
  fun _ _ _ _ _ _ _ _ _ hf => New.Subtype.val.computable hf

end

convert_to_new Subtype.property

open Nat.Partrec Denumerable in
open Lean Elab Tactic in
theorem _root_.New.Acc.rec.computable.{c, v, u}
    {ctx : Sort c}
    {ctx_extra : new_type% ctx}
    {α : ctx → Sort u}
    {α_extra : new_type% α}
    {r : (c : ctx) → α c → α c → Prop}
    {r_extra : new_type% r}
    {motive : (c : ctx) → (a : α c) → Acc (r c) a → Sort v}
    {motive_extra : new_type% motive}
    {intro : (c : ctx) → (a : α c) →
        (h : ∀ b, r c b a → Acc (r c) b) →
      (ih : ∀ b hb, motive c b (h b hb)) → motive c a (Acc.intro a h)}
    {intro_extra : new_type% intro}
    (intro_comp : DComputable (new% intro))
    {a : (c : ctx) → α c}
    {a_extra : new_type% a}
    (a_comp : DComputable (new% a))
    {t : (c : ctx) → Acc (r c) (a c)}
    {t_extra : new_type% t} :
    DComputable (new% fun c => @Acc.rec
      (α c) (r c) (motive c) (intro c) (a c) (t c)) := by
  by_cases hprop : IsProp.{imax (max (max 1 u) (imax (max 1 u) v)) v}
  · exact .of_isProp @(isProp_of_isProp_imax.{max (max 1 u) (imax (max 1 u) v), v} hprop)
  by_cases hprop : IsProp.{imax (max 1 u) v}
  · exact .of_isProp @(isProp_of_isProp_imax.{max 1 u, v} hprop)
  have_new this' : DComp (fun (c : ctx)
      (f : (a : α c) → (h : ∀ b, r c b a → Acc (r c) b) →
      (ih : ∀ b hb, motive c b (h b hb)) → motive c a (Acc.intro a h)) =>
        fun a : (a : { a : α c // ∀ b, r c b a → Acc (r c) b }) ×'
          ((b : { b : α c // r c b a }) → motive c b (a.2 b b.2)) =>
            f a.1 a.1.2 fun b hb => a.2 ⟨b, hb⟩) := by
    other_dcomp_tac
  have intro_dcomp : DComp intro := .unsafeIntro
  have intro_dcomp_extra : new_type% intro_dcomp := intro_comp
  have_new := this'.app intro_dcomp
  clear this' this'_extra
  obtain ⟨gi, hgi, hgi'⟩ := this_extra
  obtain ⟨ga, hga, hga'⟩ := a_comp
  obtain ⟨scw, hscw⟩ := Code.exists_code.mp selfCallWith_part
  obtain ⟨th, hth⟩ := Code.exists_code.mp (thing_part scw)
  have hyc := ycomb_part th
  refine ⟨_, .comp hyc (.pair hgi hga), ?_⟩
  intro b b_extra n hn
  obtain ⟨na, hna, hna'⟩ := hga' hn
  obtain ⟨ni, hni, hc⟩ := hgi' hn
  let c := Denumerable.ofNat Code ni
  rw [encoding_pi_def ‹_›] at hc
  clear hga' hgi' intro_comp intro_dcomp intro_dcomp_extra this
  revert hna' hc
  run_tac
    let names : Array Lean.Name := #[`t, `a, `intro, `motive, `r, `α]
    let b := mkIdent `b
    let eb := mkIdent `b_extra
    for nm in names do
      let id := mkIdent nm
      let eid := mkIdent (nm.appendAfter "_extra")
      let pid := mkIdent (nm.appendAfter "'")
      let peid := mkIdent (nm.appendAfter "_extra'")
      evalTactic (← `(tactic| let +generalize $peid : new_type% $id $b := $eid $eb))
      evalTactic (← `(tactic| revert $peid))
      evalTactic (← `(tactic| let +generalize $pid := $id $b))
      evalTactic (← `(tactic| revert $pid))
  intro α' α_extra' r' r_extra' motive' motive_extra' intro' intro_extra'
    a' a_extra' t' t_extra' hna' hc
  clear_value α' α_extra' r' r_extra' motive' motive_extra'
    intro' intro_extra' a' a_extra' t' t_extra'
  clear α α_extra r r_extra motive motive_extra intro intro_extra a a_extra t t_extra
  simp only [Part.eq_some_iff.mpr hni, Part.map_eq_map, Part.map_some, Part.eq_some_iff.mpr hna,
    seq_eq_bind_map, Part.bind_eq_bind, Part.bind_some]
  clear hna hni
  induction t_extra' generalizing na with | @intro a a_extra ha ha_extra ih
  have hycomb : ∃ g, (∀ n, (ofNat Code g).eval n = ycomb th (Nat.pair ni n)) ∧
      ycomb th (Nat.pair ni na) = c.eval (Nat.pair na g) := by
    refine ⟨Encodable.encode (scw.curry (Encodable.encode (th.curry ni))), ?_, ?_⟩
    · intro n
      simp [hscw, selfCallWith, ycomb]
    · simp [ycomb, hth, thing, c]
  obtain ⟨g, hg, hg'⟩ := hycomb
  specialize @hc ⟨⟨a, ha⟩,
    fun q => @Acc.rec α' r' motive' intro' q.1 (ha q.1 q.2)⟩
    ⟨⟨a_extra, @ha_extra⟩, fun _ q =>
      New.Acc.rec α_extra' r_extra' motive_extra' intro_extra' q.1 (ha_extra q.1 q.2)⟩
      (Nat.pair na g)
    ⟨by simpa using hna', ?_⟩
  · rw [encoding_pi_def ‹_›]
    intro ⟨y, hy⟩ ⟨y, hy⟩ x h
    obtain ⟨z, hz, hz'⟩ := ih y hy x h.1
    simp only [hg]
    use z, hz, hz'
  simpa only [hg', c] using hc

example : DComputable (new% fun x : Nat => x) := by
  dcomp_tac

set_option linter.unusedVariables false in
@[other_dprim]
lemma Acc.rec.dcomp.{c, v, u}
    {ctx : Sort c} {α : ctx → Sort u} {r : (c : ctx) → α c → α c → Prop}
    {motive : (c : ctx) → (a : α c) → Acc (r c) a → Sort v}
    {intro : ∀ (c : ctx) (a : α c) (h : _) (ih : ∀ b hb, motive _ _ (h b hb)),
      motive c a (Acc.intro a h)} (intro_comp : DComp intro)
    {a : (c : ctx) → α c} (a_comp : DComp a) {t : (c : ctx) → Acc (r c) (a c)} :
    DComp fun c => @Acc.rec (α c) (r c) (motive c) (intro c) (a c) (t c) := .unsafeIntro

lemma New.Acc.rec.dcomp.{c, v, u} : new_type% @Acc.rec.dcomp.{c, v, u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ hi _ _ _ ha _ _ => New.Acc.rec.computable hi ha

@[dprim]
theorem New.PUnit.unit.computable.{u, v} {ctx : Sort u} {ctx_extra : new_type% ctx} :
    DComputable (new% fun _ : ctx => PUnit.unit.{v}) := by
  refine .const' (x_extra := new% PUnit.unit.{v}) ?_
  exact ⟨0, .zero⟩

@[other_dprim] lemma PUnit.unit.dcomp.{u, v} {ctx : Sort u} :
    DComp (fun _ : ctx => PUnit.unit.{v}) := .unsafeIntro
lemma New.PUnit.unit.dcomp.{u, v} : new_type% @PUnit.unit.dcomp.{u, v} := @New.PUnit.unit.computable

@[other_dprim] lemma Unit.unit.dcomp {ctx : Sort u} : DComp (fun _ : ctx => ()) := PUnit.unit.dcomp
lemma New.Unit.unit.dcomp.{u} : new_type% @Unit.unit.dcomp.{u} := @New.PUnit.unit.computable

example : DComputable (new% fun (x : Nat → Nat) y => x y) := by
  dcomp_tac

example : DComputable (new% fun (x : Nat → Nat) y => x (x y)) := by
  dcomp_tac

example : DComputable (new% fun (x : Nat → (_ : Nat) ×' Nat) y => x (x y).2) := by
  dcomp_tac

@[dprim]
theorem _root_.New.Nat.zero.computable {ctx : Sort u} {ctx_extra : new_type% ctx} :
    DComputable (new% fun _ : ctx => Nat.zero) := .const' (x_extra := new% Nat.zero) ⟨0, rfl⟩

@[other_dprim] lemma Nat.zero.dcomp {ctx : Sort u} : DComp (fun _ : ctx => Nat.zero) := .unsafeIntro
lemma New.Nat.zero.dcomp : new_type% @Nat.zero.dcomp.{u} := @New.Nat.zero.computable

@[dprim]
theorem _root_.New.Nat.succ.computable {ctx : Sort u} {ctx_extra : new_type% ctx}
    {f : ctx → ℕ} {f_extra : new_type% f}
    (f_comp : DComputable (new% f)) :
    DComputable (new% fun c => Nat.succ (f c)) := by
  refine .comp ?_ (f_extra := new% Nat.succ) f_comp
  refine ⟨Nat.succ, .succ, ?_⟩
  intro a _ _ rfl
  exact ⟨a + 1, by simp, by rfl⟩

set_option linter.unusedVariables.funArgs false in
@[other_dprim] lemma Nat.succ.dcomp {ctx : Sort u} {f : ctx → ℕ} (f_comp : DComp f) :
    DComp (fun c => Nat.succ (f c)) := .unsafeIntro
lemma New.Nat.succ.dcomp : new_type% @Nat.succ.dcomp.{u} :=
  fun _ _ _ _ _ hf => New.Nat.succ.computable hf

@[dprim]
theorem _root_.New.Nat.rec.primrec {ctx : Sort u} {ctx_extra : new_type% ctx}
    {motive : ctx → ℕ → Sort v} {motive_extra : new_type% motive}
    {zero : (c : ctx) → motive c .zero}
    {zero_extra : new_type% zero}
    (zero_comp : DPrimrec (new% zero))
    {succ : (c : ctx) → (n : ℕ) → motive c n → motive c (.succ n)}
    {succ_extra : new_type% succ}
    (succ_comp : DPrimrec (new%
      fun x : (c : ctx) ×' (n : ℕ) ×' motive c n => succ x.1 x.2.1 x.2.2))
    {t : ctx → ℕ} {t_extra : new_type% t}
    (t_comp : DPrimrec (new% t)) :
    DPrimrec (new% fun c =>
      @Nat.rec (motive c) (zero c) (succ c) (t c)) := by
  obtain ⟨fz, hfz, hfz'⟩ := zero_comp
  obtain ⟨fs, hfs, hfs'⟩ := succ_comp
  obtain ⟨ft, hft, hft'⟩ := t_comp
  refine ⟨_, .comp (.prec hfz hfs) (.pair .id hft), ?_⟩
  intro c c_extra nc hnc
  simp only [Nat.unpaired, id_eq, Nat.unpair_pair]
  specialize hfz' hnc
  specialize hft' hnc
  rw [show t c = ft nc from hft']
  induction ft nc with
  | zero => exact hfz'
  | succ k ih =>
    specialize @hfs' ⟨c, k, Nat.rec (zero c) (succ c) k⟩
    have : new_type% k := ()
    specialize @hfs' ⟨c_extra, (), new% Nat.rec (zero c) (succ c) k⟩
    exact @hfs' (Nat.pair nc (Nat.pair k _))
      ⟨by simpa using hnc, by simp; rfl, by simpa using ih⟩

set_option linter.unusedVariables.funArgs false in
@[other_dprim] lemma Nat.rec.dprim
    {ctx : Sort u} {motive : ctx → ℕ → Sort v}
    {zero : (c : ctx) → motive c .zero} (zero_comp : DPrim zero)
    {succ : (c : ctx) → (n : ℕ) → motive c n → motive c (.succ n)}
    (succ_comp : DPrim fun x : (c : ctx) ×' (n : ℕ) ×' motive c n => succ x.1 x.2.1 x.2.2)
    {t : ctx → ℕ} (t_comp : DPrim t) :
    DPrim fun c => @Nat.rec (motive c) (zero c) (succ c) (t c) := .unsafeIntro
lemma New.Nat.rec.dprim.{u, v} : new_type% @Nat.rec.dprim.{u, v} :=
  fun _ _ _ _ _ _ _ hz _ _ _ hs _ _ _ ht => New.Nat.rec.primrec hz hs ht

set_option linter.unusedVariables.funArgs false in
@[other_dprim] lemma Nat.rec.dcomp
    {ctx : Sort u} {motive : ctx → ℕ → Sort v}
    {zero : (c : ctx) → motive c .zero} (zero_comp : DComp zero)
    {succ : (c : ctx) → (n : ℕ) → motive c n → motive c (.succ n)} (succ_comp : DComp succ)
    {t : ctx → ℕ} (t_comp : DComp t) :
    DComp fun c => @Nat.rec (motive c) (zero c) (succ c) (t c) := by
  have (c : ctx) : @Nat.rec (motive c) (zero c) (succ c) (t c) =
      @Nat.rec (fun n => Unit → motive c n) (fun _ => zero c)
        (fun n ih _ => succ c n (ih ())) (t c) () := by
    induction t c <;> simp_all
  rw [funext this]
  have recComp : DComp (fun x :
      (c : ctx) ×' (zero : Unit → motive c 0) ×'
        (succ : (n : ℕ) → (Unit → motive c n) →
          Unit → motive c (n.succ)) ×' ℕ =>
      @Nat.rec (fun n => Unit → motive x.1 n) x.2.1 x.2.2.1 x.2.2.2) := by
    refine .of_prim ?_
    other_dcomp_tac
  have mk : DComp (fun c : ctx =>
      (⟨c, fun _ => zero c, fun n ih _ => succ c n (ih ()), t c⟩ :
        (c : ctx) ×' (zero : Unit → motive c 0) ×'
          (succ : (n : ℕ) → (Unit → motive c n) →
            Unit → motive c (n.succ)) ×' ℕ)) := by
    other_dcomp_tac
  exact .comp (.app recComp Unit.unit.dcomp) mk

convert_to_new Nat.rec.dcomp

open Lean Meta Qq
def insertContextType (e : Expr) (ctx : Expr) (max : Nat) (insts : Array Expr := #[]) : Expr :=
  match max, e with
  | max + 1, .forallE nm t b bi =>
    let t := t.instantiate insts
    let newInst := .app (.bvar (insts.size + 1)) (.bvar 0)
    .lam nm (.forallE `c ctx t .default) (insertContextType b ctx max (insts.push newInst)) bi
  | max + 1, .mdata _ e => insertContextType e ctx max insts
  | _, t =>
    let t := t.instantiate insts
    .forallE `c ctx t .default

open DPrimrec.Tactic in
def autoDComp (name : Name) (arity : Option Nat := none) : MetaM Unit := do
  let info ← getConstInfoDefn name
  let levels := info.levelParams.map Level.param
  let ctxUniv := Elab.Term.mkFreshLevelName info.levelParams
  let ctxUniv' := Elab.Term.mkFreshLevelName (ctxUniv :: info.levelParams)
  have clvl : Level := .param ctxUniv
  withLocalDeclQ `ctx .implicit q(Sort clvl) fun (ctx : Q(Sort clvl)) => do
  let e ← if arity.isSome then
      forallBoundedTelescope info.type arity mkForallFVars
    else pure info.type
  let e := insertContextType e ctx (arity.getD e.getForallArity)
  lambdaTelescope e fun params body => do
    let context : Other.Context := {
      contextUniv := ctxUniv'
      localPrimThms := {}
      localCompThms := {}
      zeta := false
    }
    let rec populateContext (context : Other.Context) (i : Nat)
        (vars : Array Expr) (infos : Array Other.ParamComputability) :
        MetaM Unit := do
      if h : i < params.size then
        let param := params[i]
        let paramType ← inferType param
        let vars := vars.push param
        if ← isProp paramType then
          return ← populateContext context (i + 1) vars (infos.push .always)
        let .forallE _ _ b _ := id paramType | unreachable!
        let (context, needComp) ← withLocalDeclD `c ctx fun var => do
          let some ⟨v, irrel⟩ ← Other.isTriviallyIrrelevant (b.instantiate1 var) |
            return (context, true)
          have blam : Q($ctx → Sort v) := .lam `c ctx b .default
          let _irrel : Q((x : $ctx) → Irrel ($blam x)) ← mkLambdaFVars #[var] irrel
          have f : Q((a : $ctx) → $blam a) := param
          have e : Q(DPrim $f) := q(.irrel)
          return (Other.withBasicLocalThm.newContext true q($e) context, false)
        unless needComp do
          return ← populateContext context (i + 1) vars (infos.push .always)
        let nm ← param.fvarId!.getUserName
        let blvl ← withLocalDeclD `c ctx fun var => getLevel (b.instantiate1 var)
        have blam : Q($ctx → Sort blvl) := .lam `c ctx b .default
        have f : Q((a : $ctx) → $blam a) := param
        withLocalDeclDQ (nm.appendAfter "_comp") q(DComp $f) fun (e : Q(DComp $f)) => do
          let context := Other.withBasicLocalThm.newContext false q($e) context
          populateContext context (i + 1) (vars.push e) (infos.push .computable)
      else
        let args := params.map (.app · (.bvar 0))
        let rlvl ← withLocalDeclD `c ctx fun var => getLevel (body.bindingBody!.instantiate1 var)
        have body : Q($ctx → Sort rlvl) := .lam `ctx ctx body.bindingBody! .default
        have value : Q((c : $ctx) → $body c) := .lam `ctx ctx (info.value.beta args) .default
        have const : Q((c : $ctx) → $body c) :=
          .lam `ctx ctx (mkAppN (.const info.name levels) args) .default
        have : $const =Q $value := ⟨⟩
        let result ← (Other.solveDPrimGoal false q($value)).run context
        have result : Q(DComp $const) := q($result)
        check result
        addDecl <| .thmDecl {
          name := name ++ `dcomp
          levelParams := ctxUniv :: info.levelParams
          type := ← mkForallFVars vars result.ty
          value := ← mkLambdaFVars vars result
        }
        let entry := {
          prim := false
          declName := name
          thmName := name ++ `dcomp
          paramInfos := infos
        }
        modifyEnv (Other.otherDPrimExt.addEntry · entry)
    populateContext context 0 #[ctx] #[]

set_option linter.unusedVariables false in
lemma PProd.dprim_toPSigma {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {self : (c : ctx) → PProd (α c) (β c)} (self_comp : DPrim self) :
    DPrim (fun c => PSigma.mk (β := fun _ => β c) (self c).1 (self c).2) := .unsafeIntro

set_option linter.unusedVariables false in
lemma PProd.dprim_ofPSigma {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {self : (c : ctx) → PSigma (fun _ : α c => β c)} (self_comp : DPrim self) :
    DPrim (fun c => PProd.mk (self c).1 (self c).2) := .unsafeIntro

set_option linter.unusedVariables false in
lemma Nat.pair.dprim {ctx : Sort u} {a : ctx → ℕ} (ha : DPrim a) {b : ctx → ℕ} (hb : DPrim b) :
    DPrim fun c => Nat.pair (a c) (b c) := .unsafeIntro

structure TheoremBuilder.{c} {prectx : Sort u} (prectx_extra : new_type% prectx) where
  In (pre : prectx) (pre_extra : new_type% pre) (n : ℕ) : Prop
  OutPrim (ctx : Sort c) (ctx_extra : new_type% ctx)
      (pre : ctx → prectx) (pre_extra : new_type% pre) : Prop
  OutComp (ctx : Sort c) (ctx_extra : new_type% ctx)
      (pre : ctx → prectx) (pre_extra : new_type% pre) : Prop
  in_implies_outPrim (ctx : Sort c) (ctx_extra : new_type% ctx)
      (pre : ctx → prectx) (pre_extra : new_type% pre)
      (g : ℕ → ℕ) (hg : Nat.Primrec g)
      (h : ∀ ⦃c c_extra c_n⦄, ctx_extra.2 c_extra c_n → In (pre c) (pre_extra c_extra) (g c_n)) :
      OutPrim ctx ctx_extra pre pre_extra
  in_implies_outComp (ctx : Sort c) (ctx_extra : new_type% ctx)
      (pre : ctx → prectx) (pre_extra : new_type% pre)
      (g : ℕ →. ℕ) (hg : Nat.Partrec g)
      (h : ∀ ⦃c c_extra c_n⦄, ctx_extra.2 c_extra c_n →
        ∃ m ∈ g c_n, In (pre c) (pre_extra c_extra) m) :
      OutComp ctx ctx_extra pre pre_extra

theorem TheoremBuilder.primResult (t : @TheoremBuilder Unit (new% Unit)) (h : t.In _ (new% ()) 0) :
    ∀ {ctx : Sort c} {ctx_extra : new_type% ctx},
      t.OutPrim ctx ctx_extra _ (new% fun _ : ctx => ()) := by
  intro ctx ctx_extra
  exact t.in_implies_outPrim ctx ctx_extra _ _ _ .zero fun _ _ _ _ => h

theorem TheoremBuilder.compResult (t : @TheoremBuilder Unit (new% Unit)) (h : t.In _ (new% ()) 0) :
    ∀ {ctx : Sort c} {ctx_extra : new_type% ctx},
      t.OutComp ctx ctx_extra _ (new% fun _ : ctx => ()) := by
  intro ctx ctx_extra
  exact t.in_implies_outComp ctx ctx_extra _ _ _ .zero fun _ _ _ _ => ⟨0, ⟨⟨⟩, rfl⟩, h⟩

def TheoremBuilder.base.{c} {prectx : Sort u} {prectx_extra : new_type% prectx}
    {α : prectx → Sort v} (α_extra : new_type% α)
    {f : (c : prectx) → α c} (f_extra : new_type% f) :
    TheoremBuilder.{c} (new% prectx) where
  In _ pre n := (α_extra pre).2 (f_extra pre) n
  OutPrim _ _ pre _ := DPrimrec (new% fun a => f (pre a))
  OutComp _ _ pre _ := DComputable (new% fun a => f (pre a))
  in_implies_outPrim _ _ _ _ pre_n prim hin := ⟨pre_n, prim, @hin⟩
  in_implies_outComp _ _ _ _ pre_n comp hin := ⟨pre_n, comp, @hin⟩

def TheoremBuilder.baseTransformed.{c} {prectx : Sort u} {prectx_extra : new_type% prectx}
    {α : prectx → Sort v} (α_extra : new_type% α)
    {f : (c : prectx) → α c} (f_extra : new_type% f)
    (g : ℕ → ℕ) (hg : Nat.Primrec g) :
    TheoremBuilder.{c} (new% prectx) where
  In _ pre n := (α_extra pre).2 (f_extra pre) (g n)
  OutPrim _ _ pre _ := DPrimrec (new% fun a => f (pre a))
  OutComp _ _ pre _ := DComputable (new% fun a => f (pre a))
  in_implies_outPrim _ _ _ _ pre_n prim hin := ⟨_, hg.comp prim, hin⟩
  in_implies_outComp _ _ _ _ pre_n comp hin := ⟨_, .comp (.of_primrec hg) comp, by simpa using hin⟩

theorem primrec_pair_right (c : ℕ) : Nat.Primrec (fun n => Nat.pair n c) := .pair .id (.const c)

def TheoremBuilder.prepend.{c} {prectx : Sort u} {prectx_extra : new_type% prectx}
    {α : prectx → Sort v} {α_extra : new_type% α}
    (h : TheoremBuilder.{c} (new% (a : prectx) ×' α a)) :
    TheoremBuilder.{c} (new% prectx) where
  In pre pre_extra n :=
    ∀ a : α pre, ∀ a_extra : new_type% a, ∀ a_n : ℕ, (α_extra pre_extra).2 a_extra a_n →
      h.In _ (new% PSigma.mk pre a) (Nat.pair n a_n)
  OutPrim ctx ctx_extra pre _pre_extra :=
    ∀ a : (c : ctx) → α (pre c), ∀ a_extra : new_type% a, DPrimrec a_extra →
      h.OutPrim ctx ctx_extra _ (new% fun c : ctx => PSigma.mk (pre c) (a c))
  OutComp ctx ctx_extra pre _pre_extra :=
    ∀ a : (c : ctx) → α (pre c), ∀ a_extra : new_type% a, DComputable a_extra →
      h.OutComp ctx ctx_extra _ (new% fun c : ctx => PSigma.mk (pre c) (a c))
  in_implies_outPrim ctx ctx_extra pre pre_extra pre_n prim hin := by
    intro a a_extra ⟨g, hg, hg'⟩
    refine h.in_implies_outPrim ctx ctx_extra _ _ _ (prim.pair hg) ?_
    intro c c_extra cn hcn
    exact hin hcn (a c) (a_extra c_extra) (g cn) (hg' hcn)
  in_implies_outComp ctx ctx_extra pre pre_extra pre_n comp hin := by
    intro a a_extra ⟨g, hg, hg'⟩
    refine h.in_implies_outComp ctx ctx_extra _ _ _ (comp.pair hg) ?_
    intro c c_extra cn hcn
    obtain ⟨m, hm, hm'⟩ := hg' hcn
    obtain ⟨k, hk, hk'⟩ := hin hcn
    simpa [Seq.seq, Part.eq_some_iff.mpr hm, Part.eq_some_iff.mpr hk]
      using hk' (a c) (a_extra c_extra) m hm'

def TheoremBuilder.prependIrrelevant.{c} {prectx : Sort u} {prectx_extra : new_type% prectx}
    {α : prectx → Sort v} {α_extra : new_type% α}
    (h : TheoremBuilder.{c} (new% (a : prectx) ×' α a)) :
    TheoremBuilder.{c} (new% prectx) where
  In pre pre_extra n :=
    ∀ a : α pre, ∀ a_extra : new_type% a,
      h.In _ (new% PSigma.mk pre a) n
  OutPrim ctx ctx_extra pre _pre_extra :=
    ∀ a : (c : ctx) → α (pre c), ∀ a_extra : new_type% a,
      h.OutPrim ctx ctx_extra _ (new% fun c : ctx => PSigma.mk (pre c) (a c))
  OutComp ctx ctx_extra pre _pre_extra :=
    ∀ a : (c : ctx) → α (pre c), ∀ a_extra : new_type% a,
      h.OutComp ctx ctx_extra _ (new% fun c : ctx => PSigma.mk (pre c) (a c))
  in_implies_outPrim ctx ctx_extra pre pre_extra pre_n prim hin := by
    intro a a_extra
    refine h.in_implies_outPrim ctx ctx_extra _ _ _ prim ?_
    intro c c_extra cn hcn
    exact hin hcn (a c) (a_extra c_extra)
  in_implies_outComp ctx ctx_extra pre pre_extra pre_n comp hin := by
    intro a a_extra
    apply h.in_implies_outComp ctx ctx_extra _ _ _ comp ?_
    intro c c_extra cn hcn
    obtain ⟨k, hk, hk'⟩ := hin hcn
    exact ⟨k, hk, hk' (a c) (a_extra c_extra)⟩

def TheoremBuilder.prependFirst.{c} {prectx : Sort u} {prectx_extra : new_type% prectx}
    {α : prectx → Sort v} {α_extra : new_type% α}
    (h : TheoremBuilder.{c} (new% (a : prectx) ×' α a)) :
    TheoremBuilder.{c} (new% prectx) where
  In pre pre_extra n :=
    ∀ a : α pre, ∀ a_extra : new_type% a, ∀ a_n : ℕ, (α_extra pre_extra).2 a_extra a_n →
      h.In _ (new% PSigma.mk pre a) a_n
  OutPrim ctx ctx_extra pre _pre_extra :=
    ∀ a : (c : ctx) → α (pre c), ∀ a_extra : new_type% a, DPrimrec a_extra →
      h.OutPrim ctx ctx_extra _ (new% fun c : ctx => PSigma.mk (pre c) (a c))
  OutComp ctx ctx_extra pre _pre_extra :=
    ∀ a : (c : ctx) → α (pre c), ∀ a_extra : new_type% a, DComputable a_extra →
      h.OutComp ctx ctx_extra _ (new% fun c : ctx => PSigma.mk (pre c) (a c))
  in_implies_outPrim ctx ctx_extra pre pre pre_n prim hin := by
    intro a a_extra ⟨g, hg, hg'⟩
    refine h.in_implies_outPrim ctx ctx_extra _ _ _ hg ?_
    intro c c_extra cn hcn
    exact hin hcn (a c) (a_extra c_extra) (g cn) (hg' hcn)
  in_implies_outComp ctx ctx_extra pre pre_extra pre_n comp hin := by
    intro a a_extra ⟨g, hg, hg'⟩
    refine h.in_implies_outComp ctx ctx_extra _ _ _ hg ?_
    intro c c_extra cn hcn
    obtain ⟨m, hm, hm'⟩ := hg' hcn
    obtain ⟨k, hk, hk'⟩ := hin hcn
    simpa [Seq.seq, Part.eq_some_iff.mpr hm, Part.eq_some_iff.mpr hk]
      using hk' (a c) (a_extra c_extra) m hm'

partial def makeTheoremBuilder {α : Q(Sort u)} {α_extra : Q(new_type% $α)}
    {β : Q($α → Sort v)} {β_extra : Q(new_type% $β)}
    {f : Q((a : $α) → $β a)} (f_extra : Q(new_type% $f))
    (g : Q(ℕ → ℕ)) (hg : Q(Nat.Primrec $g)) (hadRelevant : Bool)
    (remainingParams : Nat) (clvl : Level) : MetaM Q(TheoremBuilder.{clvl} $α_extra) := do
  let .lam _ _ b _ := id β | unreachable!
  let .forallE nnnn dom body bbbiii := id b |
    if g == q(id) then
      return q(.base $β_extra $f_extra)
    else
      return q(.baseTransformed $β_extra $f_extra $g $hg)
  let .lam nm _ (.lam nm' ttt b bi) bi' := id β_extra | unreachable!
  let mkApp4 (.const ``New.Forall [w₁, w₂]) _ dom_extra _ body_extra := id b | unreachable!
  --
  let newLam (x : Expr) : Expr := .lam nm α (.lam nm' ttt x bi) bi'
  have dom_lam : Q($α → Sort w₁) := .lam nm α dom bi
  have _dom_lam : Q(new_type% $dom_lam) := newLam dom_extra
  have body_lam : Q((a : $α) → $dom_lam a → Sort w₂) :=
    .lam nm α (.lam nnnn dom body bbbiii) bi
  have _body_lam : Q(new_type% $body_lam) := newLam body_extra
  have : v =QL imax w₁ w₂ := ⟨⟩
  have : $β =Q fun c => ∀ x : $dom_lam c, $body_lam c x := ⟨⟩
  have : $β_extra =Q new% fun c => ∀ x : $dom_lam c, $body_lam c x := ⟨⟩
  let isRelevant := remainingParams == 0 && !w₁.isAlwaysZero
  let res : Q(TheoremBuilder.{clvl} (new% PSigma $dom_lam)) ←
    makeTheoremBuilder q(new% fun x : PSigma $dom_lam => $f x.1 x.2)
      q($g) q($hg) (hadRelevant || isRelevant) (remainingParams - 1) clvl
  if isRelevant then
    if hadRelevant then
      return q(.prepend $res)
    else
      return q(.prependFirst $res)
  else
    return q(.prependIrrelevant $res)

def makeCtorEncodingProof (ctor : ConstructorVal) (isStruct : Bool) (levels : List Level) :
    MetaM Expr := do
  let shortName := ctor.name.replacePrefix ctor.induct .anonymous
  unless isStruct do
    return .const (mkNewInductEncodingName ctor.induct ++ shortName) levels
  forallTelescope ctor.type fun vars _body => do
  withNewVars vars convertTypeSimpleNew fun newVars Map => do
    let params := vars.take ctor.numParams
    let newParams := newVars.take ctor.numParams
    let allParams := params.interleave newParams
    let rec go (i : Nat) (allVars : Array Expr) (encs : Array Expr) : MetaM Expr := do
      if h : i < vars.size then
        let var := vars[i]
        let newVar := newVars[i]!
        let allVars := allVars.push var |>.push newVar
        if ← isProof var then
          return ← go (i + 1) allVars encs
        let decl ← newVar.fvarId!.getDecl
        let name := decl.userName
        let mkExtraApp ty _ := decl.type | unreachable!
        withLocalDeclD (name.appendAfter "_n") q(ℕ) fun n => do
        let encType := mkApp3 (.proj ``SortExtra 1 ty) var newVar n
        withLocalDeclD (name.appendAfter "_enc") encType fun enc => do
          go (i + 1) (allVars.push n |>.push enc) (encs.push n |>.push enc)
      else
        let ctorApp := mkAppN (.const ctor.name levels) vars
        let newCtorName := mkNewInductName ctor.induct ++ shortName
        let newCtorApp := mkAppN (.const newCtorName levels) allParams
        let newCtorApp := mkAppN (newCtorApp.app ctorApp) (newVars.drop ctor.numParams)
        let encodingCtorName := mkNewInductEncodingName ctor.induct ++ shortName
        let proof := mkAppN (.const encodingCtorName levels) allParams
        let proof := mkApp2 proof ctorApp newCtorApp
        mkLambdaFVars allVars (mkAppN proof encs)
    go ctor.numParams allParams #[]

open DPrimrec.Tactic in
def proveConstructorComputable (ctorName : Name) : MetaM Unit := do
  recConvertToNew ctorName
  let ctor ← getConstInfoCtor ctorName
  let ind ← getConstInfoInduct ctor.induct
  let ctxUniv := Elab.Term.mkFreshLevelName ctor.levelParams
  have ctxLvl := .param ctxUniv
  let ctorLvl ← getLevel ctor.type
  if ctorLvl.isAlwaysZero then
    return
  let isStruct := ind.ctors matches [_] && ind.numIndices == 0 && !ind.isRec
  have ctorType : Q(Sort ctorLvl) := ctor.type
  let _ctorTypeNew : Q(new_type% $ctorType) ← conversionStepNew ctorType
  have levels := ctor.levelParams.map Level.param
  have val : Q($ctorType) := .const ctor.name levels
  have _valNew : Q(new_type% $val) := .const (mkNewName ctor.name) levels
  have off : Q(ℕ) := mkRawNatLit (ctor.cidx + 1)
  have ⟨f, hf⟩ : (f : Q(ℕ → ℕ)) × Q(Nat.Primrec $f) :=
    if isStruct then ⟨q(id), q(.id)⟩ else ⟨_, q(primrec_pair_right $off)⟩
  -- Build the theorem builder
  let builder ← makeTheoremBuilder q(new% fun _ : Unit => $val) q($f) q($hf)
    (hadRelevant := false) ctor.numParams ctxLvl
  let input : Q(($builder).In () (new% ()) 0) ← makeCtorEncodingProof ctor isStruct levels
  withLocalDeclQ `ctx .implicit q(Sort ctxLvl) fun ctx =>
  withLocalDeclQ `ctx_extra .implicit q(new_type% $ctx) fun ctx' =>
    let e := insertContextType ctorType ctx ctorType.getForallArity
    lambdaTelescope e fun vars body => do
      let rec go (prim : Bool) (i : Nat) (proof : Expr)
          (allVars : Array Expr) (allNewVars : Array Expr)
          (nparams : Nat) (comps : Array Other.ParamComputability)
          (baseMap : FVarIdMap Expr) :
          MonadCacheT ExprStructEq Expr MetaM Unit := do
        if h : i < vars.size then
          let var := vars[i]
          let decl ← var.fvarId!.getDecl
          let varNm := decl.userName
          let type := decl.type
          withImplicitBinderInfos #[var] do
          let newType ← convertTypeSimpleNew var type baseMap
          withLocalDeclD (varNm.appendAfter "_extra") newType fun extraVar => do
          let allVars := allVars.push var
          let allNewVars := allNewVars.push var |>.push extraVar
          let baseMap := baseMap.insert var.fvarId! extraVar
          let proof := mkApp2 proof var extraVar
          if nparams ≠ 0 ∨ (← isProof var) then
            return ← go prim (i + 1) proof allVars allNewVars
              (nparams - 1) (comps.push .always) baseMap
          let .forallE nm t b bi := type | unreachable!
          let lvl ← withLocalDeclD `c ctx fun var => getLevel (b.instantiate1 var)
          let pred := if prim then ``DPrim else ``DComp
          let dcomp := mkApp3 (.const pred [ctxLvl, lvl]) ctx (.lam nm t b bi) var
          withLocalDeclD (varNm.appendAfter "_comp") dcomp fun hcompDummy => do
          let newDComp ← convertTypeSimpleNew hcompDummy dcomp baseMap
          withLocalDeclD (varNm.appendAfter "_comp_extra") newDComp fun hcomp => do
          let allVars := allVars.push hcompDummy
          let allNewVars := allNewVars.push hcompDummy |>.push hcomp
          let proof := proof.app hcomp
          let theComp := if prim then .prim else .computable
          let baseMap := baseMap.insert hcompDummy.fvarId! hcomp
          go prim (i + 1) proof allVars allNewVars 0 (comps.push theComp) baseMap
        else
          let .forallE nm t b bi := body | unreachable!
          let lvl ← withLocalDeclD `c ctx fun var => getLevel (b.instantiate1 var)
          let ctorApp := mkAppN (.const ctorName levels) (vars.map (·.app (.bvar 0)))
          let ctorApp := .lam nm t ctorApp bi
          let ctorAppType := .lam nm t b bi
          let pred := if prim then ``DPrim else ``DComp
          let dummyThm := if prim then ``DPrim.unsafeIntro else ``DComp.unsafeIntro
          let proofDummy := mkApp3 (.const dummyThm [ctxLvl, lvl]) ctx ctorAppType ctorApp
          let dummyType := mkApp3 (.const pred [ctxLvl, lvl]) ctx ctorAppType ctorApp
          let dummyType ← mkForallFVars allVars dummyType
          let dummyValue ← mkLambdaFVars allVars proofDummy
          let dummyName := if prim then ctorName ++ `dprim else ctorName ++ `dcomp
          addDecl <| .thmDecl {
            name := dummyName
            levelParams := ctxUniv :: ctor.levelParams
            type := dummyType
            value := dummyValue
          }
          let dummyThm := .const dummyName (ctxLvl :: levels)
          let realType ← convertTypeSimpleNew dummyThm dummyType baseMap
          let realValue ← mkLambdaFVars allNewVars proof
          check realValue
          addDecl <| .thmDecl {
            name := mkNewName dummyName
            levelParams := ctxUniv :: ctor.levelParams
            type := realType
            value := realValue
          }
      termination_by vars.size - i
      let primResult := q(@($builder).primResult $input $ctx $ctx')
      let compResult := q(@($builder).compResult $input $ctx $ctx')
      let baseMap : FVarIdMap Expr := .insert {} ctx.fvarId! ctx'
      MonadCacheT.run <| go true 0 primResult #[ctx] #[ctx, ctx'] ctor.numParams #[] baseMap
      MonadCacheT.run <| go false 0 compResult #[ctx] #[ctx, ctx'] ctor.numParams #[] baseMap

#print Nat.Partrec.Code
#eval! proveConstructorComputable ``Nat.Partrec.Code.zero
#eval! proveConstructorComputable ``Nat.Partrec.Code.succ
#eval! proveConstructorComputable ``Nat.Partrec.Code.left
#eval! proveConstructorComputable ``Nat.Partrec.Code.right
#eval! proveConstructorComputable ``Nat.Partrec.Code.pair
#eval! proveConstructorComputable ``Nat.Partrec.Code.comp
#eval! proveConstructorComputable ``Nat.Partrec.Code.prec
#eval! proveConstructorComputable ``Nat.Partrec.Code.rfind'

#eval! proveConstructorComputable ``Std.DHashMap.Raw.mk

#print New.Std.DHashMap.Internal.AssocList
#print Std.DHashMap.Raw.mk
