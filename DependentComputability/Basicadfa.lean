import DependentComputability.Tactic.DPrimStep
import DependentComputability.Tactic.ExprOverview
import Mathlib.Tactic.DepRewrite

@[dprim]
protected theorem DPrimrec.subtypeVal {ctx : Sort u} {α : ctx → Sort v} {p : (c : ctx) → α c → Prop}
    {f : (c : ctx) → Subtype (p c)} [EncodingRelation ctx] [∀ c, EncodingRelation (α c)]
    (hf : DPrimrec f) : DPrimrec (fun c => (f c).val) := hf

@[dprim]
protected theorem DComputable.subtypeVal
    {ctx : Sort u} {α : ctx → Sort v} {p : (c : ctx) → α c → Prop}
    {f : (c : ctx) → Subtype (p c)} [EncodingRelation ctx] [∀ c, EncodingRelation (α c)]
    (hf : DComputable f) : DComputable (fun c => (f c).val) := hf

@[dprim]
protected theorem DPrimrec.subtypeMk {ctx : Sort u} {α : ctx → Sort v} {p : (c : ctx) → α c → Prop}
    {f : (c : ctx) → α c} {h : ∀ c, p c (f c)} [EncodingRelation ctx] [∀ c, EncodingRelation (α c)]
    (hf : DPrimrec f) : DPrimrec (fun c => Subtype.mk (f c) (h c)) := hf

@[dprim]
protected theorem DComputable.subtypeMk
    {ctx : Sort u} {α : ctx → Sort v} {p : (c : ctx) → α c → Prop}
    {f : (c : ctx) → α c} {h : ∀ c, p c (f c)} [EncodingRelation ctx] [∀ c, EncodingRelation (α c)]
    (hf : DComputable f) : DComputable (fun c => Subtype.mk (f c) (h c)) := hf

@[dprim]
protected theorem DPrimrec.quotMk {ctx : Sort u} {α : ctx → Sort v}
    {r : (c : ctx) → α c → α c → Prop} {f : (c : ctx) → α c}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)]
    (hf : DPrimrec f) :
    DPrimrec (fun c => Quot.mk (r c) (f c)) := by
  obtain ⟨g, hg, hg'⟩ := hf
  use g, hg
  intro a b h
  use f b, rfl, hg' h

@[dprim]
protected theorem DPrimrec.psigmaMk
    {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → α c} {g : (c : ctx) → β c (f c)}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c a, EncodingRelation (β c a)]
    (hf : DPrimrec f) (hg : DPrimrec g) :
    DPrimrec (fun a => PSigma.mk (f a) (g a)) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  refine ⟨_, hgf.pair hgg, ?_⟩
  intro a b hab
  constructor
  · simpa using hgf' hab
  · simpa using hgg' hab

@[dprim]
protected theorem DComputable.psigmaMk
    {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → α c} {g : (c : ctx) → β c (f c)}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c a, EncodingRelation (β c a)]
    (hf : DComputable f) (hg : DComputable g) :
    DComputable (fun a => PSigma.mk (f a) (g a)) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  refine ⟨_, hgf.pair hgg, ?_⟩
  intro a b hab
  obtain ⟨x, hx, hx'⟩ := hgf' hab
  obtain ⟨y, hy, hy'⟩ := hgg' hab
  use Nat.pair x y
  simp [seq_eq_bind_map, EncodingRelation.Encodes, *]

@[dprim]
protected theorem DPrimrec.psigmaFst
    {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → (a : α c) ×' β c a}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c a, EncodingRelation (β c a)]
    (hf : DPrimrec f) :
    DPrimrec (fun c => (f c).1) := by
  obtain ⟨g, hg, hg'⟩ := hf
  refine ⟨_, .comp .left hg, ?_⟩
  intro a b h
  exact (hg' h).1

@[dprim]
protected theorem DComputable.psigmaFst
    {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → (a : α c) ×' β c a}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c a, EncodingRelation (β c a)]
    (hf : DComputable f) :
    DComputable (fun c => (f c).1) := by
  obtain ⟨g, hg, hg'⟩ := hf
  refine ⟨_, .comp .left hg, ?_⟩
  intro a b h
  obtain ⟨y, hy, hy'⟩ := hg' h
  simpa using ⟨y, hy, hy'.1⟩

@[dprim]
protected theorem DPrimrec.psigmaSnd
    {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → (a : α c) ×' β c a}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c a, EncodingRelation (β c a)]
    (hf : DPrimrec f) :
    DPrimrec (fun c => (f c).2) := by
  obtain ⟨g, hg, hg'⟩ := hf
  refine ⟨_, .comp .right hg, ?_⟩
  intro a b h
  exact (hg' h).2

@[dprim]
protected theorem DComputable.psigmaSnd
    {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → (a : α c) ×' β c a}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c a, EncodingRelation (β c a)]
    (hf : DComputable f) :
    DComputable (fun c => (f c).2) := by
  obtain ⟨g, hg, hg'⟩ := hf
  refine ⟨_, .comp .right hg, ?_⟩
  intro a b h
  obtain ⟨y, hy, hy'⟩ := hg' h
  simpa using ⟨y, hy, hy'.2⟩

@[dprim]
protected theorem DPrimrec.pprodMk
    {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {f : (c : ctx) → α c} {g : (c : ctx) → β c}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c, EncodingRelation (β c)]
    (hf : DPrimrec f) (hg : DPrimrec g) :
    DPrimrec (fun a => PProd.mk (f a) (g a)) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gg, hgg, hgg'⟩ := hg
  refine ⟨_, hgf.pair hgg, ?_⟩
  intro a b hab
  constructor
  · simpa using hgf' hab
  · simpa using hgg' hab

@[dprim]
protected theorem DComputable.pprodMk
    {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {f : (c : ctx) → α c} {g : (c : ctx) → β c}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c, EncodingRelation (β c)]
    (hf : DComputable f) (hg : DComputable g) :
    DComputable (fun a => PProd.mk (f a) (g a)) := by
  dprim_step
  · dprim_step
    · refine .of_prim ?_
      dprim_step
      refine .of_prim ?_
      dprim_step
      refine .of_prim ?_
      dprim_tac
    · assumption
  · assumption

@[dprim]
protected theorem DPrimrec.pprodFst
    {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w} {f : (c : ctx) → α c ×' β c}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c, EncodingRelation (β c)]
    (hf : DPrimrec f) : DPrimrec (fun c => (f c).1) := by
  obtain ⟨g, hg, hg'⟩ := hf
  refine ⟨_, .comp .left hg, ?_⟩
  intro a b h
  exact (hg' h).1

@[dprim]
protected theorem DComputable.pprodFst
    {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w} {f : (c : ctx) → α c ×' β c}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c, EncodingRelation (β c)]
    (hf : DComputable f) : DComputable (fun c => (f c).1) := by
  dprim_step
  · refine .of_prim ?_
    dprim_step
    refine .of_prim ?_
    dprim_tac
  · assumption

@[dprim]
protected theorem DPrimrec.pprodSnd
    {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w} {f : (c : ctx) → α c ×' β c}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c, EncodingRelation (β c)]
    (hf : DPrimrec f) : DPrimrec (fun c => (f c).2) := by
  obtain ⟨g, hg, hg'⟩ := hf
  refine ⟨_, .comp .right hg, ?_⟩
  intro a b h
  exact (hg' h).2

@[dprim]
protected theorem DComputable.pprodSnd
    {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w} {f : (c : ctx) → α c ×' β c}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c, EncodingRelation (β c)]
    (hf : DComputable f) : DComputable (fun c => (f c).2) := by
  dprim_step
  · refine .of_prim ?_
    dprim_step
    refine .of_prim ?_
    dprim_tac
  · assumption

@[dprim]
protected theorem DPrimrec.natSucc {ctx : Sort u} {f : ctx → ℕ}
    [EncodingRelation ctx] (hf : DPrimrec f) :
    DPrimrec (fun c => (f c).succ) := by
  obtain ⟨g, hg, hg'⟩ := hf
  refine ⟨_, .comp .succ hg, ?_⟩
  intro a b hab
  exact congrArg Nat.succ (hg' hab)

@[dprim]
protected theorem DComputable.natSucc {ctx : Sort u} {f : ctx → ℕ}
    [EncodingRelation ctx] (hf : DComputable f) :
    DComputable (fun c => (f c).succ) := by
  dprim_step
  · refine .of_prim ?_
    dprim_step
    refine .of_prim ?_
    dprim_tac
  · assumption

@[dprim]
theorem DPrimrec.natRec {ctx : Sort v} {motive : ctx → ℕ → Sort u}
    {zero : (c : ctx) → motive c Nat.zero}
    {succ : (c : ctx) → (n : ℕ) → motive c n → motive c n.succ}
    {t : ctx → ℕ}
    [EncodingRelation ctx] [∀ c n, EncodingRelation (motive c n)]
    (hzero : DPrimrec zero)
    (hsucc : DPrimrec fun x : (c : ctx) ×' (n : ℕ) ×' motive c n ↦ succ x.1 x.2.1 x.2.2)
    (ht : DPrimrec t) :
    DPrimrec (fun ctx => @Nat.rec (motive ctx) (zero ctx) (succ ctx) (t ctx)) := by
  obtain ⟨fz, hfz, hfz'⟩ := hzero
  obtain ⟨fs, hfs, hfs'⟩ := hsucc
  obtain ⟨ft, hft, hft'⟩ := ht
  refine ⟨_, (hfz.prec hfs).comp (.pair .id hft), ?_⟩
  intro a b hab
  have hfta : ft a = t b := hft' hab
  simp +instances only [Nat.unpaired, id_eq, hfta, Nat.unpair_pair]
  induction t b with
  | zero => simpa using hfz' hab
  | succ k ih =>
    dsimp only
    refine @hfs' _ ⟨_, _, _⟩ ⟨?_, ?_, ?_⟩
    · simpa using hab
    · simp
    · simpa using ih

dcomp_decl DComputable.functionComp for Function.comp with 5

@[dprim]
theorem DComputable.natRec {ctx : Sort v} {motive : ctx → ℕ → Sort u}
    {zero : (c : ctx) → motive c Nat.zero}
    {succ : (c : ctx) → (n : ℕ) → motive c n → motive c n.succ}
    {t : ctx → ℕ}
    [EncodingRelation ctx] [∀ c n, EncodingRelation (motive c n)]
    (hzero : DComputable zero) (hsucc : DComputable succ) (ht : DComputable t) :
    DComputable (fun ctx => @Nat.rec (motive ctx) (zero ctx) (succ ctx) (t ctx)) := by
  have (c : ctx) : @Nat.rec (motive c) (zero c) (succ c) (t c) =
      @Nat.rec (fun n => Unit → motive c n) (fun _ => zero c)
        (fun n ih _ => succ c n (ih ())) (t c) () := by
    induction t c <;> simp_all
  simp only [this]
  dprim_step
  · dprim_step
    · refine .of_prim ?_
      dprim_step
      refine .of_prim ?_
      dprim_tac
    · assumption
  · dprim_step

@[dprim]
theorem DPrimrec.natCasesOn {ctx : Sort v} {motive : ctx → ℕ → Sort u}
    {t : ctx → ℕ}
    {zero : (c : ctx) → motive c Nat.zero}
    {succ : (c : ctx) → (n : ℕ) → motive c n.succ}
    [EncodingRelation ctx] [∀ c n, EncodingRelation (motive c n)]
    (hzero : DPrimrec zero)
    (hsucc : DPrimrec fun x : (_ : ctx) ×' ℕ ↦ succ x.1 x.2)
    (ht : DPrimrec t) :
    DPrimrec (fun ctx => @Nat.casesOn (motive ctx) (t ctx) (zero ctx) (succ ctx)) := by
  dprim_tac [Nat.casesOn]

dcomp_decl DComputable.natCasesOn for Nat.casesOn

instance {motive : ℕ → Sort u} [∀ n, EncodingRelation (motive n)] (t : ℕ) :
    EncodingRelation (@Nat.below motive t) :=
  Nat.rec inferInstance (fun _ _ ↦ inferInstance) t

instance {motive : ℕ → Type} [∀ n, EncodingRelation (motive n)] :
    EncodingRelation (@Nat.below motive 0) := inferInstanceAs (EncodingRelation PUnit.{1})

@[dprim]
theorem DPrimrec.natBrecOn {ctx : Sort u} {motive : ctx → ℕ → Sort v}
    {t : ctx → ℕ} {F_1 : (c : ctx) → (t : ℕ) → @Nat.below (motive c) t → motive c t}
    [EncodingRelation ctx] [∀ c n, EncodingRelation (motive c n)]
    (ht : DPrimrec t)
    (hF_1 : DPrimrec fun x : (c : ctx) ×' (t : ℕ) ×' @Nat.below (motive c) t =>
      F_1 x.1 x.2.1 x.2.2) :
    DPrimrec (fun c => @Nat.brecOn (motive c) (t c) (F_1 c)) := by
  dprim_tac [Nat.brecOn, Nat.brecOn.go]

dcomp_decl DComputable.natBrecOn for Nat.brecOn unfolding Nat.brecOn.go
dcomp_decl DComputable.natAdd for Nat.add unfolding Nat.add.match_1
dcomp_decl DComputable.natPred for Nat.pred unfolding Nat.pow.match_1
--dcomp_decl DComputable.natMul for Nat.mul unfolding Nat.mul.match_1

@[dprim]
theorem DPrimrec.natAdd {ctx : Sort u} {a b : ctx → ℕ}
    [EncodingRelation ctx] (ha : DPrimrec a) (hb : DPrimrec b) :
    DPrimrec (fun c => (a c).add (b c)) := by
  have (a b : ℕ) : Nat.add a b = Nat.rec a (fun _ ih => ih.succ) b := by
    fun_induction Nat.add <;> simp_all
  simp only [this]
  dprim_tac

@[dprim]
theorem DPrimrec.natMul {ctx : Sort u} {a b : ctx → ℕ}
    [EncodingRelation ctx] (ha : DPrimrec a) (hb : DPrimrec b) :
    DPrimrec (fun c => (a c).mul (b c)) := by
  have (a b : ℕ) : Nat.mul a b = Nat.rec 0 (fun _ ih => ih.add a) b := by
    fun_induction Nat.mul <;> simp_all
  simp only [this]
  dprim_tac

@[dprim]
theorem DPrimrec.natPow {ctx : Sort u} {a b : ctx → ℕ}
    [EncodingRelation ctx] (ha : DPrimrec a) (hb : DPrimrec b) :
    DPrimrec (fun c => (a c).pow (b c)) := by
  have (a b : ℕ) : Nat.pow a b = Nat.rec 1 (fun _ ih => ih.mul a) b := by
    fun_induction Nat.pow <;> simp_all
  simp only [this]
  dprim_tac

@[dprim]
theorem DPrimrec.natPred {ctx : Sort u} {a : ctx → ℕ}
    [EncodingRelation ctx] (ha : DPrimrec a) :
    DPrimrec (fun c => (a c).pred) := by
  dprim_tac [Nat.pred, Nat.pow.match_1]

@[dprim]
theorem DPrimrec.natSub {ctx : Sort u} {a b : ctx → ℕ}
    [EncodingRelation ctx] (ha : DPrimrec a) (hb : DPrimrec b) :
    DPrimrec (fun c => (a c).sub (b c)) := by
  have (a b : ℕ) : Nat.sub a b = Nat.rec a (fun _ ih => ih.pred) b := by
    fun_induction Nat.sub <;> simp_all
  simp only [this]
  dprim_tac

open Nat.Partrec Denumerable in
def selfCallWith (x : ℕ) : Part ℕ :=
  (ofNat Code x.unpair.1).eval x

open Nat.Partrec Denumerable Encodable in
def thing (selfCallWith : Code) (x : ℕ) : Part ℕ :=
  x.unpaired fun f x => x.unpaired fun x n =>
    (ofNat Code f).eval (Nat.pair n (encode (selfCallWith.curry x)))

open Nat.Partrec Denumerable Encodable in
def ycomb (thing : Code) (x : ℕ) : Part ℕ :=
  x.unpaired fun f n =>
    (thing.curry f).eval (Nat.pair (encode (thing.curry f)) n)

open Nat.Partrec in
theorem selfCallWith_part : Nat.Partrec selfCallWith := by
  rw [← Partrec.nat_iff]
  exact Code.eval_part.comp (.comp (.ofNat _) (.comp .fst .unpair)) .id

open Nat.Partrec in
theorem thing_part (selfCallWith : Code) : Nat.Partrec (thing selfCallWith) := by
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
theorem ycomb_part (thing : Code) : Nat.Partrec (ycomb thing) := by
  rw [← Partrec.nat_iff]
  have : Computable₂ Nat.pair := by
    refine Primrec.to_comp ?_
    simpa [Primrec] using Nat.Primrec.succ
  refine Code.eval_part.comp ?_ ?_
  · exact Code.primrec₂_curry.to_comp.comp (.const _) (.comp .fst .unpair)
  · refine this.comp ?_ (.comp .snd .unpair)
    refine .comp .encode ?_
    exact Code.primrec₂_curry.to_comp.comp (.const _) (.comp .fst .unpair)

open Nat.Partrec (Code) in
theorem dcomputable_reassoc {α : Sort u} {β : α → Sort v} {γ : (a : α) ×' β a → Sort w}
    {δ : (x : (a : α) ×' β a) ×' γ x → Sort w'}
    [EncodingRelation α] [∀ x, EncodingRelation (β x)] [∀ x, EncodingRelation (γ x)]
    [∀ x, EncodingRelation (δ x)]
    (f : (x : (x : (a : α) ×' β a) ×' γ x) → δ x) :
    DComputable f ↔ DComputable fun x : (a : α) ×' (b : β a) ×' γ ⟨a, b⟩ =>
      f ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := by
  constructor
  · intro hf
    refine DComputable.comp hf (DPrimrec.dcomputable ?_)
    dprim_tac
  · intro hf
    refine DComputable.comp
      (g := fun x : (x : (a : α) ×' β a) ×' γ x => ⟨x.1.1, x.1.2, x.2⟩) hf ?_
    refine DPrimrec.dcomputable ?_
    dprim_tac

instance : EncodingRelation (Acc r a) := instEncodingRelationProof

open Nat.Partrec Denumerable in
@[dprim]
theorem DComputable.accRec.{c, v, u}
    {ctx : Sort c} {α : ctx → Sort u} {r : (c : ctx) → α c → α c → Prop}
    {motive : (c : ctx) → (a : α c) → Acc (r c) a → Sort v}
    {intro : (c : ctx) → (a : α c) → (h : ∀ b, r c b a → Acc (r c) b) →
      (ih : ∀ b hb, motive c b (h b hb)) → motive c a (Acc.intro a h)}
    {a : (c : ctx) → α c} {t : (c : ctx) → Acc (r c) (a c)}
    [EncodingRelation ctx] [∀ c a b, EncodingRelation (r c a b)]
    [∀ c, EncodingRelation (α c)] [∀ c a h, EncodingRelation (motive c a h)]
    (hintro : DComputable intro) (ha : DComputable a) :
    DComputable fun c => @Acc.rec (α c) (r c) (motive c) (intro c) (a c) (t c) := by
  by_cases hprop : IsProp.{imax (max (max 1 u) (imax (max 1 u) v)) v}
  · have := @(isProp_of_isProp_imax.{max (max 1 u) (imax (max 1 u) v), v} hprop).irrelevant
    exact .irrel
  by_cases hprop : IsProp.{imax (max 1 u) v}
  · have := @(isProp_of_isProp_imax.{max 1 u, v} hprop).irrelevant
    exact .irrel
  have : DComputable (fun c : ctx =>
      fun x :
        (a : { a : α c // ∀ b, r c b a → Acc (r c) b }) ×'
          (∀ b : { b // r c b a }, motive c b (a.2 b b.2)) =>
          intro c x.1.1 x.1.2 fun b hb => x.2 ⟨b, hb⟩) := by
    simp only [dcomputable_curry, dcomputable_reassoc] at hintro ⊢
    let ty := (c : ctx) ×' (a : { a : α c // ∀ b, r c b a → Acc (r c) b }) ×'
      (∀ b : { b // r c b a }, motive c b (a.2 b b.2))
    refine DComputable.comp
      (g := fun a : ty => ⟨a.1, a.2.1.1, a.2.1.2, fun b hb => a.2.2 ⟨b, hb⟩⟩) hintro ?_
    dprim_tac
  obtain ⟨gi, hgi, hgi'⟩ := this
  obtain ⟨ga, hga, hga'⟩ := ha
  obtain ⟨scw, hscw⟩ := Code.exists_code.mp selfCallWith_part
  obtain ⟨th, hth⟩ := Code.exists_code.mp (thing_part scw)
  have hyc := ycomb_part th
  refine ⟨_, .comp hyc (.pair hgi hga), ?_⟩
  intro n b hn
  obtain ⟨na, hna, hna'⟩ := hga' hn
  obtain ⟨ni, hni, hc⟩ := hgi' hn
  let c := Denumerable.ofNat Code ni
  rw [encodes_pi_def] at hc
  clear hga' hgi' hintro
  specialize t b
  have (eq := haeq) a := a b
  dsimp +instances only
  rw! [← haeq] at t hna' ⊢
  simp only [Part.eq_some_iff.mpr hni, Part.map_eq_map, Part.map_some, Part.eq_some_iff.mpr hna,
    seq_eq_bind_map, Part.bind_eq_bind, Part.bind_some]
  change ∃ y ∈ _, EncodingRelation.Encodes y (@Acc.rec (α b) (r b) (motive b) (intro b) a t)
  clear hna haeq
  induction t generalizing na with | intro a ha ih
  have hycomb : ∃ g, (∀ n, (ofNat Code g).eval n = ycomb th (Nat.pair ni n)) ∧
      ycomb th (Nat.pair ni na) = c.eval (Nat.pair na g) := by
    refine ⟨Encodable.encode (scw.curry (Encodable.encode (th.curry ni))), ?_, ?_⟩
    · intro n
      simp [hscw, selfCallWith, ycomb]
    · simp [ycomb, hth, thing, c]
  obtain ⟨g, hg, hg'⟩ := hycomb
  specialize hc (Nat.pair na g)
    ⟨⟨a, ha⟩, fun q => @Acc.rec (α b) (r b) (motive b) (intro b) q.1 (ha q.1 q.2)⟩
  specialize hc ⟨by simpa using hna', ?_⟩
  · simp only [Nat.unpair_pair]
    rw [encodes_pi_def]
    intro x ⟨y, hy⟩ h
    obtain ⟨z, hz, hz'⟩ := ih y hy x h
    simp only [hg]
    use z, hz, hz'
  simpa only [hg', c] using hc

attribute [local instance] instEncodingRelationOfEncodable in
instance : EncodingRelation Bool := inferInstance

instance : EncodingRelation (Decidable p) where
  Encodes n _ := EncodingRelation.Encodes n (decide p)

instance : FullyRepresentable (Decidable p) where
  representable
    | .isFalse _ => ⟨0, rfl⟩
    | .isTrue _ => ⟨1, rfl⟩

@[dprim]
theorem DPrimrec.boolRec {ctx : Sort u} {motive : ctx → Bool → Sort v}
    {false : (c : ctx) → motive c false} {true : (c : ctx) → motive c true}
    {t : ctx → Bool} [EncodingRelation ctx] [∀ c b, EncodingRelation (motive c b)]
    (ha : DPrimrec false) (hb : DPrimrec true) (ht : DPrimrec t) :
    DPrimrec fun c => @Bool.rec (motive c) (false c) (true c) (t c) := by
  obtain ⟨ga, hga, hga'⟩ := ha
  obtain ⟨gb, hgb, hgb'⟩ := hb
  obtain ⟨gt, hgt, hgt'⟩ := ht
  refine ⟨_, .comp (.prec hga (.comp hgb .left)) (.pair .id hgt), ?_⟩
  intro a b h
  specialize hga' h
  specialize hgb' h
  specialize hgt' h
  cases htb : t b
  · simp +instances only [htb] at hgt' ⊢
    rw [show gt a = 0 from hgt', htb]
    simpa using hga'
  · simp +instances only [htb] at hgt' ⊢
    rw [show gt a = 1 from hgt', htb]
    simpa using hgb'

protected dprim_decl DPrimrec.boolCasesOn for Bool.casesOn
protected dprim_decl DPrimrec.and for and unfolding Bool.and.match_1
protected dprim_decl DPrimrec.or for or unfolding cond.match_1
protected dprim_decl DPrimrec.not for not unfolding cond.match_1
protected dprim_decl DPrimrec.cond for cond unfolding cond.match_1

@[dprim]
theorem DPrimrec.decidableIsFalse {ctx : Sort u} {p : ctx → Prop} {h : (c : ctx) → ¬p c}
    [EncodingRelation ctx] : DPrimrec fun c => isFalse (h c) := by
  use 0, .zero
  intros
  rfl

@[dprim]
theorem DPrimrec.decidableIsTrue {ctx : Sort u} {p : ctx → Prop} {h : (c : ctx) → p c}
    [EncodingRelation ctx] : DPrimrec fun c => isTrue (h c) := by
  refine ⟨_, .comp .succ .zero, ?_⟩
  intros
  rfl

@[dprim]
theorem DPrimrec.decidableRec
    {ctx : Sort u} {p : ctx → Prop} {motive : (c : ctx) → Decidable (p c) → Sort v}
    {isFalse : (c : ctx) → (h : ¬p c) → motive c (isFalse h)}
    {isTrue : (c : ctx) → (h : p c) → motive c (isTrue h)}
    {t : (c : ctx) → Decidable (p c)}
    [EncodingRelation ctx] [∀ c, EncodingRelation (p c)] [∀ c t, EncodingRelation (motive c t)]
    (hf : DPrimrec fun x : (c : ctx) ×' ¬p c => isFalse x.1 x.2)
    (ht : DPrimrec fun x : (c : ctx) ×' p c => isTrue x.1 x.2)
    (hb : DPrimrec t) :
    DPrimrec fun c => @Decidable.rec (p c) (motive c) (isFalse c) (isTrue c) (t c) := by
  obtain ⟨gf, hgf, hgf'⟩ := hf
  obtain ⟨gt, hgt, hgt'⟩ := ht
  obtain ⟨gb, hgb, hgb'⟩ := hb
  refine ⟨_, .comp (.prec (.comp hgf (.pair .id .zero))
    (.comp (.comp hgt (.pair .id .zero)) .left)) (.pair .id hgb), ?_⟩
  intro a b h
  specialize hgb' h
  cases htb : t b
  · simp +instances only [htb] at hgb' ⊢
    rw [show gb a = 0 from hgb', htb]
    simpa using @hgf' (Nat.pair a 0) ⟨b, ‹_›⟩ ⟨by simpa, by simp⟩
  · simp +instances only [htb] at hgb' ⊢
    rw [show gb a = 1 from hgb', htb]
    simpa using @hgt' (Nat.pair a 0) ⟨b, ‹_›⟩ ⟨by simpa, by simp⟩

@[dprim]
theorem DPrimrec.decidableCasesOn
    {ctx : Sort u} {p : ctx → Prop} {motive : (c : ctx) → Decidable (p c) → Sort v}
    {t : (c : ctx) → Decidable (p c)}
    {isFalse : (c : ctx) → (h : ¬p c) → motive c (isFalse h)}
    {isTrue : (c : ctx) → (h : p c) → motive c (isTrue h)}
    [EncodingRelation ctx] [∀ c, EncodingRelation (p c)] [∀ c t, EncodingRelation (motive c t)]
    (hf : DPrimrec fun x : (c : ctx) ×' ¬p c => isFalse x.1 x.2)
    (ht : DPrimrec fun x : (c : ctx) ×' p c => isTrue x.1 x.2)
    (hb : DPrimrec t) :
    DPrimrec fun c => @Decidable.casesOn (p c) (motive c) (t c) (isFalse c) (isTrue c) := by
  dprim_tac [Decidable.casesOn]

protected dprim_decl DPrimrec.instDecidableAnd for instDecidableAnd
  unfolding instDecidableAnd.match_1
protected dprim_decl DPrimrec.instDecidableOr for instDecidableOr
  unfolding instDecidableAnd.match_1
protected dprim_decl DPrimrec.instDecidableNot for instDecidableNot
  unfolding instDecidableAnd.match_1
protected dprim_decl DPrimrec.boolDecEq for Bool.decEq unfolding Bool.decEq.match_1
protected dprim_decl DPrimrec.instDecidableEqBool for instDecidableEqBool

@[dprim]
protected theorem DPrimrec.dite
    {ctx : Sort u} {α : ctx → Sort v} {p : ctx → Prop} {hp : (c : ctx) → Decidable (p c)}
    {t : (c : ctx) → p c → α c} {f : (c : ctx) → ¬p c → α c}
    [EncodingRelation ctx] [∀ c, EncodingRelation (α c)] [∀ c, EncodingRelation (p c)]
    (hhp : DPrimrec hp)
    (ht : DPrimrec fun x : (c : ctx) ×' p c => t x.1 x.2)
    (hf : DPrimrec fun x : (c : ctx) ×' ¬p c => f x.1 x.2) :
    DPrimrec fun c => @dite (@α c) (p c) (hp c) (t c) (f c) := by
  dprim_tac [dite]

protected dprim_decl DPrimrec.ite for ite

@[dprim]
protected theorem DPrimrec.natBle {ctx : Sort u} {x y : ctx → ℕ}
    [EncodingRelation ctx] (hx : DPrimrec x) (hy : DPrimrec y) :
    DPrimrec fun c => (x c).ble (y c) := by
  have (a b : ℕ) : a.ble b = (a.sub b).rec true fun _ _ => false := by
    by_cases h : a ≤ b
    · simp [Nat.ble_eq_true_of_le h, Nat.sub_eq_zero_of_le h]
    · have : a.sub b = a - b - 1 + 1 := by grind
      rw [this]
      simp [mt Nat.le_of_ble_eq_true h]
  simp only [this]
  dprim_tac

@[dprim]
protected theorem DPrimrec.natBeq {ctx : Sort u} {x y : ctx → ℕ}
    [EncodingRelation ctx] (hx : DPrimrec x) (hy : DPrimrec y) :
    DPrimrec fun c => (x c).beq (y c) := by
  have (a b : ℕ) : a.beq b = (a.ble b && b.ble a) := by
    rw [Bool.eq_iff_iff]
    simp [Nat.le_antisymm_iff]
  simp only [this]
  dprim_tac

@[dprim]
protected theorem DPrimrec.eqRec.{u, w, v}
    {ctx : Sort u} {α : ctx → Sort v} {a : (c : ctx) → α c}
    {motive : (c : ctx) → (b : α c) → a c = b → Sort w}
    {refl : (c : ctx) → motive c (a c) (Eq.refl (a c))}
    {b : (c : ctx) → α c} {t : (c : ctx) → a c = b c}
    [EncodingRelation ctx] [∀ a b c, EncodingRelation (motive a b c)]
    (hrefl : DPrimrec refl) :
    DPrimrec fun c => @Eq.rec (α c) (a c) (motive c) (refl c) (b c) (t c) := by
  rw! (castMode := .all) [← funext t]
  exact hrefl

@[dprim]
protected theorem DPrimrec.natDecEq.match_1
    {ctx : Sort u} {motive : ctx → Bool → Sort v}
    {b : ctx → Bool}
    {t : (c : ctx) → b c = true → motive c true}
    {f : (c : ctx) → b c = false → motive c false}
    [EncodingRelation ctx] [∀ c b, EncodingRelation (motive c b)]
    (hb : DPrimrec b)
    (ht : DPrimrec fun x : (c : ctx) ×' b c = true => t x.1 x.2)
    (hf : DPrimrec fun x : (c : ctx) ×' b c = false => f x.1 x.2) :
    DPrimrec fun c => @Nat.decEq.match_1 (motive c) (b c) (t c) (f c) := by
  have (c : ctx) :
      @Nat.decEq.match_1 (motive c) (b c) (t c) (f c) =
        if h : b c then h ▸ t c h
        else
          haveI h : b c = false := by simpa using h
          h ▸ f c h := by
    split
    · have := Nat.decEq.match_1.congr_eq_1 (motive c) (b c) (t c) (f c) ‹_›
      apply eq_of_heq
      rw! (castMode := .all) [this, ‹b c = true›]
      rfl
    · have : b c = false := by simpa using ‹¬b c = true›
      have := Nat.decEq.match_1.congr_eq_2 (motive c) (b c) (t c) (f c) ‹_›
      apply eq_of_heq
      rw! (castMode := .all) [this, ‹b c = false›]
      rfl
  simp only [this]
  dprim_tac

dprim_decl DPrimrec.instDecidableEqNat for instDecidableEqNat unfolding Nat.decEq
dprim_decl DPrimrec.natDecLe for Nat.decLe
dprim_decl DPrimrec.natDecLt for Nat.decLt

example : DPrimrec (fun a : ℕ => if a ≠ 3 then 2 else 5) := by dprim_tac
