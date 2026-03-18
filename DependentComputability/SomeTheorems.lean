import DependentComputability.Tactic.Computability

convert_to_new Sum

#time #eval! proveConstructorComputable ``Sum.inl
#time #eval! proveConstructorComputable ``Sum.inr
#time #eval! proveConstructorComputable ``none
#time #eval! proveConstructorComputable ``some

#print Nat.Partrec.Code

#time #eval! proveConstructorComputable ``Nat.Partrec.Code.zero
#time #eval! proveConstructorComputable ``Nat.Partrec.Code.succ
#time #eval! proveConstructorComputable ``Nat.Partrec.Code.left
#time #eval! proveConstructorComputable ``Nat.Partrec.Code.right
#time #eval! proveConstructorComputable ``Nat.Partrec.Code.pair
#time #eval! proveConstructorComputable ``Nat.Partrec.Code.comp
#time #eval! proveConstructorComputable ``Nat.Partrec.Code.prec
#time #eval! proveConstructorComputable ``Nat.Partrec.Code.rfind'

#print Lean.Syntax
#time #eval! proveConstructorComputable ``Lean.Syntax.missing

--#time #eval! proveConstructorComputable ``Lean.Syntax.node
#time #eval! proveConstructorComputable ``Lean.Syntax.ident
#time #eval! proveConstructorComputable ``Lean.Syntax.atom

#print New.Nat.Partrec.Code._encoding.pair

#print New.Sum.inl.dprim
#print New.Sum.inl.dcomp
#print New.Nat.Partrec.Code.zero.dcomp
#print Sum.inl.dprim
/-

lemma Option.none.dprim {ctx : Sort u} {α : ctx → Type v} :
    DPrim (fun c => @Option.none (α c)) := .unsafeIntro

set_option linter.unusedVariables false in
lemma Option.some.dprim {ctx : Sort u} {α : ctx → Type v}
    (f : (c : ctx) → α c) (hf : DPrim f) :
    DPrim (fun c => some (f c)) := .unsafeIntro

def wfTest (x : Nat) : Nat :=
  if x = 0 then
    34
  else
    wfTest (x - 1)
termination_by (x, 0)
decreasing_by
  refine .left _ _ ?_
  exact Nat.sub_one_lt ‹_›

def New.Lean.opaqueId.{u} : new_type% @opaqueId.{0} :=
  fun _ _ _ h => (fun _ : Sort u => _root_.Lean.opaqueId h) PUnit.{u}

lemma _root_.New.Option.none.dprim.{u, v} : new_type% @Option.none.dprim.{u, v} := by
  have := TheoremBuilder.primResult.{u} <|
    .prependIrrelevant (α := new% fun _ : Unit => Type v) <|
    .baseTransformed (α := new% fun x : (_ : Unit) ×' Type v => Option x.2)
      (new% fun x : (_ : Unit) ×' Type v => @Option.none x.2) _ (Nat.Primrec.const 1)
  exact @this @New.Option._encoding.none.{v}

open TheoremBuilder in
lemma _root_.New.Option.some.dprim.{u, v} : new_type% @Option.some.dprim.{u, v} := by
  intro ctx_base ctx α_base α f_base f _ hf
  have := TheoremBuilder.primResult.{u} <|
    .prependIrrelevant (α := new% fun _ : Unit => Type v) <|
    .prependFirst (α := new% fun x : (_ : Unit) ×' Type v => x.2) <|
    .baseTransformed (α := new% fun x : (x : (_ : Unit) ×' Type v) ×' x.2 => Option x.1.2)
      (new% fun x : (x : (_ : Unit) ×' Type v) ×' x.2 => some x.2) _ (primrec_mul_add 2 2)
  exact @this @New.Option._encoding.some.{v} ctx_base ctx α_base α f_base f hf

-/
lemma _root_.New.Nat.pair.dprim.{u} : new_type% @Nat.pair.dprim.{u} := by
  rintro ctx_base ctx a_base a _ ⟨f, hf, hf'⟩ b_base b _ ⟨g, hg, hg'⟩
  refine ⟨_, .pair hf hg, ?_⟩
  intro a_base a n han
  rw [hf' han, hg' han]
  simp [New.Nat]

lemma New.PProd.dprim_toPSigma.{u, v, w} : new_type% @PProd.dprim_toPSigma.{u, v, w} := by
  rintro ctx_base ctx α_base α β_base β self_base self _ ⟨f, hf, hf'⟩
  refine ⟨f, hf, ?_⟩
  intro a_base a n han
  specialize hf' han
  generalize f n = fval at hf'
  obtain ⟨hxn, hyn⟩ := hf'
  exact ⟨by simpa using hxn, by simpa using hyn⟩

lemma _root_.New.PProd.dprim_ofPSigma.{u, v, w} : new_type% @PProd.dprim_ofPSigma.{u, v, w} := by
  rintro ctx_base ctx α_base α β_base β self_base self _ ⟨f, hf, hf'⟩
  refine ⟨f, hf, ?_⟩
  intro a_base a n han
  specialize hf' han
  generalize f n = fval at hf'
  obtain ⟨hxn, hyn⟩ := hf'
  rw [← Nat.pair_unpair fval]
  constructor <;> assumption

@[other_dprim]
lemma PProd.fst.dprim {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {self : (c : ctx) → PProd (α c) (β c)} (self_comp : DPrim self) :
    DPrim (fun c => (self c).1) :=
  PSigma.fst.dprim (PProd.dprim_toPSigma self_comp)

@[other_dprim]
lemma PProd.fst.dcomp {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {self : (c : ctx) → PProd (α c) (β c)} (self_comp : DComp self) :
    DComp (fun c => (self c).1) := by
  refine .app (.curry (.of_prim (PProd.fst.dprim ?_))) self_comp
  exact PSigma.snd.dprim .id

@[other_dprim]
lemma PProd.snd.dprim {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {self : (c : ctx) → PProd (α c) (β c)} (self_comp : DPrim self) :
    DPrim (fun c => (self c).2) :=
  PSigma.snd.dprim (PProd.dprim_toPSigma self_comp)

@[other_dprim]
lemma PProd.snd.dcomp {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {self : (c : ctx) → PProd (α c) (β c)} (self_comp : DComp self) :
    DComp (fun c => (self c).2) := by
  refine .app (.curry (.of_prim (PProd.snd.dprim ?_))) self_comp
  exact PSigma.snd.dprim .id

@[other_dprim]
lemma PProd.mk.dprim {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {fst : (c : ctx) → α c} (fst_comp : DPrim fst)
    {snd : (c : ctx) → β c} (snd_comp : DPrim snd) :
    DPrim (fun c => PProd.mk (fst c) (snd c)) :=
  PProd.dprim_ofPSigma (PSigma.mk.dprim fst_comp snd_comp)

set_option linter.unusedVariables false in
@[other_dprim]
lemma PProd.mk.dcomp {ctx : Sort u} {α : ctx → Sort v} {β : ctx → Sort w}
    {fst : (c : ctx) → α c} (fst_comp : DComp fst)
    {snd : (c : ctx) → β c} (snd_comp : DComp snd) :
    DComp (fun c => PProd.mk (fst c) (snd c)) := .unsafeIntro

set_option linter.unusedVariables false in
@[other_dprim]
lemma OfNat.ofNat.dcomp {ctx : Sort u} {α : ctx → Type v} {n : ctx → ℕ}
    {self : (c : ctx) → OfNat (α c) (n c)} (self_comp : DComp self) :
    DComp (fun c => (self c).ofNat) := .unsafeIntro

set_option linter.unusedVariables false in
@[other_dprim]
lemma OfNat.mk.dcomp {ctx : Sort u} {α : ctx → Type v} {n : ctx → ℕ}
    {ofNat : (c : ctx) → α c} (ofNat_comp : DComp ofNat) :
    DComp (fun c => @OfNat.mk (α c) (n c) (ofNat c)) := .unsafeIntro

lemma DComp.natLit {ctx : Sort u} (n : ℕ) : DComp (fun _ : ctx => n) := .unsafeIntro
lemma DComp.strLit {ctx : Sort u} (s : String) : DComp (fun _ : ctx => s) := .unsafeIntro

#eval! autoDComp ``Nat.casesOn
#eval! autoDComp ``Nat.brecOn.go
#eval! autoDComp ``Nat.brecOn
#eval! autoDComp ``Nat.add.match_1
#eval! autoDComp ``Nat.add
#eval! autoDComp ``Nat.mul.match_1
#eval! autoDComp ``Nat.pow.match_1
#eval! autoDComp ``instOfNatNat
#eval! autoDComp ``Nat.pred
#eval! autoDComp ``Nat.sub
#eval! autoDComp ``Nat.mul
#eval! autoDComp ``Nat.pow
#eval! autoDComp ``Nat.div
#eval! autoDComp ``Nat.div

#print New.Decidable._encoding
#print New.Bool._encoding

convert_to_new Nat.pow.dcomp

#print Nat.pow.dcomp
