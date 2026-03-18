import DependentComputability.SortExtra

inductive DComp {α : Sort u} {β : α → Sort v} (f : (a : α) → β a) : Prop where
  | unsafeIntro

inductive DPrim {α : Sort u} {β : α → Sort v} (f : (a : α) → β a) : Prop where
  | unsafeIntro

class Irrel (α : Sort u) : Prop where
  unsafeIntro ::

def _root_.New.DComp.{u, v} : new_type% @DComp.{u, v} :=
  fun _ _ _ _ _ f => .mk (fun _ => DComputable f) (TrivialEncoding _) (.trivialEncoding _)

def _root_.New.DPrim.{u, v} : new_type% @DPrim.{u, v} :=
  fun _ _ _ _ _ f => .mk (fun _ => DPrimrec f) (TrivialEncoding _) (.trivialEncoding _)

def _root_.New.Irrel.{u} : new_type% @Irrel.{u} :=
  fun _ α => .mk (fun _ => Irrelevant α) (TrivialEncoding _) (.trivialEncoding _)

section

set_option linter.unusedVariables.funArgs false

instance instIrrelProof (p : Prop) : Irrel p := .unsafeIntro
instance instIrrelSort : Irrel (Sort u) := .unsafeIntro
instance instIrrelForall {α : Sort u} {β : α → Sort v} [∀ a, Irrel (β a)] :
    Irrel ((a : α) → β a) := .unsafeIntro

lemma DPrim.id {α : Sort u} : DPrim (fun x : α => x) := .unsafeIntro
lemma DPrim.comp.{u, v, w} {β : Sort v} {γ : β → Sort w} {f : (b : β) → γ b}
    (hf : DPrim f) {α : Sort u} {g : α → β} (hg : DPrim g) :
    DPrim (fun x : α => f (g x)) := .unsafeIntro
lemma DPrim.compComputable.{u, v, w} {β : Sort v} {γ : β → Sort w} {f : (b : β) → γ b}
    (hf : DPrim f) {α : Sort u} {g : α → β} (hg : DComp g) :
    DComp (fun x : α => f (g x)) := .unsafeIntro
lemma DPrim.irrel {α : Sort u} {β : α → Sort v} [∀ a, Irrel (β a)]
    {f : (a : α) → β a} : DPrim f := .unsafeIntro
lemma DPrim.proof {α : Sort u} {β : α → Prop}
    {f : (a : α) → β a} : DPrim f := .irrel
lemma DPrim.sort {α : Sort u} {f : (a : α) → Sort v} : DPrim f := .irrel
lemma DPrim.curry {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}
    {f : (a : α) → (b : β a) → γ a b} (hf : DComp fun c : PSigma β => f c.1 c.2) :
    DPrim f := .unsafeIntro

lemma DComp.of_prim {α : Sort u} {β : α → Sort v}
    {f : (a : α) → β a} (hf : DPrim f) : DComp f := .unsafeIntro
lemma DComp.id {α : Sort u} : DComp (fun x : α => x) := .of_prim .id
lemma DComp.comp.{u, v, w} {β : Sort v} {γ : β → Sort w} {f : (b : β) → γ b}
    (hf : DComp f) {α : Sort u} {g : α → β} (hg : DComp g) :
    DComp (fun x : α => f (g x)) := .unsafeIntro
lemma DComp.irrel {α : Sort u} {β : α → Sort v} [∀ a, Irrel (β a)]
    {f : (a : α) → β a} : DComp f := .unsafeIntro
lemma DComp.proof {α : Sort u} {β : α → Prop}
    {f : (a : α) → β a} : DComp f := .irrel
lemma DComp.sort {α : Sort u} {f : (a : α) → Sort v} : DComp f := .irrel
lemma DComp.curry {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}
    {f : (a : α) → (b : β a) → γ a b} (hf : DComp fun c : PSigma β => f c.1 c.2) :
    DComp f := .of_prim (.curry hf)
lemma DComp.app.{c, u, v}
    {α : Sort c} {β : α → Sort u} {γ : (a : α) → β a → Sort v}
    {f : (a : α) → (b : β a) → γ a b} (hf : DComp f)
    {g : (a : α) → β a} (hg : DComp g) :
    DComp (fun x : α => f x (g x)) := .unsafeIntro

lemma _root_.New.instIrrelProof : new_type% @instIrrelProof := @instIrrelevant
lemma _root_.New.instIrrelSort.{u} : new_type% @instIrrelSort.{u} := @instIrrelevantSort
lemma _root_.New.instIrrelForall.{u, v} : new_type% @instIrrelForall.{u, v} :=
  fun _ α _ β _ h => @instIrrelevantForall _ α _ β h

lemma _root_.New.DPrim.id.{u} : new_type% @DPrim.id.{u} := @DPrimrec.id
lemma _root_.New.DPrim.comp.{u, v, w} : new_type% @DPrim.comp.{u, v, w} :=
  fun _ _ _ _ _ _ _ hf _ _ _ _ _ hg => .comp hf hg
lemma _root_.New.DPrim.compComputable.{u, v, w} : new_type% @DPrim.compComputable.{u, v, w} :=
  fun _ _ _ _ _ _ _ hf _ _ _ _ _ hg => hf.compComputable hg
lemma _root_.New.DPrim.irrel.{u, v} : new_type% @DPrim.irrel.{u, v} :=
  fun _ _ _ _ _ h _ _ => @DPrimrec.irrelevant _ _ _ _ h _ _
lemma _root_.New.DPrim.proof.{u} : new_type% @DPrim.proof.{u} := @DPrimrec.proof
lemma _root_.New.DPrim.sort.{u, v} : new_type% @DPrim.sort.{u, v} := @DPrimrec.sort
lemma _root_.New.DPrim.curry.{u, v, w} : new_type% @DPrim.curry.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ hf => .curry hf

lemma _root_.New.DComp.of_prim.{u, v} : new_type% @DComp.of_prim.{u, v} :=
  fun _ _ _ _ _ _ _ hf => .of_prim hf
lemma _root_.New.DComp.id.{u} : new_type% @DComp.id.{u} := @DComputable.id
lemma _root_.New.DComp.comp.{u, v, w} : new_type% @DComp.comp.{u, v, w} :=
  fun _ _ _ _ _ _ _ hf _ _ _ _ _ hg => .comp hf hg
lemma _root_.New.DComp.irrel.{u, v} : new_type% @DComp.irrel.{u, v} :=
  fun _ _ _ _ _ h _ _ => @DComputable.irrelevant _ _ _ _ h _ _
lemma _root_.New.DComp.proof.{u} : new_type% @DComp.proof.{u} := @DComputable.proof
lemma _root_.New.DComp.sort.{u, v} : new_type% @DComp.sort.{u, v} := @DComputable.sort
lemma _root_.New.DComp.curry.{u, v, w} : new_type% @DComp.curry.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ hf => .curry hf
lemma _root_.New.DComp.app.{u, v, w} : new_type% @DComp.app.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ hf _ _ _ hg => .app hf hg

lemma PSigma.mk.dprim {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → α c} (hf : DPrim f) {g : (c : ctx) → β c (f c)} (hg : DPrim g) :
    DPrim (fun c => PSigma.mk (f c) (g c)) := .unsafeIntro

lemma PSigma.fst.dprim {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → PSigma (β c)} (hf : DPrim f) :
    DPrim (fun c => (f c).1) := .unsafeIntro

lemma PSigma.snd.dprim {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → PSigma (β c)} (hf : DPrim f) :
    DPrim (fun c => (f c).2) := .unsafeIntro

lemma PSigma.mk.dcomp {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → α c} (hf : DComp f) {g : (c : ctx) → β c (f c)} (hg : DComp g) :
    DComp (fun c => PSigma.mk (f c) (g c)) := .unsafeIntro

lemma PSigma.fst.dcomp {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → PSigma (β c)} (hf : DComp f) :
    DComp (fun c => (f c).1) := .unsafeIntro

lemma PSigma.snd.dcomp {ctx : Sort u} {α : ctx → Sort v} {β : (c : ctx) → α c → Sort w}
    {f : (c : ctx) → PSigma (β c)} (hf : DComp f) :
    DComp (fun c => (f c).2) := .unsafeIntro

lemma _root_.New.PSigma.mk.dprim.{u, v, w} : new_type% @PSigma.mk.dprim.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ hf _ _ _ hg => New.PSigma.mk.primrec hf hg
lemma _root_.New.PSigma.fst.dprim.{u, v, w} : new_type% @PSigma.fst.dprim.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ hf => New.PSigma.fst.primrec hf
lemma _root_.New.PSigma.snd.dprim.{u, v, w} : new_type% @PSigma.snd.dprim.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ hf => New.PSigma.snd.primrec hf
lemma _root_.New.PSigma.mk.dcomp.{u, v, w} : new_type% @PSigma.mk.dcomp.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ hf _ _ _ hg => New.PSigma.mk.computable hf hg
lemma _root_.New.PSigma.fst.dcomp.{u, v, w} : new_type% @PSigma.fst.dcomp.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ hf => New.PSigma.fst.computable hf
lemma _root_.New.PSigma.snd.dcomp.{u, v, w} : new_type% @PSigma.snd.dcomp.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ _ hf => New.PSigma.snd.computable hf

end
