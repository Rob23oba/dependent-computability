# Dependent computability

> Disclaimer: This project currently only compiles on PR releases from leanprover/lean4#8867.
> The reason for this is that we need `imax u (imax u v) = imax u v` and the current version of Lean doesn't provide this defeq.
> The simplest solution I could come up with was to reuse my PR for complete level defeq as the toolchain of this project.

A framework for automatically proving that a function is computable. This project builds upon the existing computability API that mathlib provides;
however, the existing definition of `Computable` is insufficient for several reasons:
1. It doesn't work for dependent functions.
2. It only works for types that are countable and e.g. not for a function that has `ℕ → ℕ` as a domain.

The solution in this project is to only require a relation `α → ℕ → Prop` that relates values with its encodings.
In particular, one value may have many encodings (e.g. with `Quot`), one value may have no encodings (e.g. all noncomputable functions) and
one encoding may have many values associated with it (e.g. with `Sort u`; all types are encoded as `0`).

Additionally, we define a predicate `DComputable` that describes whether a function is computable (and similarly `DPrimrec` for primitive-recursive functions).
However, you'll probably end up using `DComp` and `DPrim` more, which have the convenient signature `{α : Sort u} {β : α → Sort v} (f : (a : α) → β a) : Prop`.
More on why this is possible in the next section.

## A new world

One question you might ask yourself is how exactly encoding relations are associated to a type. A simple idea would be instance search -- just write a `class EncodingRelation (α : Sort u)` and provide it as an assumption for `DComputable` and `DPrimrec`.
However, this falls apart when looking at types like this one:
```lean4
structure Any.{u} where
  ty : Sort u
  value : ty
```
What should the encoding relation for `Any` be? Well, obviously we should encode an `Any` like we encode the `value`; however we don't know the encoding relation on `ty`!
Because any value could have types hidden inside of it, we'll just provide a new declaration for "extra stuff" that belongs to the original declaration. For a type `α : Sort u`, that extra stuff is:
1. A type for extra stuff associated to a value `a : α`, that is, a function `Extra : α → Sort u`. In the case of `Any`, this will be a pair of extra stuff for `ty` and extra stuff for `value`.
2. An encoding relation that relates value `a : α` in combination with their extra stuff `a_extra : Extra a` with natural numbers, that is, a function `⦃a : α⦄ → Extra a → ℕ → Prop`.
   In the case of `Any`, you could choose to relate `a` and `a_extra` with `n` iff the encoding of `ty` (contained in `a_extra`) relates `a.val` with `n`; but for implementation reasons,
   the relation ends up encoding `a_extra` as `Nat.pair 0 n` iff the encoding of `ty` relates `a.val` with `n`.
3. An assertion that if `α` is a proposition then the encoding relation is trivial (i.e. everything is encoded as `0`). We need this for proof irrelevance and for `propext`.

We collect these three things in the type `SortExtra α`. For the first entry in the list, we make a special elaborator: `new_type% a` for `a : α` elaborates to `α'.1 a` where `α' : SortExtra α`.
Notably, `new_type% α = SortExtra α` for a type `α : Sort u` so we use that as the standard spelling for `SortExtra` instead of using `SortExtra` directly.
Furthermore, we add the `new% a` elaborator which provides the canonical term of type `new_type% a` (if it can).
After that, we use the namespace `New` for the extra stuff for existing declarations. Specifically, given a constant `abc`, `New.abc` contains the "extra stuff" associated to `abc` and `new% abc` will also translate to `New.abc`.
Declarations are translated automatically into the new universe when using `new%` or `new_type%` but you can also use `convert_to_new abc xyz` to generate `New.abc` and `New.xyz`.
Most of the time, this essentially uses the `new%` elaborator to convert the value of the declaration but for some constants (notably, inductive types) there are special handlers.
Sometimes however, automation is not enough and you have to put a constant into the new world manually. This involves creating a declaration `def New.xyz.{u, v} : new_type% @xyz.{u, v}` directly.
For example, this is necessary to convert some of the foundational declarations into the new world, like `Quot`, `propext` and `Quot.sound`.

One thing you might notice is that there are two values for `SortExtra True`: 3. ensures that there is only one possible encoding relation but the extra type for a proof `h : True` can still be either `False` or `True`.
This results in two different "true" propositions: a real true proposition and a "false" true proposition. So notably, the new universe is non-classical since there are three propositions.
This can prevent translating declarations that depend on `Classical.choice`, even if only in proofs. However, many proofs can still be translated into the new world as long as we can be sure that we don't
work with the "middle" proposition. Also, while it's not possible to use general choice, `uniqueChoice`, the axiom of unique choice, is still available.

Now, while you might see this non-classicality as a disadvantage at first, it turns out to be quite useful! For example, `DPrim` and `DComp` are always true in the regular world but are sometimes false in the new world.
This allows you to write proofs using `DPrim` and `DComp` and convert them using `convert_to_new`, resulting in an actual proof of computability!

## Example

```lean4
import DependentComputability

def test (x : Nat) : Nat :=
  (((x / (x + 3) : Rat) * 30) ^ 2 - 27).floor.toNat

set_option Elab.async false in
lemma test_computable : Computable test := by
  have_new hcomp : DComp test := by
    dcomp_tac
  exact hcomp_extra.computable (new% test)
```

In the first step, we prove `DComp test` using `dcomp_tac` and, using `have_new`, automatically get a proof in the new universe. Then, we use `DComputable.computable` to translate this proof into a proof of mathlib's `Computable` predicate.
To help type inference, we also specify the new form of what we want to prove computable. We don't need to be so specific here though; using `new% _` is enough for the `new%` elaborator to know what to do.
During this process, we generate many auxiliary definitions and lemmas; this doesn't work too well with `Elab.async` so we have to disable it here.
