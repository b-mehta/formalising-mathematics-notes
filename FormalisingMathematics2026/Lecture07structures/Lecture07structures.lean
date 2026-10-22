/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!
# Lecture 7: Structures
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section

variable {α β γ : Type*}

/-
We now have the tools to start developing basic mathematics in Lean.
In this lecture we will develop the theory of bijective functions
to get a sense of best practices for developing mathematics in Lean.

The first thing we must do is write down the relevant definitions.
It is good practice to write a short docstring for each definition.
These will appear whenever you hover over any occurance of that definition.
-/

/-- A function `f : α → β` is injective if `f x = f y` implies `x = y`. -/
def Injective (f : α → β) : Prop :=
  ∀ a b : α, f a = f b → a = b

/-- A function `f : α → β` is surjective if every `b : β` is equal to `f a` for
some `a : α`. -/
def Surjective (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

/-- A function is bijective if it is both injective and surjective. -/
def Bijective (f : α → β) : Prop :=
  Injective f ∧ Surjective f

/-
Notice that we wrote `Injective f` and `Surjective f` instead of
`Injective α β f` and `Surjective α β f`, even though `α` and `β`
are arguments to `Injective` and `Surjective`. This is because we
marked `α` and `β` as implicit arguments with braces `{α β : Type*}`.
Implicit arguments are not passed in and are instead inferred from
the explicit arguments. For the definitions above, `α` and `β` can
be inferred from the type of `f : α → β`, so it is reasonable to
make `α` and `β` implicit.

Next, it is a good idea to write some basic "API" for these definitions.
API is a computer science term, but in Lean it refers to basic lemmas about
the new defition that allow you to work with the definition without having
to unfold it. If API is comprehensive and well written, then later code
referring to the definition may never have to unfold the definition directly,
but can instead reason purely from the API lemmas about the definition.

API is often updated as additional code reveals gaps in the existing API.
-/

theorem injective_id : Injective (id : α → α) := by
  intro a b h
  exact h

theorem surjective_id : Surjective (id : α → α) := by
  intro a
  use a
  rfl

theorem bijective_id : Bijective (id : α → α) := by
  constructor
  · exact injective_id
  · exact surjective_id

variable {f : α → β} {g : β → γ}

theorem Injective.comp (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := by
  intro a b h
  apply hf
  apply hg
  exact h

theorem Surjective.comp (hg : Surjective g) (hf : Surjective f) :
    Surjective (g ∘ f) := by
  intro c
  rcases hg c with ⟨b, hb⟩
  rcases hf b with ⟨a, ha⟩
  use a
  rw [Function.comp_apply, ha, hb]

theorem Bijective.comp (hg : Bijective g) (hf : Bijective f) :
    Bijective (g ∘ f) := by
  rcases hf with ⟨hf_inj, hf_surj⟩
  rcases hg with ⟨hg_inj, hg_surj⟩
  constructor
  · exact hg_inj.comp hf_inj
  · exact hg_surj.comp hf_surj

/-
Notice that we could write `hg_inj.comp hf_inj` and `hg_surj.comp hf_surj`
instead of `Injective.comp hg_inj hf_inj` and `Surjective.comp hg_surj hf_surj`.
This is called dot-notation. In this case, `hg_inj` has type `Injective f`, so
`hg_inj.comp` tells Lean to look for a theorem called `Injective.comp`.
-/

theorem Injective.of_comp (hgf : Injective (g ∘ f)) : Injective f := by
  intro a b hf
  apply hgf
  rw [Function.comp_apply, Function.comp_apply, hf]

theorem Surjective.of_comp (hgf : Surjective (g ∘ f)) : Surjective g := by
  intro c
  rcases hgf c with ⟨a, ha⟩
  use f a
  exact ha

/-
Here are two more examples of basic API lemmas as examples for you to try.
-/

theorem Injective.of_comp_right (hgf : Injective (g ∘ f)) (hf : Surjective f) :
    Injective g := by
  sorry

theorem Surjective.of_comp_left (hgf : Surjective (g ∘ f)) (hg : Injective g) :
    Surjective f := by
  sorry

/-
A predicate `Bijective` on functions `f : α → β` is one possible way
to translate the mathematical notion of bijective functions into Lean.
This is called the "unbundled" approach. The bundled approach would be
to define a type of all bijective functions `α → β` so that the function
and its bijectivity are bundled together into a single term. But there
are still several ways in which this bundled type could be implemented.
One option would be to define a bijective function to be a pair of a
function `f : α → β` and a proof `hf : Bijective f`. Another option would
be to define a bijective function to be a tuple of a function `f : α → β`,
an inverse function `g : β → α`, and proofs of `g ∘ f = id` and `f ∘ g = id`.

In Lean, the way to define types like this is with the `structure` command.
-/

/-- A bundled bijection consisting of a function and a proof of bijectivity. -/
structure BundledBij (α β : Type*) where
  f : α → β
  hf : Bijective f

#check BundledBij
#check BundledBij.f
#check BundledBij.hf

/-
This defines a type `BundledBij α β` whose terms consist of a pair of a
function `f : α → β` and a proof `hf : BundledBij hf`.
-/

/-- The bundled bijection from a type to itself. -/
def BundledBij.refl : BundledBij α α where
  f := id
  hf := bijective_id

/-- Composition of bundled bijections. -/
def BundledBij.trans (e1 : BundledBij α β) (e2 : BundledBij β γ) :
    BundledBij α γ where
  f := e2.f ∘ e1.f
  hf := e2.hf.comp e1.hf

/-
However, defining the inverse bijection `BundledBij.symm` is not so easy,
and would end up being hard to work with due to bad definitional equality.
A better approach is to bundle the inverse function into the structure itself.
-/

/-- An equivalence consisting of an inverse pair of functions. -/
structure MyEquiv (α β : Type*) where
  toFun : α → β
  invFun : β → α
  left_inv : invFun ∘ toFun = id
  right_inv : toFun ∘ invFun = id

theorem MyEquiv.invFun_toFun (e : MyEquiv α β) (a : α) :
    e.invFun (e.toFun a) = a := by
  rw [← e.invFun.comp_apply, e.left_inv, id_eq]

theorem MyEquiv.toFun_invFun (e : MyEquiv α β) (b : β) :
    e.toFun (e.invFun b) = b := by
  rw [← e.toFun.comp_apply, e.right_inv, id_eq]

/-- The equivalence from a type to itself. -/
def MyEquiv.refl (α : Type*) : MyEquiv α α where
  toFun := id
  invFun := id
  left_inv := rfl
  right_inv := rfl

/-- Inverse of an equivalence. -/
def MyEquiv.symm (e : MyEquiv α β) : MyEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Composition of equivalences. -/
def MyEquiv.trans (e1 : MyEquiv α β) (e2 : MyEquiv β γ) : MyEquiv α γ where
  toFun := e2.toFun ∘ e1.toFun
  invFun := e1.invFun ∘ e2.invFun
  left_inv := by
    ext a
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
      e2.invFun_toFun, e1.invFun_toFun, id_eq]
  right_inv := by
    ext a
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
      e1.toFun_invFun, e2.toFun_invFun, id_eq]

/-
With this bundled approach, `MyEquiv.symm` has nice definitional equality.
-/

theorem MyEquiv.symm_symm (e : MyEquiv α β) : e.symm.symm = e := by
  rfl

theorem MyEquiv.symm_trans (e1 : MyEquiv α β) (e2 : MyEquiv β γ) :
    (e1.trans e2).symm = e2.symm.trans e1.symm := by
  rfl

/-
Lastly, let us conclude by relating the unbundled and bundled approaches to
bijective functions. Proving that an equivalence is a bijective function is
not so hard, and is left as an example for you to try.
-/

theorem MyEquiv.bijective (e : MyEquiv α β) : Bijective e.toFun := by
  sorry

/-
Producing an equivalence from a bijective function is more difficult.
This requires constructing data inside of the proof. The first issue
is that the `have` tactic merely remembers that you have a term of the
given type but will immediately forget how the term was defined. This
hasn't been a problem for propositions since all that matters is that
the proposition has a proof, not what the specific proof is. But for
terms that contain data, the `have` tactic is usually insufficient
(unless only the existence of a term of the given type is needed).
The tactic to use instead is the `let` tactic is the same as the
`have` tactic but does not throw away the definition of the term.
The second issue is producing the inverse function from surjectivity
`∀ b : β, ∃ a : α, f a = b`. Fortunately, there is a (rarely used)
tactic called `choose` that solves exactly this problem of producing
a choice function from an assumption of the form `∀ ..., ∃ ..., ...`.
-/

theorem Bijective.exists_myEquiv (f : α → β) (hf : Bijective f) :
    ∃ e : MyEquiv α β, e.toFun = f := by
  rcases hf with ⟨hf_inj, hf_surj⟩
  choose g hg using hf_surj
  let e : MyEquiv α β :=
  { toFun := f
    invFun := g
    left_inv := by
      sorry
    right_inv := by
      sorry }
  use e
