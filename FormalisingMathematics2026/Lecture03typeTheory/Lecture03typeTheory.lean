/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!
# Lecture 3: Type Theory
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section

/-
So far we have learned tactics to work with the basic logical building blocks
`→` (implication), `∧` (and), `∨` (or), `¬` (not), `True`, and `False`.
We now turn to the two quantifiers: `∀` (for all) and `∃` (there exists).
But first we must answer the question: quantifying over what?

Usually mathematics is built on set theory, in which case we quantify over sets.
For example, there is a set `ℝ` of real numbers, a set `ℂ` of complex numbers,
and we could write `∀ x ∈ ℝ, x ^ 2 + 1 ≠ 0` or `∃ x ∈ ℂ, x ^ 2 + 1 = 0`.

But Lean is built on type theory rather than set theory.

In set theory, the fundamental relation is `x ∈ y` (`x` is an element of `y`).
Any given expression (e.g., `37`, `∅`) can be an element of many different sets.

In type theory, the fundamental relation is `x : y` (`x` is a term of type `y`).
The key difference is that every expression is a term of one and only one type.
Lean has the `#check` command to determine the type of a given expression.
-/

#check 37
#check (37 : ℤ)
#check (37 : ℚ)
#check (37 : ℝ)
#check (37 : ℂ)

/-
These five `37`'s are all different since they all have different types.
Note that these types are themselves expressions and thus must also have a type.
-/

#check ℕ
#check ℤ
#check ℚ
#check ℝ
#check ℂ

/-
It might look like `Type` is "the type of all types".
But then what type does `Type` have?
-/

#check Type
#check Type 1
#check Type 2

/-
Thus, Lean actually has a infinite heirarchy of universes. This helps avoid the
Russell-like paradoxes that arise with notions like "the set of all sets".

You can use the `def` command to define terms of a given type.
-/

def myFavoriteNumber : ℕ := 37
def myFavoriteType : Type := ℕ

#check myFavoriteNumber
#check myFavoriteType

/-
If the syntax for `def` with the `:` and the `:=` looks similar to the syntax
for `example`, it's because `example` and `def` are indeed exactly the same.
The only difference is that a `def` is named while an `example` is not.
-/

example : ℕ := 37
example : Type := ℕ

/-
This means that every previous theorem that we wrote as an `example` could
instead be written as `def`, although if you try then Lean will tell you to
use `theorem` instead of `def` for proofs of propositions.
-/

example (P : Prop) (h : P) : P := by
  exact h

def myFavoriteDef (P : Prop) (h : P) : P := by
  exact h

theorem myFavoriteTheorem (P : Prop) (h : P) : P := by
  exact h

#check myFavoriteTheorem

/-
In practice, the advantage of `def` and `theorem` over `example` is that a
`def` or `theorem` has a name so it can be referred to later and built upon.

Mathlib is a large library of hundreds of thousands of `def`s and `theorem`s
that build on each other to eventually reach hard mathematics.

We have actually already seen an example of a named `theorem`. If you
control-click on `trivial`, you will see `theorem trivial : True := ⟨⟩`.
Even though we do not yet understand this mysterious two character proof,
we are still able invoke this theorem when we write `exact trivial`.
-/

#check trivial
#check True
#check Prop

/-
You might be wondering how to make sense of `trivial` having type `True`.
We will get to this more in lecture 5, but basically every `Prop` (like `True`)
is itself a type whose terms are its proofs. So saying that `trivial` has type
`True` is exactly the same as saying that `trivial` is a proof of `True`.
Likewise, `(hP : P)` can be viewed as saying that `hP` is a proof of `P`.

Now returning to quantifiers, if `α` is a type, we can quantify over `α` by
writing `∀ a : α, ...` or `∃ a : α, ...`.
-/

example : ∀ x : ℝ, x ^ 2 + 1 ≠ 0 := by
  sorry

example : ∃ x : ℂ, x ^ 2 + 1 = 0 := by
  sorry

/-
It is also valid syntax to write `∀ a, ...` or `∃ a, ...` without the full
type ascription `a : α`. However, this forces Lean to infer the type of `a`,
possibly incorrectly. For example, in the example below, `x` is inferred to
have type `ℕ`, even though the proposition involves subtraction. This is because
Lean has defined a truncated subtraction on the natural numbers, so to Lean
the proposition makes perfect sense when `x` is taken to be a natural number.
-/

example : ∀ x, x - 1 < x := by
  sorry

/-
We will only need to learn one new tactic to be able to work with `∀` and `∃`.
When a goal is of the form `∃ a : α, ...` and you are able to write down a
specific `a : α`, the tactic `use a` will plug that specific `a` into the goal,
dropping the existential quantifier `∃`.
-/

example : ∃ P : Prop, ¬ P → P := by
  use True
  intro h
  exact trivial

/-
Sometimes `use` will do more than you expect and will close the resulting goal.
This is because `use` attempts to close any resulting goals with a "discharger".
-/

example : ∃ P : Prop, P := by
  use True

/-
To give more examples, we will work with an arbitrary predicate on an aribitrary
type. We can write `(α : Type*)` to indicate an arbitrary type in an arbitrary
universe (this is what `Type*` means), and `P : α → Prop` to denote an arbitrary
true/false predicate on `α`, expressed as a function from `α` to `Prop`.
-/

example (α : Type*) (P : α → Prop) (a : α) (h : P a) : ∃ a, P a := by
  use a

/-
We will learn more about functions in lecture 6, but one initial note is that
in Lean we write `P a` instead of `P(a)` (in fact, the latter gives an error).

When a hypothesis is of the form `hP : ∃ a : α, P a`, the tactic
`rcases hP with ⟨a, ha⟩` will extract a witness `a : α` and a proof `ha : P a`.
-/

example (α : Type*) (P Q : α → Prop) (hPQ : ∀ a, P a → Q a) (hP : ∃ a, P a) :
    (∃ a : α, Q a) := by
  rcases hP with ⟨a, ha⟩
  use a
  specialize hPQ a
  apply hPQ
  exact ha

/-
When a goal is of the form `∀ a : α, P a`, the tactic `intro a` will add an
arbitrary `a : α` as an assumption, and replace the goal with `P a`.

Likewise, when a hypothesis is of the form `hP : ∀ a : a, P a` and you are able
to write down a specific `a : α`, the tactic `specialize hP a` will plug that
specific `a` into the goal, dropping the universal quantifier `∀`.
-/

example (α : Type*) (P Q : α → Prop) (hPQ : ∀ a, P a → Q a) (hP : ∀ a, P a) :
    (∀ a : α, Q a) := by
  intro a
  specialize hP a
  specialize hPQ a
  apply hPQ
  exact hP

/-
Finally, it is worth thinking about which of our tactics so far are "safe" in
the sense that they cannot get you trapped with an impossible goal.

For example, `specialize` for `→` is always a safe tactic, since it merely
drops an assumption from a hypothesis, thereby strengthening your position.
Whereas `specialize` for `∀` is potentially unsafe since it destroys the
original hypothesis without allowing you to plug in other values.

So far, `exact`, `intro`, `specialize` (for `→`), `constructor`, `rcases`,
`by_contra`, `by_cases` are all safe tactics, whereas `apply`, `specialize`
(for `∀`), `have`, `suffices`, `left`, `right`, `use` are potentially unsafe.

However, the "safe" tactics are safe precisely because they do not fundamentally
change the current proof state mathematically. It is the potentially unsafe
tactics that are "useful" in the sense of genuinely altering the current state.
-/

/-
## Examples for you to try

Delete the `sorry`s and replace them with tactic proofs using the tactics
learned so far (`exact`, `intro`, `apply`, `specialize`, `have`, `suffices`,
`left`, `right`, `constructor`, `rcases`, `by_contra`, `by_cases`, `use`).
-/

example (α : Type*) (P : α → Prop) (h : ∀ a : α, ¬ P a) : ¬ ∃ a : α, P a := by
  sorry

example (α : Type*) (P : α → Prop) (h : ¬ ∀ a : α, P a) : ∃ a : α, ¬ P a := by
  sorry

example (α : Type*) (P : α → Prop) (h : ∃ a : α, ¬ P a) : ¬ ∀ a : α, P a := by
  sorry

example (α : Type*) (P : α → Prop) (h : ¬ ∃ a : α, P a) : ∀ a : α, ¬ P a := by
  sorry
