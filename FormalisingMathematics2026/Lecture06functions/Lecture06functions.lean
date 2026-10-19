/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!
# Lecture 6: Functions
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section

variable (α β γ : Type*)

/-
Given two types `α` and `β`, the type of all functions from `α` to `β` is
denoted by `α → β`. The value of a function `f : α → β` at a term `a : α` is
denoted by `f a`. The notation for writing down a specific function is
`fun a : α ↦ f a`.
-/

example : ℕ → ℕ := fun n ↦ n + 1

/-
The `def` command with arguments before the colon also produces functions.
-/

def myFun (n : ℕ) : ℕ := n + 1

#print myFun

/-
However, when there are two arguments before the colon, rather than producing
a function of type `ℕ × ℕ → ℕ`, we instead get a function `ℕ → ℕ → ℕ`.
This is known as "currying".
-/

def myFun2 (m n : ℕ) : ℕ := n + m

#print myFun2

/-
In other words, this is a function that outputs a function! In order to evaluate
this function at `m` and `n`, we must first plug in `m`, and then plug in `n`.
-/

#check myFun2 1 1

/-
If we only plug in the first argument, then we get the partially applied
function `myFun2 1 : ℕ → ℕ`.
-/

#check myFun2 1

/-
To prove that two functions `f g : α → β` are equal, the tactic `ext a` will
add an arbitrary `a : α` as an assumption and replace the goal with `f a = g a`.
-/

example : myFun = myFun2 1 := by
  ext n
  rfl

/-
Two more things to know are the identity function `id : α → α` and
function composition `f ∘ g`. They satisfy the definitional equalities
`id a = a` and `(g ∘ f) a = g (f a)`.
-/

example : α → α := id

example (a : α) : id a = a := by
  rfl

example (f : α → β) (g : β → γ) : α → γ := g ∘ f

example (f : α → β) (g : β → γ) (a : α) : (g ∘ f) a = g (f a) := by
  rfl

/-
Given a type `α`, the type of all subsets of `α` is denoted by `Set α`.
Given a set `s : Set α` and a term `a : α`, the expression `a ∈ s` denotes
the proposition stating that `a` is an element of `s`. The notation for
writing down a specific set is `{a : α | P a}`.
-/

#check Set ℕ

example : Set ℕ := {n | 1 < n ∧ ¬ ∃ p q, 1 < p ∧ 1 < q ∧ n = p * q}

/-
There is lots of new notation for sets, but we will not need to learn any new
tactics as long as we can remember the following definitional equalities:
`s ⊆ t` is definitionally equal to `∀ a, a ∈ s → a ∈ t`.
`a ∈ s ∪ t` is definitionally equal to `a ∈ s ∨ a ∈ t`.
`a ∈ s ∩ t` is definitionally equal to `a ∈ s ∧ a ∈ t`.
`a ∈ ∅` is definitionally equal to `False`
`a ∈ Set.univ` is definitionally equal to `True`.
`a ∈ sᶜ` is definitionally equal to `a ∉ s` (notation for `¬ a ∈ s`).
`a ∈ f '' s` is definitionally equal to `∃ b, f b = a`.
`a ∈ f⁻¹' s` is definitionally equal to `f a ∈ s`.

To prove that two sets `s t : Set α` are equal, the tactic `ext a` will add an
arbitrary `a : α` as an assumption and replace the goal with `a ∈ s ↔ a ∈ t`.
-/

example (α : Type*) (s t : Set α) : s ∩ t ⊆ s ∪ t := by
  intro a ha
  rcases ha with ⟨has, hat⟩
  left
  exact has

/-
In pratice, when dealing with sets, many basic properties already exist as
theorems in mathlib. There are many different ways of finding these theorems.

Guess: Mathlib has developed a naming convention which assigns predictable names
to theorems. Once you get familiar with this convention, you can often guess
the name of the desired theorem directly or within a few tries. For example,
the triangle inequality `|a + b| ≤ |a| + |b|` is called `abs_add_le`.
-/

#check abs_add_le

/-
Tactics: Mathlib has a few tactics which help locate existing theorems.
One of these tactics is `simp` which is like `rw` but repeatedly applies
the specified theorems as well as any theorems in the library that have been
tagged with `@[simp]`. The `simp?` tactic allows you to see which theorems
were applied, and the `simp only` tactic allows you to specify exactly which
simplification theorems to use. A theorem should be tagged with `@[simp]`
when the right hand side is simpler than the left hand side. For example,
`add_zero` is tagged with `@[simp]` but `add_comm` is not.
-/

#check add_zero
#check add_comm

example (a : ℝ) : a * a - 1 = (a - 1) * (a + 1) := by
  simp [sub_mul, mul_add]

example (a : ℝ) : a * a - 1 = (a - 1) * (a + 1) := by
  simp? [sub_mul, mul_add]

example (a : ℝ) : a * a - 1 = (a - 1) * (a + 1) := by
  simp only [mul_add, sub_mul, one_mul, mul_one, sub_add_sub_cancel]

/-
Another tactic that can help locate existing theorems is `exact?`.
It tries to close the current goal by searching through all of mathlib.
Two common pitfalls here are not importing enough of mathlib, and slight
differences between your goal and how the theorem is stated in mathlib.
For example, mathlib contains `a * a - 1 = (a + 1) * (a - 1)` but not
`a * a - 1 = (a - 1) * (a + 1)`.
-/

example (a : ℝ) : a * a - 1 = (a + 1) * (a - 1) := by
  exact?

example (a : ℝ) : a * a - 1 = (a + 1) * (a - 1) := by
  exact mul_self_sub_one a

/-
Search: Finally, there are search tools which function as
a search engine for theorems and definitions in mathlib.
Some use AI (such as LeanSearch and LeanExplore) whereas
others perform more exact matching (such as Loogle).
-/

/-
## Examples for you to try

Manually prove these examples for yourself using basic tactics, but then
check if `simp?` or `exact?` finds any relevant lemmas in mathlib.
-/

section

variable (s t u v : Set α)

example : s ⊆ s := by
  sorry

example : s ⊆ t → t ⊆ u → s ⊆ u := by
  sorry

example : s ⊆ s ∪ t := by
  sorry

example : s ∩ t ⊆ s := by
  sorry

example : s ⊆ t → s ⊆ u → s ⊆ t ∩ u := by
  sorry

example : t ⊆ s → u ⊆ s → t ∪ u ⊆ s := by
  sorry

example : s ⊆ t → u ⊆ v → s ∪ u ⊆ t ∪ v := by
  sorry

example : s ⊆ t → u ⊆ v → s ∩ u ⊆ t ∩ v := by
  sorry

example : ∅ ⊆ s := by
  sorry

example : s ⊆ Set.univ := by
  sorry

example : s ⊆ t → t ⊆ s → s = t := by
  sorry

example : s ∪ s = s := by
  sorry

example : s ∩ s = s := by
  sorry

example : s ∪ ∅ = s := by
  sorry

example : s ∪ Set.univ = Set.univ := by
  sorry

example : s ∩ ∅ = ∅ := by
  sorry

example : s ∩ Set.univ = s := by
  sorry

example : s ∪ t = t ∪ s := by
  sorry

example : s ∩ t = t ∩ s := by
  sorry

example : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) := by
  sorry

example : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u := by
  sorry

example : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  sorry

example : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  sorry

end

section

variable (f : α → β) (g : β → γ) (s : Set α) (t : Set β) (u : Set γ)

example : s ⊆ f ⁻¹' (f '' s) := by
  sorry

example : f '' (f ⁻¹' t) ⊆ t := by
  sorry

example : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  sorry

example : id ⁻¹' s = s := by
  sorry

example : id '' s = s := by
  sorry

example : g ∘ f ⁻¹' u = f ⁻¹' (g ⁻¹' u) := by
  sorry

example : g ∘ f '' s = g '' (f '' s) := by
  sorry

end
