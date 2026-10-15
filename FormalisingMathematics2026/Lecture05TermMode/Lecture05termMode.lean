/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!
# Lecture 4: Equality
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section

/-
In lecture 2 we distinguished between forward reasoning tactics
(reasoning forward from the hypotheses you currently have),
and backwards reasoning tactics (reasoning backwards from the goal).

There is actually a tactic called `refine` that can replace all of the
backwards reasoning tactics that we have learned so far. For example:

* `exact h` can be replaced by `refine h`
* `intro h` can be replaced by `refine fun h ↦ ?_`
* `apply h` can be replaced by `refine h ?_`
* `left` can be replaced by `refine Or.inl ?_`
* `right` can be replaced by `refine Or.inr ?_`
* `constructor` can be replaced by `refine ⟨?_, ?_⟩`
* `use a` can be replaced by `refine ⟨a, ?_⟩`
* `rfl` can be replaced by `refine rfl`

We can illustrate this replacement with the following example.
-/

theorem mythm (P Q : Prop) (h : P → Q) : ¬ Q → ¬ P := by
  intro hnQ
  intro hP
  apply hnQ
  apply h
  exact hP

example (P Q : Prop) (h : P → Q) : ¬ Q → ¬ P := by
  refine fun hnQ ↦ ?_
  refine fun hP ↦ ?_
  refine hnQ ?_
  refine h ?_
  refine hP

/-
The idea behind this replacement is that ultimately a proof in Lean consists of
a "proof term". In general, tactics are commands that instruct Lean how to build
the proof term. The `#print` command allows you to see the resulting proof term.
-/

#print mythm

/-
The `refine` tactic allows you to provide a partial proof term with
"holes" denoted by `?_` that are filled in by subsequent goals.

For example, the last two lines above generate the proof term `h hP` since the
hole in `h ?_` is filled in by the complete proof term `hP`. In general, we can
combine consecutive `refine` tactics by replacing holes in the first `refine`
tactic by the partial proof term specified by the following `refine` tactics.
-/

example (P Q : Prop) (h : P → Q) : ¬ Q → ¬ P := by
  refine fun hnQ ↦ fun hP ↦ hnQ (h hP)

/-
Now that there are no holes remaining, we can replace `refine` with `exact`.
In general, a `refine` tactic with no holes is the same as an `exact`.

We can also combine the two `fun` commands into a single `fun` command in the
same way that we can combine two `intro` tactics into a single `intro` tactic.
-/

example (P Q : Prop) (h : P → Q) : ¬ Q → ¬ P := by
  exact fun hnQ hP ↦ hnQ (h hP)

/-
We can even clean this up further with a better understanding of the syntax:
* The `:=` means that we are about to provide the proof term.
* The `by` means that we are going to build the proof term with tactics.
* The `exact` means that we are going to provide the proof term directly.

In other words, `by` switches from term-mode to tactic-mode, and `exact`
switches back from tactic-mode to term-mode. So the combination `by exact`
does nothing and can be safely removed.
-/

example (P Q : Prop) (h : P → Q) : ¬ Q → ¬ P :=
  fun hnQ hP ↦ hnQ (h hP)

/-
And in fact, notice how this now basically matches the output of `#print mythm`.
-/

#print mythm

/-
Lastly, we will try to expain some of the syntax appearing in the=
"refine dictionary".

Recall that every proposition is a type whose terms are its proofs. For example,
this means that a term of `P ∧ Q` consists of a pair of a term of `P` and
a term of `Q`. In Lean, these are packaged together with the angle bracket
syntax `⟨_, _⟩`. This is why `constructor` is equivalent to `refine ⟨?_, ?_⟩`.

Likewise, a term of `∃ a : α, P a` consists of a pair of a term `a : α` and
a term of `P a`. This is why `use a` is equivalent to `refine ⟨a, ?_⟩`.

A term of `P → Q` consists of a function from `P` to `Q` (i.e., given a proof
of `P`, produce a proof of `Q`). Functions are denoted by `fun h ↦ ...`, so this
is why `intro h` is equivalent to `refine fun h ↦ ?_`.

Likewise, a term of `∀ a : α, P a` consists of a function mapping each `a : α`
to a term of `P a`. This is why `intro a` is equivalent to `refine fun a ↦ ?_`.

For `apply h`, we have a function `h : P → Q` from `P` to `Q`. If we had a
term `hP` of `P`, then plugging `hP` into `h` would give a term `h hP` of `Q`
(without parentheses). This is why `apply h` is equivalent to `refine h ?_`.

For the tactics `left` and `right`, there are functions `Or.inl : P → P ∨ Q` and
`Or.inr : Q → P ∨ Q` which can be applied to produce a term of `P ∨ Q` from a
term of `P` or a term of `Q`. Thus, `left` is equivalent to `refine Or.inl ?_`
and `right` is equivalent to `refine Or.inr ?_`.
-/

#check Or.inl
#check Or.inr

/-
## Examples for you to try

Use the "refine dictionary" to produce term-mode proofs of the following propositions.
-/

variable (P Q R : Prop)

example : P → (P → Q) → Q :=
  sorry

example : (P → Q) → (Q → R) → P → R :=
  sorry

example : (P → Q → R) → (P → Q) → P → R :=
  sorry

example : (P → Q) → ((P → Q) → P) → Q :=
  sorry

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P :=
  sorry

example : ((Q → P) → P) → (Q → R) → (R → P) → P :=
  sorry

example (α : Type*) (P : α → Prop) (h : ¬ ∃ a : α, P a) : ∀ a : α, ¬ P a := by
  sorry
