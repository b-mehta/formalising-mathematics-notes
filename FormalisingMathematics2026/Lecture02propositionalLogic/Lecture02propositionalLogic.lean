/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!
# Lecture 2: Propositional Logic
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section

variable (P Q R : Prop)

/-
In the previous lecture, we saw that the implication
"if `P` is true, then `Q` is true" is denoted by `P → Q` in Lean.

We can also express and, or, and not in Lean.
* "`P` and `Q` are both true" is denoted `P ∧ Q`.
* "`P` is true or `Q` is true" is denoted `P ∨ Q`.
* "`P` is not true" is denoted `¬ P`.

Lean also has `True` and `False` which denote the trivially true proposition
and the trivially false proposition.

Before getting on to tactics, we should first discuss associativity.
For implication, the propositions `P → (Q → R)` and `(P → Q) → R` are different.
The first says "if `P` is true, then if `Q` is also true, then `R` is true".
In other words, "if `P` and `Q` are both true, then `R` is true". The second
says, "if it is true that [if `P` is true, then `Q` is true], then `R` is true".
These are different statements. The first can be true while the second
remains false (although not the other way around).

The first version `P → (Q → R)` is the more natural of the two, so Lean has
decided that the implication arrow `→` is right-associative. This means that
Lean will interpret `P → Q → R` as meaning `P → (Q → R)`. This also means that
Lean will display `P → Q → R` in place of `P → (Q → R)`. This can be confusing
for beginners. For example, if you put your cursor just before the following
`sorry`, then the infoview will display `P → Q → R` instead of `P → (Q → R)`.
-/

example : P → (Q → R) := by
  sorry

/-
And (`∧`) and or (`∨`) are associative mathematically, but in Lean this
is a theorem that needs to be proved. This means that `P ∧ (Q ∧ R)` and
`(P ∧ Q) ∧ R` are treated as different by Lean. Lean has decided that `∧`
and `∨` are also right-associative like `→`, so `P ∧ Q ∧ R` is interpreted
as meaning `P ∧ (Q ∧ R)`, and `P ∧ (Q ∧ R)` displays as `P ∧ Q ∧ R`.

We can now discuss tactics. For each of the logical building blocks
(`→`, `∧`, `∨`, `¬`, `True`, `False`), we will need tactics that can work with
them when they appear as the goal or as a hypothesis.

We have already seen that `intro` works when the goal is of the form `P → Q`.
But we also need to be able to handle the situation where a hypothesis is of the
form `P → Q`. There are actually multiple different tactics that fit this
purpose. The first is `apply` which works when one of your hypotheses is an
implication whose conclusion matches the goal. For example, if your goal is `Q`
and you have a hypothesis `hPQ : P → Q`, then the tactic `apply hPQ` will
replace the goal with `P`.
-/

example (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP

/-
The second is `specialize` which works when one of your hypotheses is an
implication whose assumption matches another hypothesis. For example, if you
have hypotheses `hP : P` and `hPQ : P → Q`, then `specialize hPQ hP` will
replace the hypothesis `hPQ` with `Q`.
-/

example (hPQ : P → Q) (hP : P) : Q := by
  specialize hPQ hP
  exact hPQ

/-
One way of understanding the difference between `specialize` and `apply` is in
terms of forwards reasoning vs backwards reasoning. With `specialize`, you are
reasoning forward from the hypotheses you currently have. With `apply`, you are
reasoning backwards from the goal. Forwards reasoning is more common in regular
mathematics, but for Lean it is useful to be able to work with both.

Another pair of tactics that captures forwards reasoning vs backwards reasoning
is `have` and `suffices`. Both allow you to specify an intermediate goal. With
`have`, you first prove the intermediate goal, and then have it available to use
in the proof of the original goal. With `suffices`, you first prove the original
goal from the intermediate goal, and then prove the intermediate goal.
-/

example : Q := by
  have hP : P := by
    sorry
  sorry

example : Q := by
  suffices hP : P by
    sorry
  sorry

/-
When the goal is of the form `P ∨ Q`, you can choose between proving `P` and
proving `Q`. Once you know which side you want to prove, you can lock in your
decision with the tactics `left` and `right`. The tactic `left` will replace
the goal with `P`, and the tactic `right` will replace the goal with `Q`.
-/

example (hP : P) : P ∨ Q := by
  left
  exact hP

example (hQ : Q) : P ∨ Q := by
  right
  exact hQ

/-
When the goal is of the form `P ∧ Q`, you must prove both `P` and `Q`.
The tactic `constructor` will split `P` and `Q` into two separate goals.
Whenever you have multiple goals, each should be indented two spaces with `·`.
-/

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

/-
When a hypothesis is of the form `hPQ : P ∨ Q`, the tactic
`rcases hPQ with hP | hQ` will produce two goals, one where the hypothesis `hPQ`
is replaced by `hP : P` and another where `hPQ` is replaced by `hQ : Q`.
-/

example (hPQ : P ∨ Q) (h : P → Q) : Q := by
  rcases hPQ with hP | hQ
  · apply h
    exact hP
  · exact hQ

/-
When a hypothesis is of the form `hPQ : P ∧ Q`, the tactic
`rcases hPQ with ⟨hP, hQ⟩` will replace `hPQ` with the hypotheses `hP : P` and
`hQ : Q`. Remember this angle bracket syntax, since it will show up quite a bit.
-/

example (hPQ : P ∧ Q) : P := by
  rcases hPQ with ⟨hP, hQ⟩
  exact hP

example (hPQ : P ∧ Q) : Q := by
  rcases hPQ with ⟨hP, hQ⟩
  exact hQ

/-
Finally, we now turn to `True`, `False`, and `¬`. You will not see `True` very
often. It is the trivially true proposition. Indeed, the fact that `True`
is true is called `trivial`. Thus, a hypothesis `h : True` contributes nothing
and can be safely ignored since you already have `trivial : True`. And if `True`
appears as the goal then `exact trivial` will immediately close the goal.
-/

example : True := by
  exact trivial

/-
Likewise, `False` is the trivially false proposition. You can think of it as
denoting a contradiction. It arises most commonly in a proof by contradiction.
If your goal is `P`, then the tactic `by_contra hP` will replace the goal with
`False` and will add `hP : ¬ P` as a hypothesis. In other words, it allows you
to assume that `P` is false in order to derive a contradiction.
-/

example (h : False) : P := by
  by_contra hP
  exact h

/-
The above example demonstrates that `False` can prove every other proposition.
This is known in logic as the principle of explosion.

Finally, the negation `¬ P` is actually defined as `P → False`. This means that
you can treat it like an implication and use `intro`, `apply`, and `specialize`.
-/

example (hP : P) (hnP : ¬ P) : False := by
  apply hnP
  exact hP

example (hP : P) (hnP : ¬ P) : False := by
  specialize hnP hP
  exact hnP

/-
One last tactic that you may find helpful is `by_cases`.
The tactic `by_cases hP : P` will produce two goals, one where you have the
hypothesis `hP : P` and another where you have the hypothesis `hP : ¬ P`.
-/

example : P ∨ ¬ P := by
  by_cases hP : P
  · left
    exact hP
  · right
    exact hP

/-
## Examples for you to try

Delete the `sorry`s and replace them with tactic proofs using the tactics
learned so far (`exact`, `intro`, `apply`, `specialize`, `have`, `suffices`,
`left`, `right`, `constructor`, `rcases`, `by_contra`, `by_cases`).
-/

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
This is called "modus ponens" by logicians. -/
example : P → (P → Q) → Q := by
  sorry

/-- `→` is transitive. -/
example : (P → Q) → (Q → R) → P → R := by
  sorry

/-- If `h : P → Q → R` with goal `⊢ R`, then `apply h` will give two goals! -/
example : (P → Q → R) → (P → Q) → P → R := by
  sorry

/-- `∨` is symmetric. -/
example : P ∨ Q → Q ∨ P := by
  sorry

/-- `∧` is symmetric. -/
example : P ∧ Q → Q ∧ P := by
  sorry

/-- `∧` is transitive. -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  sorry

example : P ∨ Q → (P → R) → (Q → R) → R := by
  sorry

example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry

example : P → True := by
  sorry

example : False → P := by
  sorry

example : ¬ True → P := by
  sorry

example : P → ¬ False := by
  sorry

example : ¬ P → P → Q := by
  sorry

/-- If we know `P → Q`, and we also know `¬ Q`, we can deduce `¬ P`.
This is called "modus tollens" by logicians. -/
example : (P → Q) → ¬ Q → ¬ P := by
  sorry

example : (¬ Q → ¬ P) → P → Q := by
  sorry

example : (P → Q) → ((P → Q) → P) → Q := by
  sorry

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  sorry

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  sorry
