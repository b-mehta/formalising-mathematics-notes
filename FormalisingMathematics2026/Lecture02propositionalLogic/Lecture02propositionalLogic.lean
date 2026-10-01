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
set_option linter.unusedVariables false

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
Implication (`→`) is not associative. The propositions `P → (Q → R)` and
`(P → Q) → R` are genuinely different. The first says "if `P` is true,
then if `Q` is also true, then `R` is true". In other words,
"if `P` and `Q` are both true, then `R` is true". The second says,
"if it is true that [if `P` is true, then `Q` is true], then `R` is true".
These are different statements. The first can be true while the second
remains false (but not the other way around).

The first version `P → (Q → R)` is more natural, so Lean has decided that
the implication arrow `→` is right-associative. This means that Lean will
interpret `P → Q → R` as meaning `P → (Q → R)`. It also means that Lean will
display `P → Q → R` in place of `P → (Q → R)`. This can be confusing for
beginners. For example, if you put your cursor just before the following
`sorry`, then the infoview will display `P → Q → R` instead of `P → (Q → R)`.
-/

example : P → (Q → R) := by
  sorry

/-
And (`∧`) and or (`∨`) are associative mathematically, but in Lean this is
a theorem that needs to be proved. This means that `P ∧ (Q ∧ R)` and
`(P ∧ Q) ∧ R` are not the same. Lean has decided that `∧` and `∨` are also
right-associative, like implication, so `P ∧ Q ∧ R` will be interpreted as
`P ∧ (Q ∧ R)` which will display as `P ∧ Q ∧ R`.

We can now discuss tactics. For each of the logical building blocks
(`→`, `∧`, `∨`, `¬`, `True`, `False`), we will need tactics that can work with
them when they are the goal or a hypothesis.

We have already seen that `intro` works when the goal is of the form `P → Q`.
But we also need to able to handle the situation where a hypothesis is of the
form `P → Q`. There are actually multiple different tactics that fit this
purpose. The first is `apply` which works when one of your assumptions is an
implication whose conclusion matches the goal. If your goal is `Q` and you have
a hypothesis `hPQ : P → Q`, then the tactic `apply hPQ` will replace the goal
with `P`.
-/

example (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP

/-
The second is `specialize` which works when one of your assumptions is an
implication whose assumption matches another hypothesis. If you have hypotheses
`hP : P` and `hPQ : P → Q`, then `specialize hPQ hP` will replace `hPQ` with
`Q`.
-/

example (hPQ : P → Q) (hP : P) : Q := by
  specialize hPQ hP
  exact hPQ

/-
The difference between `specialize` and `apply` is in forwards reasoning vs
backwards reasoning. With `specialize`, you are reasoning forward from the
hypotheses you current have. With `apply`, you are reasoning backwards from
the goal. Forwards reasoning is more common in regular mathematics, but for
Lean it is useful to be able to work with both.

Another pair of tactics for forwards reasoning and backwards reasoning is
`have` and `suffices`. Both allow you to specify an intermediate goal.
With `have`, you first prove the intermediate goal, and then have it available
in the remaining proof of the original goal. With `suffices`, you first prove
the original goal from the intermediate goal, and then prove the intermediate
goal.
-/

example (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  have hQ : Q := by
    specialize hPQ hP
    exact hPQ
  specialize hQR hQ
  exact hQR

example (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  suffices hQ : Q by
    apply hQR
    exact hQ
  apply hPQ
  exact hP

/-
For `∨` in the goal, the relevant tactics are `left` and `right`.
-/

/-
For `∧` in the goal, the relevant tactic is `constructor`.
-/

/-
For `∨` in a hypothesis, the relevant tactic is `rcases`.
-/

/-
For `∧` in a hypothesis, the relevant tactic is again `rcases`, but this time
with different syntax. Remember this angle bracket syntax, since it will show
up quite a bit.
-/

/-
For `True`, the only relevant tactic is `trivial`.

For `False`, the relevant tactics are `by_contra` and `exfalso`.
-/

/-
Technically `¬ P` is implemented as `P → False`, but one extra tactic you
might find useful is `by_cases P` which splits into two cases.
-/















/-

## Examples for you to try

Delete the `sorry`s and replace them with tactic proofs using `intro`,
`exact` and `apply`, separating them with newlines or semicolons (`;`).

-/

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
This is called "Modus Ponens" by logicians. -/
example : P → (P → Q) → Q := by
  sorry

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
so is `P → R`. -/
example : (P → Q) → (Q → R) → P → R := by
  sorry

/-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
two goals! Note that tactics operate on only the first goal. -/
example : (P → Q → R) → (P → Q) → P → R := by
  sorry

/-
Here are some harder puzzles. They won't teach you anything new about
Lean, they're just trickier. If you're not into logic puzzles
and you feel like you understand `intro`, `exact` and `apply`
then you can just skip these and move onto the next sheet
in this section, where you'll learn some more tactics.
-/
variable (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  sorry

example : (P → Q) → ((P → Q) → P) → Q := by
  sorry

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  sorry

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  sorry

example : (((P → Q) → Q) → Q) → P → Q := by
  sorry

example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  sorry
