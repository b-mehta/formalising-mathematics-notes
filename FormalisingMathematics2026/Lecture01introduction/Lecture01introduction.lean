/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Tactic -- imports all of the tactics in mathlib

/-!
# Lecture 1: Introduction
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option pp.parens true

@[expose] public section

/-
A *proposition* is a true-false statement, like `2 + 2 = 4` or `2 + 2 = 5` or
the Riemann hypothesis. In algebra we manipulate numbers whilst not knowing
what the numbers actually are; the trick is that we give the numbers names like
`x` and `y`. In this lecture we will manipulate propositions without saying what
the propositions are by giving them names like `P` and `Q`.

Here is one of the most basic theorems you can write down in Lean.
It says that if a proposition `P` is true, then `P` is true.
-/

example (P : Prop) (h : P) : P := by
  sorry

/-
Before continuing, let's break down the syntax here:
* `example` tells Lean that we are about to state and prove a theorem. We must
  first provide the statement of the theorem, consisting of the hypotheses
  followed by the conclusion, and then we can start writing the proof.
* `(P : Prop)` means that `P` is a true-false statement.
* `(h : P)` is the assumption that `P` is true.
* The next colon marks the transition from the hypotheses to the conclusion,
  so the `: P` means that the conclusion of the theorem is that `P` is true.
* The `:= by` marks the transition from the statement of the theorem
  (the hypotheses and the conclusion) to the proof of the theorem.
  The proof of the theorem will consist of "tactics", each on its own line
  indented by two spaces. A tactic is just a command that tells Lean
  how to make progress on the proof.
* `sorry` is a special tactic which aborts an incomplete proof. Without the
  `sorry`, Lean gives an error indicating that the proof is incomplete. With the
  `sorry`, Lean only gives a warning informing you that the proof uses `sorry`.

When writing proofs on paper, you must constantly keep track of what your
current assumptions are and what your current goal is. Every step of the proof
will update your assumptions and goal, and you have to keep track of these
changes in your head. Lean has an infoview which keeps track of this information
for you automatically. For example, if you put your cursor just before the
`sorry`, then the infoview will display the following information:
```
P : Prop
h : P
⊢ P
```
The `⊢` symbol indicates the goal which here is to prove that `P` is true.
The current assumptions are listed above the goal. Here, `P : Prop` means that
`P` is a true-false statement, and `h : P` is the hypothesis that `P` is true.
So right now at the start of the proof, this is just a repackaging of the
theorem statement. But in middle of a long proof, this information will be
extremely helpful.

We are now ready for our first tactic (besides `sorry`).
The `exact` tactic allows you to say "the goal is exactly this".
In our case, the goal is to prove that `P` is true, and the fact that
`P` is true is exactly our hypothesis `h`. So `exact h` will close the goal.

This is an overly simplistic explanation of the `exact` tactic, but will be
sufficient for our current purposes. A more complete explanation will have to
wait for our discussion of type theory in lecture 5.
-/

example (P : Prop) (h : P) : P := by
  exact h

/-
Now if you put your cursor after the proof, there is no infoview.
Instead, it says "no goals", indicating that the theorem is proved.

Note that `exact P` does *not* work. `P` is the name of the proposition,
but the goal is exactly the hypothesis `h` that `P` is true.

Rather than having to write `(P : Prop)` on every subsequent example,
we can use the `variable` command to declare variables that can be
referred to in all subsequent examples.
-/

variable (P Q R : Prop)

/-
Here is another example.
It says that if propositions `P`, `Q`, and `R` are all true, then `P` is true.
-/

example (hP : P) (hQ : Q) (hR : R) : P := by
  exact hP

/-
Note that `hP`, `hQ`, and `hR` are just names. They can be anything you want.
-/

example (fish : P) (giraffe : Q) (dodecahedron : R) : P := by
  exact fish

/-
However, if you try to give them all the same name,
then you can only refer to the most recent one.
-/

example (h : P) (h : Q) (h : R) : R := by
  exact h

/-
Given two propositions `P` and `Q`, the expression `P → Q` denotes the
implication "if `P` is true, then `Q` is true". Mathematicians usually
write the implication arrow as `P ⇒ Q`, but Lean prefers a single arrow
for reasons that we will discuss in lecture 5.

When the goal is of the form `P → Q`, the `intro` tactic will introduce
`P` as a hypothesis and reduce the goal to `Q`. So after the `intro`
tactic, you are now reduced to showing that if `P` is true (as a hypothesis),
then `Q` is true (the new goal).

Here are few examples of how to use `intro` with `exact`.
-/

example : P → P := by
  intro h
  exact h

example (hQ : Q) : P → Q := by
  intro hP
  exact hQ

example : P → (Q → P) := by
  intro hP
  intro hQ
  exact hP

/-
In this last example, Lean helpfully notifies us that `intro hP hQ` also works.
-/

example : P → (Q → P) := by
  intro hP hQ
  exact hP
