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

There is also `True` and `False` which denote the trivially
true proposition and the trivially false proposition.

At this point we should probably say something about associativity.
Implication (`→`) is not associative. The propositions `P → (Q → R)` and
`(P → Q) → R` are genuinely different. The first says "if `P` is true,
then if `Q` is also true, then `R` is true". In other words,
"if `P` and `Q` are both true, then `R` is true". The second says,
"if it is true that [if `P` is true, then `Q` is true], then `R` is true".
These are different statements. The first can be true while the second
remains false (but not the other way around, curiously enough).

The first version `P → (Q → R)` is more natural, so Lean has decided that
the implication arrow `→` is right-associative. This means that Lean will
interpret `P → Q → R` as meaning `P → (Q → R)`. It also means that Lean will
display `P → Q → R` in place of `P → (Q → R)`. This can be confusing for
beginners. For example, if you put your cursor just before the `sorry`,
then the infoview will display `P → Q → R` instead of `P → (Q → R)`.
-/

example : P → (Q → R) := by
  sorry

/-
And (`∧`) and or (`∨`) are associative mathematically, but this is a theorem,
not automatic in Lean.
`P ∧ (Q ∧ R)` and `(P ∧ Q) ∧ R` are not the same.
Lean has decided that `∧` and `∨` are also right-associative, like implication.
-/

/-





For each of these expressions, we will need tactics that can
deal with them when the show up in the goal and when the show
up as hypotheses.

We have already seen that `intro` works when the goal is
of the form `P → Q`. But we also need to able to handle
the situation where a hypothesis is of the form `P → Q`.
There are actually multiple different tactics that fit this
purpose. The first is `apply` which works when the
hypothesis is of the form `h : P → Q` and the goal is exactly `Q`.
In this situation, `apply h` will replace the goal with `P`.
-/

example (hPQ : P → Q) (hP : P) : Q := by
  apply hPQ
  exact hP

/-

-/

example (hPQ : P → Q) (hP : P) : Q := by
  specialize hPQ hP
  exact hPQ

/-
Use `apply` vs `specialize` to talk about backwards vs forward reasoning
and `have` (`suffices`).
-/













/-
A *proposition* is a true-false statement, like `2 + 2 = 4` or `2 + 2 = 5`
or the Riemann hypothesis. In algebra we manipulate numbers whilst not
knowing what the numbers actually are; the trick is that we call the numbers
`x` and `y` and so on. In this lecture we will manipulate propositions without
saying what the propositions are -- we'll just call them things like `P` and `Q`.

Here is one of the most basic theorems you can write down in Lean.
It says that if a proposition `P` is true, then `P` is true.
-/

example (P : Prop) (h : P) : P := by
  sorry

/-
Before continuing, let's break down the syntax here:
* `example` tells Lean that we are about to state and prove a theorem.
  We must first provide the statement of the theorem, consisting of the
  hypotheses followed by the conclusion, and then we can start writing the proof.
* `(P : Prop)` means that `P` is a true-false statement.
* `(h : P)` is the assumption that `P` is true.
* The next colon marks the transition from the hypotheses to the conclusion,
  so `: P` means that the conclusion of the theorem is that `P` is true.
* The `:= by` marks the transition from the statement of the theorem
  (the hypotheses and the conclusion) to the proof of the theorem.
  The proof of the theorem will consist of "tactics", each on its own line
  indented by two spaces. A tactic is just a command that tells Lean
  how to make progress on the proof.
* `sorry` is a special tactic which finishes an incomplete proof.
  Without the `sorry`, there will be an error indicating that the proof is incomplete.
  With the `sorry`, there is only a warning informing you that the proof uses sorry.
-/

/-
When writing proofs on paper, you must constantly keep track of what your current
assumptions are and what your current goal is. Every step of the proof will update
your assumptions and goal, and you have to keep track of these changes in your head.

Lean has an infoview which keeps track of this information for you automatically.

For example, if you put your cursor just before the `sorry`, then the infoview
will display the following information:
```
P : Prop
h : P
⊢ P
```
The `⊢` symbol indicates the current goal which here is to prove that `P` is true.
The current assumptions are listed above the goal. Here, `P : Prop` means that `P`
is a true-false statement, and `h : P` is the hypothesis that `P` is true.
So right now, this is just a repackaging of the theorem statement.
But in middle of a long proof, this information will be extremely helpful.
-/

/-
We are now ready for our first tactic (besides `sorry`).
The `exact` tactic allows you to say "the goal is exactly this".
In our case, the goal is to prove that `P` is true, and the fact that
`P` is true is exactly our hypothesis `h`. So `exact h` will close the goal.

This is an oversimplification of the `exact` tactic.
A more in-depth explanation will have to wait for our discussion of type theory in lecture 5.
-/

example (P : Prop) (h : P) : P := by
  exact h

/-
Now if you put your cursor after the proof, there is no infoview.
Instead, it says "no goals", indicating that the theorem is proved.
-/

/-
Note that `exact P` does *not* work. `P` is the name of the proposition,
but the goal is exactly the hypothesis `h` that `P` is true.
-/

/-
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
However, if you try to give them all the same name, then `h`
will refer only to the most recent one.
-/

example (h : P) (h : Q) (h : R) : P := by
  exact h

example (h : R) (h : Q) (h : P) : P := by
  exact h

/-
Given two propositions `P` and `Q`, the expression `P → Q` denotes the
implication "if `P` is true, then `Q` is true". Mathematicians usually
write the implication arrow as `P ⇒ Q`, but Lean prefers a single arrow
for reasons that we will discuss in lecture 5.
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
Lean helpfully gives a warning saying that `intro hP hQ` works.
-/

example : P → (Q → P) := by
  intro hP hQ
  exact hP



/-!

# Lecture 1: Introduction



# Logic in Lean, example sheet 1 : "implies" (`→`)

The purpose of these first few sheets is to teach you some very basic
*tactics*. In particular we will learn how to manipulate statements
such as "P implies Q", which is itself a true-false statement (e.g.
it is false when P is true and Q is false). In Lean we use the
notation `P → Q` for "P implies Q". You can get
this arrow by typing `\to` or `\r`. Mathematicians usually write the
implication arrow as `P ⇒ Q` but Lean prefers a single arrow.

## The absolute basics

`P : Prop` means that `P` is a true-false statement. `h : P` means
that `h` is a proof that `P` is true. You can also regard `h` as the
hypothesis that `P` is true; logically these are the same. Stuff above
the `⊢` symbol is your assumptions. The statement to the right of it is
the goal. Your job is to prove the goal from the assumptions.

## Tactics you will need

To solve the levels on this sheet you will need to know how to use the
following three tactics:

* `intro`
* `exact`
* `apply`

You can read the descriptions of these tactics in Part 2 of the online course
notes here https://b-mehta.github.io/formalising-mathematics-notes/
In this course we'll be learning about 30 tactics in total; the goal of this
first logic section is to get you up to speed with ten very basic ones.

## Worked examples

Click around in the proofs to see the tactic state (on the right) change.
The tactic is implemented and the state changes just before the newline or semicolon (`;`).
I will use the following conventions: variables with capital
letters like `P`, `Q`, `R` denote propositions
(i.e. true/false statements) and variables whose names begin
with `h` like `h1` or `hP` are proofs or hypotheses.

-/



-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

-- Here are some examples of `intro`, `exact` and `apply` being used.
-- Assume that `P` and `Q` and `R` are all true. Deduce that `P` is true.
example (hP : P) (hQ : Q) (hR : R) : P := by
  -- note that `exact P` does *not* work. `P` is the proposition, `hP` is the proof.
  exact hP

-- Same example: assume that `P` and `Q` and `R` are true, but this time
-- give the assumptions silly names. Deduce that `P` is true.
example (fish : P) (giraffe : Q) (dodecahedron : R) : P := by
-- `fish` is the name of the assumption that `P` is true (but `hP` is a better name)
  exact fish

-- Assume `Q` is true. Prove that `P → Q`.
example (hQ : Q) : P → Q := by
  -- The goal is of the form `X → Y` so we can use `intro`
  intro (fish : P)
  -- now `h` is the hypothesis that `P` is true.
  -- Our goal is now the same as a hypothesis so we can use `exact`
  exact hQ
  -- note `exact Q` doesn't work: `exact` takes the *term*, not the type.

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q := by
  -- `hP` says that `P` is true, and `h` says that `P` implies `Q`, so `apply h at hP` will change
  -- `hP` to a proof of `Q`.
  apply h at hP
  -- now `hP` is a proof of `Q` so that's exactly what we want.
  exact hP

-- The `apply` tactic always needs a hypothesis of the form `P → Q`. But instead of applying
-- it to a hypothesis `h : P` (which changes the hypothesis to a proof of `Q`), you can instead
-- just use a bare `apply h` and it will apply it to the *goal*, changing it from `Q` to `P`.
-- Here we are "arguing backwards" -- if we know that P implies Q, then to prove Q it suffices to
-- prove P.

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q := by
  -- `h` says that `P` implies `Q`, so to prove `Q` (our goal) it suffices to prove `P`.
  apply h
  -- Our goal is now `⊢ P`.
  exact hP

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`. If you think
about it, this means that to deduce `R` you will need to prove both `P`
and `Q`. In general to prove `P1 → P2 → P3 → ... Pn` you can assume
`P1`, `P2`,...,`P(n-1)` and then you have to prove `Pn`.

So the next level is asking you to prove that `P → (Q → P)`.

-/
example : P → Q → P := by
  intro hP hQ
  -- the `assumption` tactic will close a goal if
  -- it's exactly equal to one of the hypotheses.
  assumption

/-

## Examples for you to try

Delete the `sorry`s and replace them with tactic proofs using `intro`,
`exact` and `apply`, separating them with newlines or semicolons (`;`).

-/
/-- Every proposition implies itself. -/
example : P → P := by
  intro h
  exact h

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
