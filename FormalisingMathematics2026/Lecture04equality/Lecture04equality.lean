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
Given two terms `a b : α` of the same type `α`, the expression `a = b`
denotes the proposition stating that `a` and `b` are equal.

There are two relevant tactics here. The first is `rfl` which will close the
goal when the two sides are definitionally equal. Roughly speaking, definitional
equality means that the two sides match after unfolding all of the definitions.
-/

example : 37 = 37 := by
  rfl

/-
In the following example, even though `x` and `y` are defined separately,
they have the same definition, so `rfl` can still prove equality.
-/

def x : ℝ := 37
def y : ℝ := 37

example : x = y := by
  rfl

/-
As another example, `¬ P` is definitionally equal to `P → False`.
-/

example (P : Prop) : (¬ P) = (P → False) := by
  rfl

/-
The parentheses above are necessary because `=` has higher "precedence"
(binds more tightly) than logical operators like `¬` and `→`.

Without parentheses, the expression `¬ P = P → False` is interpreted as
meaning `(¬ (P = P)) → False`.
-/

example (P : Prop) : ¬ P = P → False := by
  intro h
  apply h
  rfl

/-
The other tactic that is useful for working with equalities is `rw`.
Given a proof `h_eq : a = b` of equality between `a` and `b`, the
tactic `rw [h]` will replace all occurances of `a` in the goal with `b`.
There is also the variant `rw [h_eq] at h` which will rewrite all
occurances of `a` in the hypothesis `h` with `b`, and the backwards
variant `rw [← h]` which will replace all occurances of `b` with `a`.
-/

example (α : Type*) (a b c : α) (hab : a = b) (hbc : b = c) : a = c := by
  rw [hab, hbc]

example (α : Type*) (a b : α) (h : a = b) : b = a := by
  rw [h]

/-
The tactic `rw` requires syntactic equality, not just definitional equality.
Roughly speaking, syntactic equality means that the two sides match as written.
-/

example (z : ℝ) (h : y = z) : z = y ∧ x = y := by
  rw [h]
  constructor
  · rfl
  · exact h

/-
In this example, `rw [h]` only rewrites the occurances of `y` and not
the occurances of `x` since `x` and `y` are only definitionally equal,
not syntactically equal. But `exact h` is able to prove `x = y` since
the `exact` tactic only requires definitional equality.

In practice, it is common to rewrite with lemmas from mathlib rather than
local hypotheses. For example, commutativity of addition is called `add_comm`,
and distributivity of multiplication over addition is called `mul_add`.
-/

#check add_comm
#check mul_add

example (a b c d : ℕ) : (a + b) * (c + d) = (b + a) * c + (a + b) * d := by
  rw [add_comm, mul_add]

/-
In this example, if you place your cursor after the comma, you can see that
the lemma `add_comm` was applied to both occurances of `a + b`, but not to
any of the other occurances of addition. The reason for this is that the tactic
`add_comm` initially has a few undetermined variables. The `rw` tactic looks
for the first place where `add_comm` could be applied, then determines the
values of these variables, and only then replaces all occurances.

In the following example, `rw [add_comm]` does not work, but you can specify
the undetermined variables by directly plugging them in to `add_comm`.
-/

example (a b c : ℕ) : a + b + c = b + a + c := by
  rw [add_comm a b]

/-
There is one more logical connective: "if and only if", denoted `P ↔ Q`.
We have saved it until now because it behaves similarly to equality.
In particular, the tactics `rfl` and `rw` work on `↔` in the same way as `=`.
-/

example (P : Prop) : P ↔ P := by
  rfl

example (P Q R : Prop) (hPQ : P ↔ Q) (hQR : Q ↔ R) : P ↔ R := by
  rw [hPQ, hQR]

example (P Q : Prop) (hPQ : P ↔ Q) : Q ↔ P := by
  rw [hPQ]

/-
While not definitionally equal to `P → Q ∧ Q → P`, the operator `P ↔ Q` behaves
similarly in the sense that `constructor` can be used to split into two goals
`P → Q` and `Q → P`. In theory, `rcases` can also be used to break apart a
hypothesis that is an `iff`, but this is rarely done in practice.
-/

example (P Q : Prop) (hPQ : P ↔ Q) : Q ↔ P := by
  rcases hPQ with ⟨hPQ, hQP⟩
  constructor
  · exact hQP
  · exact hPQ

/-
## Examples for you to try

We now have enough to build up the basic theory of the natural numbers.
This will require some boilerplate that we will learn to understand later.
-/

inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

namespace MyNat

def add (a : MyNat) : MyNat → MyNat
  | zero => a
  | succ b => succ (add a b)

instance : Add MyNat where
  add := add

def mul (a : MyNat) : MyNat → MyNat
  | zero => zero
  | succ b => mul a b + a

instance : Mul MyNat where
  mul := mul

/-
This boilerplate defines a custom copy `MyNat` of the natural numbers
as well as custom addition and multiplication operations such that the
most basic properties are all provable as definitional equalities.
-/

theorem add_zero (a : MyNat) : a + zero = a := by
  rfl

theorem add_succ (a b : MyNat) : a + succ b = succ (a + b) := by
  rfl

theorem mul_zero (a : MyNat) : a * zero = zero := by
  rfl

theorem mul_succ (a b : MyNat) : a * succ b = a * b + a := by
  rfl

/-
We can now start to prove theorems. This particular sequence of theorems
is taken from *The Natural Number Game* and is progressive in the sense
that earlier theorems will be helpful in proving later theorems.

Most of these will require the `induction` tactic for proof by induction.
The first theorem is proved for you to help you learn the syntax.
-/

theorem zero_add (a : MyNat) : zero + a = a := by
  induction a with
  | zero =>
    rw [add_zero]
  | succ n h =>
    rw [add_succ, h]

theorem succ_add (a b : MyNat) : succ a + b = succ (a + b) := by
  sorry

theorem add_comm (a b : MyNat) : a + b = b + a := by
  sorry

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  sorry

theorem zero_mul (a : MyNat) : zero * a = zero := by
  sorry

theorem succ_mul (a b : MyNat) : succ a * b = a * b + b := by
  sorry

theorem mul_comm (a b : MyNat) : a * b = b * a := by
  sorry

theorem mul_add (a b c : MyNat) : a * (b + c) = a * b + a * c := by
  sorry

theorem add_mul (a b c : MyNat) : (a + b) * c = a * c + b * c := by
  sorry

theorem mul_assoc (a b c : MyNat) : a * b * c = a * (b * c) := by
  sorry

theorem mul_one (a : MyNat) : a * succ zero = a := by
  sorry

theorem one_mul (a : MyNat) : succ zero * a = a := by
  sorry

end MyNat
