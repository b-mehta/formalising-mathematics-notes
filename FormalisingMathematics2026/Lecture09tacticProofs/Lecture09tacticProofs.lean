/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!
# Lecture 9: Tactic Proofs
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section


/-
When writing longer tactic proofs, it will be important to be aware of
mathlib's powerful tactics and to know how to deploy them effectively.

* `simp` repeatedly simplifies with any imported theorems that have been
  tagged with `@[simp]` as well as any results provided in square brackets.
  Variants include `simp only` which only uses the results provided in the
  square brackets, `simpa` which will close the resulting goal by finding
  a matching assumption, and `simpa using h` which will simplify both `h`
  and the goal and then close the goal with `exact h`.
* `ring` can prove equations in commutative rings.
-/

example (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-
* `norm_num` can prove numerical goals by normalizing numerical expressions.
* `fun_prop` proves function properties like continuity and differentiability.
-/

example : ∃ x ∈ Set.Icc (1.3 : ℝ) (1.4 : ℝ), x ^ 3 - x - 1 = 0 := by
  apply intermediate_value_Icc
  · norm_num
  · fun_prop
  · norm_num

/-
The next pair of tactics deals with coercions. A coercion is a function that
has been registered as an instance so that Lean can apply it automatically.

* `push_cast` pushes coercions inward.
-/

example (x : ℕ) (y : ℤ) : (x - y : ℤ) = (x - y : ℝ) := by
  push_cast
  rfl

/-
* `norm_cast` pulls coercions outward.
-/

example (x : ℕ) (y : ℤ) (h : (x : ℝ) < (y : ℝ)) : (x : ℝ) ≤ (y : ℝ) - 1 := by
  norm_cast at h ⊢
  simpa

/-
* `positivity` proves goals of the form `0 ≤ x`, `0 < x`, and `x ≠ 0`.
  It work algorithmically, combining simpler positivity results.
-/

example (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b := by
  positivity

/-
* `linarith` proves linear inequalities over linearly ordered commutative rings.
-/

example (x y : ℚ) (h1 : 0 < x + y) (h2 : 0 < x - y) : 0 < x := by
  linarith

/-
* `grw` is a generalization of `rw` that supports inequalities.
-/

example (x y : ℝ) : |Real.sin (x + y)| ≤ |Real.sin x| + |Real.sin y| := by
  grw [Real.sin_add, abs_add_le, abs_mul, abs_mul,
    Real.abs_cos_le_one, Real.abs_cos_le_one, mul_one, one_mul]

example {R : Type*} [CommRing R] (I J : Ideal R) (h : I ⊔ J = ⊤) :
    I * J = I ⊓ J := by
  refine le_antisymm Ideal.mul_le_inf ?_
  rw [← Ideal.mul_top (I ⊓ J), ← h, Ideal.mul_sup]
  apply sup_le
  · grw [inf_le_right, mul_comm]
  · grw [inf_le_left]

/-
* `push Not` pushes negations inward.
* `by_contra!` does `by_contra` and then `push Not`
-/

example (S : Set ℝ) (a : ℝ) (is_lub : ∀ x, (∀ y ∈ S, y ≤ x) → a ≤ x) :
    ∀ ε > 0, ∃ x ∈ S, a - ε < x := by
  intro ε hε
  specialize is_lub (a - ε)
  by_contra! h
  specialize is_lub h
  linarith

/-
* `contrapose` uses contraposition to swap a given hypothesis with the goal.
* `contrapose!` does `contrapose` and then `push Not`
-/

example (S : Set ℝ) (a : ℝ) (is_lub : ∀ x, (∀ y ∈ S, y ≤ x) → a ≤ x) :
    ∀ ε > 0, ∃ x ∈ S, a - ε < x := by
  intro ε hε
  specialize is_lub (a - ε)
  contrapose! is_lub
  exact ⟨is_lub, by linarith⟩

/-
* `grind` is a powerful tactic that uses library lemmas tagged with `@[grind]`
  to assemble equalities, inequalities, and logical facts. `grind` also has
  solvers for domains like linear arithmetic and commutative rings.
-/

example (a b c d : ℝ) (h_add : a + b = c + d) (h_mul : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  grind

example {α : Type*} (A B C : Set α) :
    (A ∪ B) ∩ (B ∪ C) ∩ (C ∪ A) = (A ∩ B) ∪ (B ∩ C) ∪ (C ∩ A) := by
  grind

/-
A few more points of guidance:

* Use the right tactic for the job. Prefer focused tactics over general tactics.
* The usage of tactics should help communicate the structure of the proof.
  Edge-cases and side goals should be closed quickly with automation, whereas
  important steps and key theorems should be highlighted with focused tactics.
* Tactics can be classified as rigid (predictable and focused) or flexible
  (unpredictable and general). For example, `simp` and `grind` are classified as
  flexible since they draw upon all of mathlib and their behavior can change as
  the library changes and more `@[simp]` and `@[grind]` tags are added. Flexible
  tactics (like `simp` and `grind`) with unpredictable output should not not be
  used before rigid tactics (like `rw`) that are sensitive to the exact state.

Here are two examples about convergence of sequences. Convergence is formalized
using filters. E.g., `Filter.Tendsto f Filter.atTop (nhds 0)` means that `f(x)`
tends to `0` and `x` tends to `+∞`. This avoids needing separate definitions
for each variety of limit. These examples have slick proofs using filters,
but you can give a more traditional proof by using `Metric.tendsto_atTop`.
-/

#check Metric.tendsto_atTop
#check exists_nat_ge

open Filter

example : Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
  sorry

example : ¬ ∃ a, Tendsto (fun n : ℕ ↦ (-1) ^ n) atTop (nhds a) := by
  sorry
