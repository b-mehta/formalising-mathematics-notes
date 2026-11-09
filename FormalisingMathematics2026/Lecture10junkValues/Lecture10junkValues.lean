/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Lecture 10: Junk Values
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section

/-
In ordinary mathematics, a definition may be undefined on certain inputs.
For example, division is undefined when the denominator is zero, or
the derivative is undefined when the function is not differentiable.

There are several ways to formalize these definitions in Lean. One way
would be to restrict the definitions to the subtype where they are defined.
-/

noncomputable def div_subtype (x : ℚ) (y : {t : ℚ // t ≠ 0}) : ℚ :=
  sorry

/-
The problem with this approach is that you cannot directly plug a rational
number into this definition because there is no coercion `ℚ → {t : ℚ // t ≠ 0}`.
-/

#check div_subtype 1 ⟨2, two_ne_zero⟩

/-
Another way would be to add hypotheses to the definitions.
-/

def div_hypothesis (x : ℚ) (y : ℚ) (hy : y ≠ 0) : ℝ :=
  sorry

/-
The problem is still that every single time you want to write down division,
you have to reprovide the proof that the denominator is nonzero.
-/

#check div_hypothesis 1 2 two_ne_zero

/-
Instead, Lean and mathlib frequently opt to drop hypotheses entirely by
adding junk values such as `a / 0 = 0`.
-/

#eval (1 : ℚ) / (0 : ℚ)

/-
This doesn't result in any contradictions, because the hypotheses will
instead appear in theorems that would otherwise fail at these junk values.
-/

#check mul_div_cancel₀

/-
But sometimes well-chosen junk values allow these hypotheses to be
dropped entirely from certain theorems.
-/

#check Nat.mul_sub
#check div_div
#check pow_card_eq_one'
#check orderOf_dvd_iff_pow_eq_one
#check Subgroup.index_inf_le
#check tsum_mul_left
#check tprod_inv
#check Real.deriv_log
#check exists_deriv_eq_zero
#check integral_gaussian
#check Real.zero_at_infty_fourier
#check Matrix.mul_inv_rev
#check LinearMap.det_comp
#check Polynomial.card_roots'
#check minpoly.aeval
#check Module.finrank_mul_finrank

/-
In rare cases, a junk value might be a natural artifact of the
construction rather than a conscious decision.
-/

#check riemannZeta_one

/-
Junk values are one common source of misformalization.
At the very least, Lean will not alert you to missing hypotheses
since the theorem statements make perfect sense without them.

For example, the following theorem is false without the
additional hypotheses that `f` and `g` are differentiable.
-/

example (f g : ℝ → ℝ) : deriv (f + g) = deriv f + deriv g := by
  sorry

/-
Junk values can also make it harder to determine when a definition will behave
as expected. For example, the following theorem is false, but can you see why?
-/

open Filter in
example (a : ℕ → ℝ) (L : ℝ)
    (h : Tendsto (fun N ↦ ∑ n ∈ Finset.range N, a n) atTop (nhds L)) :
    ∑' n : ℕ, a n = L :=
  sorry

/-
And finally, here is one last example of junk value subtlety.
-/

variable {X : Type*} [MetricSpace X]

noncomputable def infDist (x : X) (s : Set X) : ℝ :=
  ⨅ y ∈ s, dist x y

/-
The issue is that `⨅ y ∈ s, dist x y` actually parses as a nested infimum
`⨅ y : ℝ, ⨅ (_ : y ∈ s), dist x y` where the inner infimum will have
junk value zero when the indexing type `y ∈ s` is empty.

Mathlib solves this by first defining an `ENNReal` version of `infDist`.
-/

#check Metric.infDist
#check Metric.infEDist

/-
## Examples for you to try
-/

example (s : Set X) (x : X) : infDist x s = 0 := by
  sorry

example (x : ℝ) : orderOf x ≤ 2 := by
  sorry

example (α : Type*) : ∑' a : α, 1 = Nat.card α := by
  sorry

example : deriv (fun t : ℝ ↦ t / t) = 0 := by
  sorry

open scoped IntermediateField in
example {K L : Type*} [Field K] [Field L] [Algebra K L] {x : L} :
    Module.finrank K K⟮x⟯ = (minpoly K x).natDegree := by
  sorry

open Filter in
example : ∃ (a : ℕ → ℝ) (L : ℝ),
    Tendsto (fun N ↦ ∑ n ∈ Finset.range N, a n) atTop (nhds L)
      ∧ ¬ ∑' n : ℕ, a n = L := by
  sorry
