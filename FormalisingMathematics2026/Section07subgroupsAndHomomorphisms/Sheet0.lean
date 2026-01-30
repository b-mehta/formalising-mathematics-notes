/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import Mathlib

/-!

# Some common error messages

When you get a Lean error, it can be hard to understand what it means, and even harder to fix it.
This file contains some common error messages that you might encounter, and explains what they mean,
and how you could fix them.
-/

/-!
# application type mismatch
This is a very common error for beginners who tend to make a bunch of arguments explicit in some
`variable` statement.
-/
section application_type_mismatch

/-! The following line accidentally makes `G` be explicit in `fancy`. -/
variable (G : Type) [AddCommGroup G]

/-! If your variable statement is very high up in the file, it might look like `fancyOp` takes two
explicit arguments only: `a` and `b`. -/
def fancyOp (a b : G) : G := a + b - b

#check fancyOp

/-! Lean complains that you are providing `a` instead of `G`. -/
-- lemma fancyOp_eq_left (a b : G) : fancyOp a b = a := sorry

end application_type_mismatch




section no_application_type_mismatch
/-! The better way to deal with this is to avoid declaring *any* explicit argument in the
`variable`. This is obviously a rule of thumb which you should feel free to disregard when there is
a good reason to do so. -/
variable {G : Type} [AddCommGroup G]

def otherFancyOp (a b : G) : G := a + b - b

/-! Works as expected. -/
lemma otherFancyOp_eq_left (a b : G) : otherFancyOp a b = a := sorry

end no_application_type_mismatch




/-!
# don't know how to synthesize placeholder
This is kind of the dual error to the above, as it often happens when too many arguments to a
definition are implicit. -/
section dont_know_how_to_synthesize_placeholder

def mulByZero {𝕜 : Type} {E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (x : E) : E :=
  (0 : 𝕜) • x

-- lemma mulByZero_eq_zero {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (x : E) :
--     mulByZero x = 0 := sorry

end dont_know_how_to_synthesize_placeholder

section dont_know_how_to_synthesize_placeholder

def mulByZero' {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (x : E) : E := (0 : 𝕜) • x

lemma mulByZero'_eq_zero {E : Type} [AddCommGroup E] [Module ℂ E] (x : E) :
    mulByZero' (𝕜 := ℂ) x = 0 := sorry

end dont_know_how_to_synthesize_placeholder


section dont_know_how_to_synthesize_placeholder

variable {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

-- a lot of junk here

#where

/-! Binder update -/

variable (𝕜) in
def mulByZero'' (x : E) : E := (0 : 𝕜) • x

#where

#check mulByZero''

lemma mulByZero''_eq_zero (x : E) : mulByZero'' 𝕜 x = 0 := sorry

end dont_know_how_to_synthesize_placeholder






/-! # failed to synthesize instance -/
section failed_to_synthesize_instance

variable {ι : Type} [Fintype ι]

-- lemma card_eq_card_ι_sub_one (i : ι) : Fintype.card {j // j ≠ i} = Fintype.card ι - 1 := sorry

end failed_to_synthesize_instance






/-!
# Junk values
-/

-- What should a - b mean if a < b?

example : 2 - 3 = 0 := by simp

example : 5 / 3 = 1 := by simp

example : (2 : ℤ) - 3 = -1 := by
  simp

example : (2 : ℚ) / 3 ≠ 0 := by
  simp

example : (2.01 : ℝ) / 3 ≠ 2 / 3 := by
  sorry

#eval 2 - 3
#eval 2 / 3
-- 2 // 3

example : (1 : ℝ) / 0 = 0 := by simp

example {x y : ℝ} (hy : y ≠ 0) : (x / y) * y = x := by
  rw [div_mul_cancel₀]
  exact hy

example : Real.sqrt (-1) = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos (by simp)

example : Real.log (-2) = Real.log 2 := by
  rw [Real.log_neg_eq_log]

#eval 2 - 3
#eval 2 - 4
