/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic

section Section15Sheet7

/-

# Prove that for every positive integer n the number 3 × (1⁵ +2⁵ +...+n⁵)
# is divisible by 1³+2³+...+n³

This is question 9 in Sierpinski's book

-/

open scoped BigOperators

open Finset

example (n : ℕ) : ∑ i ∈ range n, i ^ 3 ∣ 3 * ∑ i ∈ range n, i ^ 5 := by
  let S3 : ℕ → ℤ := fun n => ∑ i ∈ range n, (i : ℤ) ^ 3
  let S5 : ℕ → ℤ := fun n => ∑ i ∈ range n, (i : ℤ) ^ 5
  have h3 (n : ℕ) : 4 * S3 n = (n : ℤ) ^ 2 * (n - 1) ^ 2 := by
    induction n with
    | zero => rfl
    | succ d hd =>
      unfold S3; rw [sum_range_succ]
      push_cast
      linear_combination hd
  have h5 (n : ℕ) : 12 * S5 n = (n : ℤ) ^ 2 * (n - 1) ^ 2 * (2 * (n : ℤ) ^ 2 - 2 * n - 1) := by
    induction n with
    | zero => rfl
    | succ d hd =>
      unfold S5; rw [sum_range_succ]
      push_cast
      linear_combination hd
  zify
  push_cast
  have h_eq : 3 * S5 n = S3 n * (2 * (n : ℤ) ^ 2 - 2 * n - 1) := by
    apply Int.eq_of_mul_eq_mul_left (by norm_num : (4 : ℤ) ≠ 0)
    linear_combination 1 * h5 n - (2 * (n : ℤ) ^ 2 - 2 * n - 1) * h3 n
  rw [h_eq]
  apply dvd_mul_right

end Section15Sheet7
