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

example (n : ℕ) : ∑ i ∈ range n, i ^ 3 ∣ 3 * ∑ i ∈ range n, i ^ 5 := sorry

end Section15Sheet7
