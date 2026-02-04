/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace Section15Sheet5

/-

# Prove that 19 ∣ 2^(2⁶ᵏ⁺²) + 3 for k = 0,1,2,...


This is the fifth question in Sierpinski's book "250 elementary problems
in number theory".

thoughts

if a(k)=2^(2⁶ᵏ⁺²)
then a(k+1)=2^(2⁶*2⁶ᵏ⁺²)=a(k)^64

Note that 16^64 is 16 mod 19 according to a brute force calculation
and so all of the a(k) are 16 mod 19 and we're done

-/

theorem sixteen_pow_sixtyfour_mod_nineteen : (16 : ZMod 19) ^ 64 = 16 := by decide

theorem a_k_eq_16 (k : ℕ) : ((2 : ZMod 19) ^ 2 ^ (6 * k + 2)) = 16 := by
  induction k with
  | zero => decide
  | succ d hd =>
    rw [show 6 * (d + 1) + 2 = (6 * d + 2) + 6 by ring, pow_add, pow_mul, hd]
    exact sixteen_pow_sixtyfour_mod_nineteen

example (k : ℕ) : 19 ∣ 2 ^ 2 ^ (6 * k + 2) + 3 := by
  apply (ZMod.natCast_eq_zero_iff _ 19).mp
  push_cast
  rw [a_k_eq_16]
  decide

end Section15Sheet5
