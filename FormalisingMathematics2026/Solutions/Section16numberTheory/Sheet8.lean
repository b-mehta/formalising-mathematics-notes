/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Factorial.BigOperators

namespace Section15Sheet8

open scoped BigOperators

open Finset

/-

## -1 is a square mod p if p=1 mod 4

I formalise the following constructive proof in the solutions:
`((p-1)/2)!` works!

Why does it work: claim `1*2*...*(p-1)/2` squared is `-1`
`1*2*....*(p-1)/2 - p` is 1 mod 4 so this is also
`-1 * -2 * ... * -((p-1)/2)`, and mod p this is the same
`(p-1) * (p-2) * ... ((p+1)/2)`, so `i²=1*2*....*(p-2)*(p-1)=(p-1)!`
Wilson's theorem tells us that `(p-1)! = -1 mod p` if p is prime.

-/

theorem exists_sqrt_neg_one_of_one_mod_four
    (p : ℕ) (hp : p.Prime) (hp2 : ∃ n, p = 4 * n + 1) :
    ∃ i : ZMod p, i ^ 2 = -1 := by
  obtain ⟨n, rfl⟩ := hp2
  let i : ZMod (4 * n + 1) := (2 * n).factorial
  use i
  haveI : Fact (4 * n + 1).Prime := ⟨hp⟩
  have h_wilson := ZMod.wilsons_lemma (4 * n + 1)
  change ((4 * n).factorial : ZMod (4 * n + 1)) = -1 at h_wilson
  rw [← h_wilson]
  rw [pow_two]
  dsimp [i]
  have h_eq : (4 * n).factorial = (2 * n).factorial * (∏ j ∈ range (2 * n), (2 * n + j + 1))
  · rw [Nat.factorial_eq_prod_range_add_one, Nat.factorial_eq_prod_range_add_one,
        show 4 * n = 2 * n + 2 * n by ring, prod_range_add]
  rw [h_eq]
  push_cast
  congr 1
  rw [Nat.factorial_eq_prod_range_add_one]
  push_cast
  conv_rhs => rw [prod_range_reflect _ (2 * n)]
  simp only
  have : ∀ j ∈ range (2 * n), (2 * ↑n + (2 * n - 1 - j) + 1 : ZMod (4 * n + 1)) = -(j + 1 : ZMod (4 * n + 1))
  · intro j hj
    rw [ZMod.eq_neg_iff_add_eq_zero]
    push_cast
    rw [show 2 * n + (2 * n - 1 - j) + 1 + (j + 1) = 4 * n + 1 by
      simp at hj; omega]
    rw [ZMod.natCast_self]
  rw [prod_congr rfl this, prod_neg, show (-1 : ZMod (4 * n + 1)) ^ (2 * n) = 1 by
    rw [pow_mul, show (-1 : ZMod (4 * n + 1)) ^ 2 = 1 by ring, one_pow]]
  simp

end Section15Sheet8