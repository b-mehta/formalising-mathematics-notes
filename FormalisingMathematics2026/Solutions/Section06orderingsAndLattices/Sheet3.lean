/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic

/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one of these equalities holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not into puzzles like this, then feel free to skip
this question.

-/

example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  constructor
  · intro h a b c
    symm
    calc
      a ⊓ b ⊔ a ⊓ c = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [h]
      _ = a ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm, sup_of_le_left inf_le_left]
      _ = a ⊓ (c ⊔ a ⊓ b) := by rw [sup_comm]
      _ = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) := by rw [h]
      _ = a ⊓ (a ⊔ c) ⊓ (b ⊔ c) := by rw [inf_assoc, sup_comm, sup_comm c b]
      _ = a ⊓ (b ⊔ c) := by rw [inf_of_le_left (le_sup_left : a ≤ a ⊔ c)]
  · intro h a b c
    symm
    calc
      (a ⊔ b) ⊓ (a ⊔ c) = (a ⊔ b) ⊓ a ⊔ (a ⊔ b) ⊓ c := by rw [h]
      _ = a ⊔ (a ⊔ b) ⊓ c := by rw [inf_comm, inf_of_le_left (le_sup_left : a ≤ a ⊔ b)]
      _ = a ⊔ c ⊓ (a ⊔ b) := by rw [inf_comm]
      _ = a ⊔ (c ⊓ a ⊔ c ⊓ b) := by rw [h]
      _ = (a ⊔ c ⊓ a) ⊔ c ⊓ b := by rw [sup_assoc, inf_comm]
      _ = a ⊔ b ⊓ c := by rw [sup_of_le_left (inf_le_right : c ⊓ a ≤ a), inf_comm]
