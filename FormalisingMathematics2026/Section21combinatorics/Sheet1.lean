/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib

-- # Combinatorics

open Classical
open Finset

-- Have a look at these lemmas:
#check Finset.sum_const
#check Finset.sum_congr
#check Finset.sum_le_sum
#check Finset.sum_comm

lemma Finset.card_eq_sum_ones' {α : Type*} (s : Finset α) : #s = ∑ x ∈ s, 1 := by
  rw [Finset.sum_const]
  simp

theorem double_counting {α β : Type*} (s : Finset α) (t : Finset β) (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #(t.filter (r a ·)))
    (h_right : ∀ b ∈ t, #(s.filter (r · b)) = 1) :
    3 * #s ≤ #t := by
  calc 3 * #s = ∑ a ∈ s, 3 := by simp [mul_comm]
    _ ≤ ∑ a ∈ s, #(t.filter (r a ·)) := sum_le_sum h_left
    _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := sum_comm
    _ = ∑ b ∈ t, #(s.filter (r · b)) := by simp
    _ = ∑ b ∈ t, 1 := sum_congr rfl h_right
    _ = #t := by simp

theorem doubleCounting' {α β : Type*} (s : Finset α) (t : Finset β) (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ (t.filter (r a ·)).card)
    (h_right : ∀ b ∈ t, (s.filter (r · b)).card = 1) :
    3 * s.card ≤ t.card := by
  suffices s.card * 3 ≤ t.card * 1 by linarith
  exact Finset.card_mul_le_card_mul r h_left (fun b hb => (h_right b hb).le)

lemma Nat.coprime_self_add_one (n : ℕ) :
    Nat.Coprime n (n + 1) := by simp

-- This one will help!
#check exists_lt_card_fiber_of_mul_lt_card_of_maps_to

example {n : ℕ} (A : Finset ℕ)
    (hA : A.card = n + 1)
    (hA' : A ⊆ Finset.range (2 * n)) :
    ∃ x y, x ≠ y ∧ x ∈ A ∧ y ∈ A ∧ Nat.Coprime x y := by
  let s := A
  let t := range n
  let f : ℕ → ℕ := fun n ↦ n / 2
  let m : ℕ := 1
  have h₁ : ∀ a ∈ s, f a ∈ t := by
    simp only [s, f, t, mem_range]
    intro a ha
    have : a ∈ range (2 * n) := hA' ha
    simp only [mem_range] at this
    omega
  have h₂ : #t * m < #s := by
    simp only [t, m, s]
    simp [hA]
  obtain ⟨y, hy, hy'⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to h₁ h₂
  simp only [m, one_lt_card, mem_filter, ne_eq, f, s] at hy'
  obtain ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, hab⟩ := hy'
  use a, b, hab, ha, hb
  wlog hab' : a ≤ b generalizing a b
  · exact (this b hb hb' _ (Ne.symm hab) ha ha' (by omega)).symm
  have : b = a + 1 := by omega
  rw [this]
  apply Nat.coprime_self_add_one

-- harder. ordCompl or ordProj could help
example {n : ℕ} (A : Finset ℕ)
    (hA : A.card = n + 1)
    (hA' : A ⊆ Finset.Ioc 0 (2 * n)) :
    ∃ x y, x ≠ y ∧ x ∈ A ∧ y ∈ A ∧ x ∣ y := by
  sorry
