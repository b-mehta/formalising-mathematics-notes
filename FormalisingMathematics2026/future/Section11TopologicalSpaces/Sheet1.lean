/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jujian Zhang, Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section10sheet1

noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, the type `TopologicalSpace X` is the type of topologies on `X`.
`TopologicalSpace` is a structure; its four fields are one data field `IsOpen : Set X → Prop` (the
predicate on subsets of `X` saying whether or not they're open) and then three proof fields
(`isOpen_univ` saying the whole space is open, `isOpen_inter` saying the intersection of two
opens is open, and `isOpen_sUnion` saying an arbitrary union of opens is open).

Here is a simple example: let's make the discrete topology on a type.
-/

open TopologicalSpace

set_option autoImplicit true

set_option linter.unusedVariables false -- please stop moaning about unused variables

example : TopologicalSpace X where
  IsOpen (s : Set X) := True -- "Is `s` open? Yes, always"
  isOpen_univ := by
    -- is the whole space open? The goal is `True`
    trivial
  isOpen_inter := by
    -- let s and t be two sets
    intros s t
    -- assume they're open
    intros hs ht
    -- Is their intersection open?
    -- By definition, this means "can you prove `True`"?
    trivial
  isOpen_sUnion := by
    -- say F is a family of sets
    intro F
    -- say they're all open
    intro hF
    -- Is their union open?
    trivial

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ -- empty set or whole thing
  isOpen_univ := by
    sorry -- use `dsimp`
  isOpen_inter s t := by
    intro hs ht
    rcases hs with rfl | rfl
    · simp
    · simpa
  isOpen_sUnion := by
    intro F
    -- do cases on whether Set.univ ∈ F
    -- by_cases
    sorry

-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  sorry

-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ
#synth UniformSpace ℝ
#synth PseudoMetricSpace ℝ

-- Let's make it from first principles.

/-- documentation string -/
def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y → y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  rw [Real.IsOpen]
  simp only [Set.mem_univ, gt_iff_lt, implies_true, and_true, forall_const]
  use 1
  norm_num

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  sorry

lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  sorry

set_option autoImplicit true

-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion

#lint
