/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import Mathlib.Order.Filter.Basic

/-!

# Examples of filters

## `atTop` filter on a totally ordered set

Let `L` be a non-empty totally ordered set. Let's say that a subset `X` of `L` is
"big" if there exists `x : L` such for all `y ≥ x`, `y ∈ X`.

I claim that the big subsets are a filter. Check this. The mathematical idea
is that the "big subsets" are the neighbourhoods of `∞`, so the corresponding
filter is some representation of an infinitesimal neighbourhood of `∞`.

Implementation notes: `LinearOrder L` is the type of linear orders on `L`.
`e : L` is just an easy way of saying that `L` is nonempty.

Recall that `max x y` is the max of x and y in a `LinearOrder`, and
`le_max_left a b : a ≤ max a b` and similarly `le_max_right`.
-/

namespace Filter

open Set

-- (The real definition of the atTop filter is more general than this: it only assumes that we have
-- a preorder. But for now, where we're just thinking about going to infinity in ℕ or ℝ, a nonempty
-- linear order is plenty general enough.)

/-- A simplified version of the `atTop'` filter for nonempty linear orders. -/
def atTop' (L : Type) [LinearOrder L] (e : L) : Filter L where
  sets := {X : Set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X}
  univ_sets := by
    use e
    intro y hy
    trivial
  sets_of_superset := by
    rintro x y ⟨x₀, hx⟩ hxy
    use x₀
    intro z hz
    apply hxy
    apply hx
    exact hz
  inter_sets := by
    rintro x y ⟨x₀, hx⟩ ⟨y₀, hy⟩
    use max x₀ y₀
    intro z hz
    constructor
    · apply hx
      exact le_trans (le_max_left x₀ y₀) hz
    · apply hy
      exact le_trans (le_max_right x₀ y₀) hz
/-

## the cofinite filter

The _cofinite filter_ on a type `α` has as its sets the subsets `S : set α`
with the property that `Sᶜ`, the complement of `S`, is finite.
Let's show that these are a filter.

Things you might find helpful:

`compl_univ : univᶜ = ∅`
`finite_empty : Finite ∅`
`compl_subset_compl : Xᶜ ⊆ Yᶜ ↔ Y ⊆ X`
`Finite.subset : S.finite → ∀ {T : set α}, T ⊆ S → T.Finite`
`compl_inter S T : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ`
`Finite.union : S.finite → T.finite → (S ∪ T).Finite`

NB if you are thinking "I could never use Lean by myself, I don't know
the names of all the lemmas so I have to rely on someone telling them all to
me" then what you don't realise is that I myself don't know the names
of all the lemmas either -- I am literally just guessing them and pressing
ctrl-space to check. Look at the names of the lemmas and begin to understand
that you can probably guess them yourself.
-/
def cofinite' (α : Type) : Filter α where
  sets := {S : Set α | Sᶜ.Finite}
  univ_sets := by
    simp [compl_univ, finite_empty]
  sets_of_superset := by
    intro x y hx hxy
    rw [mem_setOf_eq] at *
    apply hx.subset
    rwa [compl_subset_compl]
  inter_sets := by
    intro x y hx hy
    rw [mem_setOf_eq] at *
    rw [compl_inter]
    exact hx.union hy

def nhds' {X : Type} [TopologicalSpace X] (x : X) : Filter X where
  sets := {s : Set X | ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ s}
  univ_sets := by
    use univ
    simp [isOpen_univ]
  sets_of_superset := by
    rintro x₀ y ⟨U, hx, hU, hUx⟩ hxy
    use U
    exact ⟨hx, hU, hUx.trans hxy⟩
  inter_sets := by
    rintro x₀ y ⟨U, hx, hU, hUx⟩ ⟨V, hy, hV, hVy⟩
    use U ∩ V
    refine ⟨⟨hx, hy⟩, IsOpen.inter hU hV, ?_⟩
    exact inter_subset_inter hUx hVy

/-

## Harder exercises.

If you like this filter stuff, then formalise in Lean and prove the following:

(1) prove that the cofinite filter on a finite type is the entire power set filter (`⊥`).
(2) prove that the cofinite filter on `ℕ` is equal to the `atTop` filter.
(3) Prove that the cofinite filter on `ℤ` is not equal to the `atTop` filter.
(4) Prove that the cofinite filter on `ℕ` is not principal.

-/

end Filter
