/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import Mathlib

section GroupTheory

/-- Lagrange's theorem:
The order of a subgroup divides the order of the group. -/
example {G : Type*} [Group G] (H K : Subgroup G) (h_le : H ≤ K) :
    Nat.card H ∣ Nat.card K := by
  exact Subgroup.card_dvd_of_le h_le

/-- The order of an element divides the order of the group. -/
example {G : Type*} [Group G] (g : G) :
    orderOf g ∣ Nat.card G := by
  exact orderOf_dvd_natCard g

example {G G' : Type*} [Group G] [Group G'] (H : Subgroup G)
    (f : G →* G') : H ≤ (H.map f).comap f := by
  intro g hg
  rw [Subgroup.mem_comap]
  rw [Subgroup.mem_map]
  use g

example {G G' : Type*} [Group G] [Group G'] (H : Subgroup G)
    (f : G →* G') : H ≤ (H.map f).comap f := by
  rw [← Subgroup.map_le_iff_le_comap] -- Look Ma, no elements!

/-- Subgroups of coprime order are disjoint. -/
example {G : Type*} [Group G] (H K : Subgroup G)
    (hH : Nat.card H = 37) (hK : Nat.card K = 42) :
    H ⊓ K = ⊥ := by
  sorry

/-- Subgroups of coprime index generate the whole group. -/
example {G : Type*} [Group G] (H K : Subgroup G)
    (hH : H.index = 37) (hK : K.index = 42) :
    H ⊔ K = ⊤ := by
  sorry

/-- A group of prime order is cyclic. -/
example {G : Type*} [Group G] (hG : Nat.card G = 37) :
    ∃ g : G, Subgroup.zpowers g = ⊤ := by
  sorry

end GroupTheory

section RingTheory

example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    (f : R →+* S) : I ≤ (I.map f).comap f := by
  intro x hx
  rw [Ideal.mem_comap]
  -- eek! there's no `Ideal.mem_map`!
  sorry

example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    (f : R →+* S) : I ≤ (I.map f).comap f := by
  rw [← Ideal.map_le_iff_le_comap] -- Look Ma, no elements!

example {R : Type*} [CommRing R] (I J K : Ideal R)
    (h : (I : Set R) ⊆ J ∪ K) : I ≤ J ∨ I ≤ K := by
  -- this is in mathlib, but try proving this directly with elements
  sorry

example {R : Type*} [CommRing R] (I J P : Ideal R)
    (hP : P.IsPrime) (h : I * J ≤ P) : I ≤ P ∨ J ≤ P := by
  -- this is in mathlib, but try proving this directly with elements
  sorry

end RingTheory

section LinearAlgebra

variable {K V W : Type*} [Field K] [AddCommGroup V] [AddCommGroup W]
  [Module K V] [Module K W] (f : V →ₗ[K] W)

#check LinearMap.ker f -- `f.ker` in latest Mathlib
#check LinearMap.range f -- `f.range` in latest Mathlib

/-- The rank-nullity theorem. -/
example [FiniteDimensional K V] :
    Module.finrank K (LinearMap.range f) +
      Module.finrank K (LinearMap.ker f) = Module.finrank K V := by
  exact f.finrank_range_add_finrank_ker

example (hV : Module.finrank K V = 42) (hW : Module.finrank K W = 37) :
    ¬ Function.Injective f := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  have : FiniteDimensional K W := Module.finite_of_finrank_eq_succ hW
  sorry

example (hV : Module.finrank K V = 37) (hW : Module.finrank K W = 42) :
    ¬ Function.Surjective f := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  have : FiniteDimensional K W := Module.finite_of_finrank_eq_succ hW
  sorry

example (S T : Submodule K V) (hV : Module.finrank K V = 50)
    (hS : Module.finrank K S = 37) (hT : Module.finrank K T = 42) :
    29 ≤ Module.finrank K (S ⊓ T : Submodule K V) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  sorry

end LinearAlgebra

section FieldTheory

open Complex IntermediateField Polynomial

-- Many ways to produce field extensions:
#check ℚ⟮I⟯ -- notation for `IntermediateField.adjoin ℚ {I}`
#check AdjoinRoot (X ^ 2 + 1 : ℚ[X])
#check (X ^ 2 + 1 : ℚ[X]).SplittingField

/-- Multiplicativity of degree, stated for `IntermediateField`. -/
example {F L : Type*} [Field F] [Field L] [Algebra F L]
    (K : IntermediateField F L) :
    Module.finrank F K * Module.finrank K L = Module.finrank F L := by
  exact Module.finrank_mul_finrank F K L

/-- Multiplicativity of degree, stated relatively. -/
example {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L] :
    Module.finrank F K * Module.finrank K L = Module.finrank F L := by
  exact Module.finrank_mul_finrank F K L

example {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F E : IntermediateField K L)
    (hF : Module.finrank K F = 37) (hE : Module.finrank K E = 42) :
    F ⊓ E = ⊥ := by
  sorry

example {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F E : IntermediateField K L)
    (hF : Module.finrank K F = 37) (hE : Module.finrank K E = 42) :
    Module.finrank K (F ⊔ E : IntermediateField K L) = 37 * 42 := by
  sorry

end FieldTheory

section GaloisTheory

open IntermediateField IsGalois Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

#check fixingSubgroup
#check fixedField
#check fixingSubgroup_fixedField
#check fixedField_fixingSubgroup
#check fixingSubgroup_antitone
#check fixedField_antitone

example : IsGalois K L ↔ Algebra.IsSeparable K L ∧ Normal K L := by
  exact isGalois_iff

example : IsGalois K L ↔ fixedField (⊤ : Subgroup Gal(L/K)) = ⊥ := by
  exact IsGalois.tfae.out 0 1

example : IsGalois K L ↔ Nat.card Gal(L/K) = Module.finrank K L := by
  exact IsGalois.tfae.out 0 2

example : IsGalois K L ↔
    ∃ p : K[X], p.Separable ∧ p.IsSplittingField K L := by
  exact IsGalois.tfae.out 0 3

example (F E : IntermediateField K L) :
    fixingSubgroup (F ⊔ E) = fixingSubgroup F ⊓ fixingSubgroup E := by
  exact fixingSubgroup_sup

example [IsGalois K L] (G H : Subgroup Gal(L/K)) :
    fixedField (G ⊓ H) = fixedField G ⊔ fixedField H := by
  sorry

example [IsGalois K L] (G H : Subgroup Gal(L/K)) :
    fixedField (G ⊔ H) = fixedField G ⊓ fixedField H := by
  sorry

example [IsGalois K L] (F E : IntermediateField K L) :
    fixingSubgroup (F ⊓ E) = fixingSubgroup F ⊔ fixingSubgroup E := by
  sorry

end GaloisTheory
