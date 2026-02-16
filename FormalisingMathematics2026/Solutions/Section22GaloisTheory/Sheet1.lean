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
  have h37 : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card H := by
    apply Subgroup.card_dvd_of_le
    exact inf_le_left
  have h42 : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card K := by
    apply Subgroup.card_dvd_of_le
    exact inf_le_right
  have h1 : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.gcd (Nat.card H) (Nat.card K) := by
    exact Nat.dvd_gcd h37 h42
  simp_rw [hH, hK, Nat.reduceGcd, Nat.dvd_one, Subgroup.card_eq_one] at h1
  exact h1

/-- Subgroups of coprime index generate the whole group. -/
example {G : Type*} [Group G] (H K : Subgroup G)
    (hH : H.index = 37) (hK : K.index = 42) :
    H ⊔ K = ⊤ := by
  have h37 : (H ⊔ K).index ∣ H.index := by
    apply Subgroup.index_dvd_of_le
    exact le_sup_left
  have h42 : (H ⊔ K).index ∣ K.index := by
    apply Subgroup.index_dvd_of_le
    exact le_sup_right
  have h1 : (H ⊔ K).index ∣ Nat.gcd H.index K.index := by
    exact Nat.dvd_gcd h37 h42
  simp_rw [hH, hK, Nat.reduceGcd, Nat.dvd_one, Subgroup.index_eq_one] at h1
  exact h1

/-- A group of prime order is cyclic. -/
example {G : Type*} [Group G] (hG : Nat.card G = 37) :
    ∃ g : G, Subgroup.zpowers g = ⊤ := by
  replace hG : (Nat.card G).Prime := by
    rw [hG]
    norm_num
  have : Finite G := by
    apply Nat.finite_of_card_ne_zero
    exact hG.ne_zero
  have : 1 < Nat.card G := by
    exact hG.one_lt
  rw [Finite.one_lt_card_iff_nontrivial] at this
  have : ∃ g : G, g ≠ 1 := by
    exact exists_ne 1
  obtain ⟨g, hg⟩ := this
  use g
  replace hg : Nat.card (Subgroup.zpowers g) ≠ 1 := by
    simpa
  have hg' : Nat.card (Subgroup.zpowers g) ∣ Nat.card G := by
    exact (Subgroup.zpowers g).card_subgroup_dvd_card
  rw [hG.dvd_iff_eq hg] at hg'
  exact (Subgroup.zpowers g).eq_top_of_card_eq hg'.symm

end GroupTheory

section RingTheory

example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    (f : R →+* S) : I ≤ (I.map f).comap f := by
  rw [← Ideal.map_le_iff_le_comap] -- Look Ma, no elements!

example {R : Type*} [CommRing R] (I J K : Ideal R)
    (h : (I : Set R) ⊆ J ∪ K) : I ≤ J ∨ I ≤ K := by
  contrapose! h
  obtain ⟨hI, hJ⟩ := h
  rw [SetLike.not_le_iff_exists] at hI hJ
  obtain ⟨x, xI, xJ⟩ := hI
  obtain ⟨y, yI, yK⟩ := hJ
  simp_rw [Set.not_subset, Set.mem_union, not_or]
  by_cases xK : x ∈ K
  · by_cases yJ : y ∈ J
    · refine ⟨x + y, ?_, ?_, ?_⟩
      · exact I.add_mem xI yI
      · contrapose! xJ
        exact (Submodule.add_mem_iff_left J yJ).mp xJ
      · contrapose yK
        exact (Submodule.add_mem_iff_right K xK).mp yK
    · exact ⟨y, yI, yJ, yK⟩
  · exact ⟨x, xI, xJ, xK⟩

example {R : Type*} [CommRing R] (I J P : Ideal R)
    (hP : P.IsPrime) (h : I * J ≤ P) : I ≤ P ∨ J ≤ P := by
  contrapose! h
  obtain ⟨hI, hJ⟩ := h
  rw [SetLike.not_le_iff_exists] at hI hJ ⊢
  obtain ⟨x, xI, xP⟩ := hI
  obtain ⟨y, yI, yP⟩ := hJ
  exact ⟨x * y, I.mul_mem_mul xI yI, hP.mul_notMem xP yP⟩

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
  have : FiniteDimensional K W := Module.finite_of_finrank_eq_succ hW
  by_contra h
  apply LinearMap.finrank_le_finrank_of_injective at h
  rw [hV, hW] at h
  norm_num at h

example (hV : Module.finrank K V = 37) (hW : Module.finrank K W = 42) :
    ¬ Function.Surjective f := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  by_contra h
  apply LinearMap.range_eq_top_of_surjective at h
  have hf := f.finrank_range_add_finrank_ker
  rw [h, finrank_top, hV, hW] at hf
  grind

example (S T : Submodule K V) (hV : Module.finrank K V = 50)
    (hS : Module.finrank K S = 37) (hT : Module.finrank K T = 42) :
    29 ≤ Module.finrank K (S ⊓ T : Submodule K V) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  have := Submodule.finrank_sup_add_finrank_inf_eq S T
  have := Submodule.finrank_le (S ⊔ T)
  grind

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
  have h37 : Module.finrank K (F ⊓ E : IntermediateField K L) ∣ Module.finrank K F := by
    apply finrank_dvd_of_le_right
    exact inf_le_left
  have h42 : Module.finrank K (F ⊓ E : IntermediateField K L) ∣ Module.finrank K E := by
    apply finrank_dvd_of_le_right
    exact inf_le_right
  simpa [hF, hE] using Nat.dvd_gcd h37 h42

example {K L : Type*} [Field K] [Field L] [Algebra K L] (F E : IntermediateField K L)
    (hF : Module.finrank K F = 37) (hE : Module.finrank K E = 42) :
    Module.finrank K (F ⊔ E : IntermediateField K L) = 37 * 42 := by
  apply le_antisymm
  · grw [finrank_sup_le, hF, hE]
  have h37 : Module.finrank K F ∣ Module.finrank K (F ⊔ E : IntermediateField K L) := by
    apply finrank_dvd_of_le_right
    exact le_sup_left
  have h42 : Module.finrank K E ∣ Module.finrank K (F ⊔ E : IntermediateField K L) := by
    apply finrank_dvd_of_le_right
    exact le_sup_right
  have h1 := Nat.lcm_dvd h37 h42
  simp_rw [hF, hE, Nat.lcm_eq_mul_div, Nat.reduceGcd, Nat.div_one] at h1
  suffices FiniteDimensional K (F ⊔ E : IntermediateField K L) from
    Nat.le_of_dvd Module.finrank_pos h1
  have : FiniteDimensional K F := Module.finite_of_finrank_eq_succ hF
  have : FiniteDimensional K E := Module.finite_of_finrank_eq_succ hE
  exact finiteDimensional_sup F E

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

example : IsGalois K L ↔ ∃ p : K[X], p.Separable ∧ p.IsSplittingField K L := by
  exact IsGalois.tfae.out 0 3

example (F E : IntermediateField K L) :
    fixingSubgroup (F ⊔ E) = fixingSubgroup F ⊓ fixingSubgroup E := by
  exact fixingSubgroup_sup

example [IsGalois K L] (G H : Subgroup Gal(L/K)) :
    fixedField (G ⊓ H) = fixedField G ⊔ fixedField H := by
  rw [← fixedField_fixingSubgroup (fixedField G ⊔ fixedField H),
    fixingSubgroup_sup, fixingSubgroup_fixedField, fixingSubgroup_fixedField]

example [IsGalois K L] (G H : Subgroup Gal(L/K)) :
    fixedField (G ⊔ H) = fixedField G ⊓ fixedField H := by
  apply le_antisymm
  · apply le_inf
    · exact fixedField_antitone le_sup_left
    · exact fixedField_antitone le_sup_right
  · rw [← fixedField_fixingSubgroup (fixedField G ⊓ fixedField H)]
    apply fixedField_antitone
    apply sup_le
    · conv_lhs => rw [← fixingSubgroup_fixedField G]
      apply IntermediateField.fixingSubgroup_antitone
      exact inf_le_left
    · conv_lhs => rw [← fixingSubgroup_fixedField H]
      apply IntermediateField.fixingSubgroup_antitone
      exact inf_le_right

example [IsGalois K L] (F E : IntermediateField K L) :
    fixingSubgroup (F ⊓ E) = fixingSubgroup F ⊔ fixingSubgroup E := by
  apply le_antisymm
  · rw [← fixingSubgroup_fixedField (F.fixingSubgroup ⊔ E.fixingSubgroup)]
    apply IntermediateField.fixingSubgroup_antitone
    apply le_inf
    · conv_rhs => rw [← fixedField_fixingSubgroup F]
      apply fixedField_antitone
      exact le_sup_left
    · conv_rhs => rw [← fixedField_fixingSubgroup E]
      apply fixedField_antitone
      exact le_sup_right
  · apply sup_le
    · exact fixingSubgroup_antitone inf_le_left
    · exact fixingSubgroup_antitone inf_le_right

end GaloisTheory
