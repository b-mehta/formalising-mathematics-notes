/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.PrincipalIdealDomain
-- theory of PIDs

/-!

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/

namespace Section14Sheet1

variable (R : Type) [CommRing R]

-- We say `R` is a *principal ideal ring* if all ideals are principal.
-- We say `R` is a *domain* if it's an integral domain.
-- We say `R` is a *principal ideal domain* if it's both.
-- So here's how to say "Assume `R` is a PID":
variable [IsPrincipalIdealRing R] [IsDomain R]

-- Note that both of these are typeclasses, so various things should
-- be automatic.
example : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b
  apply eq_zero_or_eq_zero_of_mul_eq_zero

-- typeclass inference
-- magically extracts the assumption from `IsDomain`
example : (0 : R) ≠ 1 :=
  zero_ne_one

example (I : Ideal R) : I.IsPrincipal :=
  inferInstance

example (I : Ideal R) : ∃ j, I = Ideal.span {j} :=
  ⟨Submodule.IsPrincipal.generator I, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩

-- product of two PIDs isn't a PID, but only because it's not a domain
example (A B : Type) [CommRing A] [CommRing B]
    [IsPrincipalIdealRing A] [IsPrincipalIdealRing B] :
    IsPrincipalIdealRing (A × B) where
  principal I := by
    -- every ideal of A × B is of the form I₁ × I₂
    let I1 : Ideal A := I.map (RingHom.fst A B)
    let I2 : Ideal B := I.map (RingHom.snd A B)
    have hI : I = I1.prod I2 := by
      ext x
      constructor
      · intro h
        exact ⟨Ideal.mem_map_of_mem _ h, Ideal.mem_map_of_mem _ h⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective (RingHom.fst A B)
          (fun a => ⟨(a, 0), rfl⟩)).1 h1
        obtain ⟨z, hz, hzx⟩ := (Ideal.mem_map_iff_of_surjective (RingHom.snd A B)
          (fun b => ⟨(0, b), rfl⟩)).1 h2
        have : x = (1, 0) * y + (0, 1) * z := by
          ext
          · simp; exact hyx.symm
          · simp; exact hzx.symm
        rw [this]
        apply Ideal.add_mem
        · apply Ideal.mul_mem_left
          exact hy
        · apply Ideal.mul_mem_left
          exact hz
    rw [hI]
    obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal I1
    obtain ⟨b, hb⟩ := IsPrincipalIdealRing.principal I2
    use (a, b)
    rw [ha, hb]
    ext x
    simp [Ideal.mem_prod, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      use (r, s)
      ext <;> simp [hr, hs]
    · rintro ⟨⟨r, s⟩, rfl⟩
      simp

end Section14Sheet1