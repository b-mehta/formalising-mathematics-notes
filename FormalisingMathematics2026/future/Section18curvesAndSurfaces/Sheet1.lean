/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv


/-

# Basic calculus

Let's figure out how to do differentiability in Lean together
-/

section DifferentiabilityInGeneral

-- This is how to say a function is differentiable:
-- these variables will only live in this section
-- Let 𝕜 be a field equipped with a non-trivial norm (e.g. ℝ)
variable (𝕜 : Type) [NontriviallyNormedField 𝕜]

-- Let `E` be a 𝕜-vector space with a norm (e.g. ℝ or ℝ²)
variable (E : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- and let `F` be another one
variable (F : Type) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- Then it makes sense to say that a function `f : E → F` is differentiable
variable (f : E → F)

-- This is the true-false statement that `f` is differentiable.
example : Prop := Differentiable 𝕜 f

-- You can also ask that `f` is differentiable at `e : E`
example (e : E) : Prop := DifferentiableAt 𝕜 f e

open ContDiff

-- Here's how you say "`f` is continuously differentiable 37 times"
-- (i.e. you can differentiate f 37 times and when you're done the answer is continuous
-- but might not be differentiable)
example : Prop :=
  ContDiff 𝕜 37 f

-- Here's how you say "`f` is smooth, i.e. infinitely differentiable"
example : Prop :=
  ContDiff 𝕜 ∞ f

-- A recent change to the library means we can also say `f` is analytic in this setup, like this
-- Take a look at the documentation in the ContDiff/Defs file for more details
example : Prop :=
  ContDiff 𝕜 ω f

end DifferentiabilityInGeneral

-- Let's now just assume `𝕜 = ℝ`; then `E` and `F` can be `ℝ` or `ℂ` or `ℝ × ℝ` or `Fin n → ℝ` (the
-- way we say `ℝⁿ` in mathlib) or ...
open Real

-- because there is `Real.cos` and `Complex.cos`,
-- This says "the cos(sin(x))*exp(x) is differentiable"
-- Hint: the theorems are called theorems like `Differentiable.mul` etc.
-- Try proving it by hand.
example : Differentiable ℝ fun x => cos (sin x) * exp x := by
  sorry

-- Now see what `hint` has to say!
example : Differentiable ℝ fun x => cos (sin x) * exp x := by sorry

-- The simplifier can do this with the help of `ring` afterwards
example (x : ℝ) :
    deriv (fun x => cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  simp
  ring

-- Try this one:
example (a : ℝ) (x : ℝ) : DifferentiableAt ℝ (fun y : ℝ => exp (-(a * y ^ 2))) x := by sorry

-- For continuity, differentiability, and contdiff, there are a few different objects floating
-- around.
-- (In fact, the same applies for infinite sums and infinite products too!)
-- I'll continue with the differentiability example.

-- there's
-- HasDerivWithinAt, HasDerivAt
-- DifferentiableWithinAt, DifferentiableAt, DifferentiableOn, Differentiable
-- derivWithinAt, derivWithin, deriv
-- Think of this as two-dimensional: I can go down this list or across it.

-- oh, and then FDeriv versions of everything
-- the F stands for Fréchet: this is the version where you're differentiating maps ℝⁿ → ℝᵐ
-- and so the derivative is a linear map, rather than just a number; I'll ignore this generalisation
-- for now and focus on the version where the domain is one-dimensional

-- `HasDerivWithinAt` and `HasDerivAt` are used as
-- `HasDerivWithinAt f f' s x` and `HasDerivAt f f' x`, and they're both saying that the derivative
-- of `f` at `x` exists and is `f'`.
-- But `HasDerivWithinAt` is a bit more restrictive: it says that in the limit defining the
-- derivative, you can only take limits within `s`. So, for example, if `s = [0, 1]` and `x = 0`,
-- the "ramp" function satisfies `HasDerivWithinAt ramp 1 [0, 1] 0` since we can only take the limit
-- from the right but doesn't satisfy `HasDerivAt ramp 1 0`, since if you take the limit from the
-- left you get a different answer as from the left.

-- `DifferentiableWithinAt` and `DifferentiableAt` basically just say that there's some `f'` for
-- which `HasDerivWithinAt` or `HasDerivAt`, respectively, are true
-- `DifferentiableOn 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`, and
-- `Differentiable 𝕜 f` means that `f` is differentiable at any point.
-- These four actually *do* work in the higher-dimensional case, since they don't explicitly mention
-- the output type of the derivative. And so `f : E → F` can be a function between two general
-- vector spaces over the field, not just `f : 𝕜 → F`; the one-dimensional case.
-- (This is why 𝕜 needs to be specified in these four, since it can't be inferred from the type of
-- `f`)

-- Finally `derivWithin` and `deriv` give you the actual value of the derivative,
-- if it exists. If it doesn't exist, they give zero (remember junk values?).
-- That is, if `HasDerivAt f f' x` then `deriv f x = f'`.
-- There's a slight catch, however in that it might be true that `HasDerivAt f f₁ x` and
-- `HasDerivAt f f₂ x` could both be true if your spaces are sufficiently weird (think about how
-- limits might not be unique in a non-Hausdorff space). So the equality I just told you is only
-- true if you can assume derivatives are unique, which is written with `UniqueDiff...`.
-- In most practical settings, that will be true.

-- Continuity has the WithinAt / At / On / - quadruple too, with the analogous meaning as for
-- differentiability
-- Infinite sums have the other dimension of duplication: there's HasSum, Summable and tsum
-- which play the same roles as HasDerivAt, DifferentiableAt and deriv.
