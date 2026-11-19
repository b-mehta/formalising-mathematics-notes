/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Lecture 11: Filters
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section

variable (a : ℝ) (s : Set ℝ)

open scoped Topology

/-
There are many different notions of limits. Some examples include:
* limits of sequences (e.g., `lim_{n → ∞} a_n`),
* limits of functions (e.g., `lim_{x → a} f(x)`),
* one-sided limits (e.g., `lim_{x → a⁺} f(x)`),
* limits to plus/minus infinity (e.g., `lim_{x → -∞} f(x)`).

There are actually many more, since it's only complete expressions like
`lim_{n → ∞} a_n = L` or `lim_{x → a} f(x) = ∞` that have meaning.

Defining all of these different notions of limits in Lean would
get quite repetetive. Even worse, standard theorems such as
composition of limits would have to be duplicated immensely.

For example, one variant would state that if `lim_{n → ∞} a_n = L`
and `lim_{x → L} f(x) = ∞`, then `lim_{n → ∞} f(a_n) = ∞`.

To avoid this duplication, mathlib uses filters. For each limiting
behavior (e.g., `n → ∞` or `x → L`), there is a corresponding filter.

Limiting to `∞` is given by `Filter.atTop`. This works for both natural
numbers and real numbers. Limiting to `-∞` is given by `Filter.atBot`.
-/

example : Filter ℕ := Filter.atTop
example : Filter ℝ := Filter.atTop
example : Filter ℝ := Filter.atBot

/-
Limiting to a real number is given by `𝓝 a` (notation for `nhds a`).
Limiting to a real number from below is given by `𝓝[<] a`.
Limiting to a real number from above is given by `𝓝[>] a`.
-/

example : Filter ℝ := 𝓝 a
example : Filter ℝ := 𝓝[<] a
example : Filter ℝ := 𝓝[>] a

/-
There are also more exotic variants, like `𝓝[≠] a` for punctured neighborhoods
and `𝓝[s] a` for convergnce to `a` but only within a set `s`.
-/

example : Filter ℝ := 𝓝[≠] a
example : Filter ℝ := 𝓝[s] a

/-
For any pair of filters, convergence is expressed by `Filter.Tendsto`.
-/

#check Filter.Tendsto
#check Filter.Tendsto.comp

#check Real.tendsto_tan_pi_div_two
#check tendsto_one_div_add_atTop_nhds_zero_nat

/-
This still leaves open the question of how filters are actually defined.
But if we think about the precise definition of convergence, we can at
least motivate the definition of filters that appears in mathlib.

The basic expression `lim_{x → a} f(x) = L` means that for every `ε > 0`,
there exists a `δ > 0` such that if `|x - a| < δ` then `|f(x) - L| < ε`.
This can be rephrased in terms of sets as "for every neighborhood `V` of `L`,
there exists a neighborhood `U` of `a` such that `f(U) ⊆ V`".

By swapping out neighborhoods of `a` and `L` for other families of sets, we
can get different limiting behaviors. For example, `n → ∞` is captured by
the family "every set containing all sufficiently large natural numbers".

Thus, we can define a filter to be a family of sets satisfying certain axioms.
The precise axioms we want are closure under intersection and supersets.
We also want a filter to be nonempty which is equivalent to containing `univ`.
-/

structure Filter₁ (α : Type*) where
  sets : Set (Set α)
  univ_sets : Set.univ ∈ sets
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets

/-
There are many different ways to write down the definition of convergence.
To motivate mathlib's definition, we will being with the condition that
for every set `V ∈ Fα`, there exists a set `U ∈ Fβ` such that `f(U) ⊆ V`.
-/

variable {α β γ : Type*} (f : α → β) (g : β → γ)
  (Fα : Filter α) (Fβ : Filter β) (Fγ : Filter γ)

def Filter.Tendsto₁ : Prop :=
  ∀ V ∈ Fβ, ∃ U ∈ Fα, f '' U ⊆ V

/-
The first improvement we can make is to use preimage rather than image.
The containment `f '' U ⊆ V` is equivalent to `U ⊆ f ⁻¹' V` but the later
has better definitional equality, being equivalent to `∀ x ∈ U, f x ∈ V`
rather than the more clunky `∀ y, (∃ x ∈ U, f x = y) → y ∈ V`.
-/

variable {U : Set α} {V : Set β}

example : U ⊆ f⁻¹' V ↔ ∀ x ∈ U, f x ∈ V := by rfl
example : f '' U ⊆ V ↔ ∀ y, (∃ x ∈ U, f x = y) → y ∈ V := by rfl

#check Set.image_subset_iff

def Filter.Tendsto₂ : Prop :=
  ∀ V ∈ Fβ, ∃ U ∈ Fα, U ⊆ f ⁻¹' V

/-
The next improvement we can make is to notice that since `Fα` is closed
under supersets, it is equivalent to ask for `f ⁻¹' V ∈ Fα` directly.
-/

def Filter.Tendsto₃ : Prop :=
  ∀ V ∈ Fβ, f ⁻¹' V ∈ Fα

/-
At this point the definition is now definitionally equal to the
definition in mathlib, but there are still room for improvement.
-/

example : Filter.Tendsto f Fα Fβ ↔ Filter.Tendsto₃ f Fα Fβ := by rfl

/-
The next improvement to be had comes from noticing that the set of all
`V` with the property that `f ⁻¹' V ∈ Fα` is itself a filter on `Fα`.
This is called `Filter.map`.
-/

#check Filter.map

def Filter.Tendsto₄ (Fα : Filter α) (Fβ : Filter β) : Prop :=
  ∀ V ∈ Fβ, V ∈ Fα.map f

/-
The final improvement we can make is to notice that the condition
`∀ V ∈ F₁, V ∈ F₂` (i.e., `F₁.sets ⊆ F₂.sets`) defines an ordering on filters.
However, we write `F₂ ≤ F₁`, opposite from what you might initially expect.

The reason for this is the closure under supersets axiom. A filter with smaller
sets will necessarily contain more sets overall than a filter with larger sets.
-/

def Filter.Tendsto₅ (Fα : Filter α) (Fβ : Filter β) : Prop :=
  Fα.map f ≤ Fβ

/-
There is also a `Filter.comap`, and `Fα.map f ≤ Fβ` is actually equivalent
to `Fα ≤ Fβ.comap f`, but `Filter.comap` has worse definitional equality.
-/

#check Filter.map_le_iff_le_comap

/-
In general this pattern of having an ordering with a `.map` and a `.comap`
satisfying `X.map f ≤ Y ↔ X ≤ Y.comap f` is quite common in mathlib.
-/

#check Subgroup.map_le_iff_le_comap
#check Ideal.map_le_iff_le_comap
#check IntermediateField.map_le_iff_le_comap

/-
This abstraction also allows us to prove theorems without mentioning sets.
-/

example (hf : Filter.Tendsto f Fα Fβ) (hg : Filter.Tendsto g Fβ Fγ) :
    Filter.Tendsto (g ∘ f) Fα Fγ := by
  rw [Filter.Tendsto] at *
  grw [← Filter.map_map, hf, hg]

/-
One more important definition is `Filter.principal` which turns a
set into a filter by adding in all of the sets containing it.
And if `s ⊆ t`, then `Filter.principal s ≤ Filter.principal t`.
-/

#check Filter.principal
#check Filter.principal_mono

/-
There are also analogues of `∀` and `∃` with filters. They are denoted
`∀ᶠ` and `∃ᶠ` and mean "eventually forall" or "frequently exists".
-/

#check Filter.Eventually
#check Filter.Frequently

/-
`∀ᶠ x in F, P x` just means that the set `{x | P x}` lies in the filter `F`.

It is used in measure theory to say that a property holds "almost everywhere".
-/

#check MeasureTheory.ae
#check MeasureTheory.ae_lt_top

/-
`∃ᶠ x in F, P x` is defined as `¬ ∀ᶠ x in F, ¬ P x`. It roughly says that no
matter how far you go, you can continue to find `x` such that `P x` holds.
-/

example : ∃ᶠ n in Filter.atTop, Nat.Prime n := by
  rw [Filter.frequently_atTop]
  exact Nat.exists_infinite_primes
