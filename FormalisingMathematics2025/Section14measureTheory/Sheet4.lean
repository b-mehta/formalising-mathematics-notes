/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jason Kexing Ying, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Order.CompletePartialOrder
import Mathlib

-- note to self: surely too much
/-

# Measures

Recall that Lean calls a space equipped with
a sigma algebra a "MeasurableSpace". We will go with this language
and call sets in the sigma algebra "measurable sets".

Given a measurable space, a *measure* on the measurable space is a function from
the measurable sets to `[0,∞]` which is countably additive (i.e.,
the measure of a countable disjoint union of measurable sets is the sum of the measures).
This is not the *definition* of a measure in Lean, but it is mathematically equivalent to the
definition.

For what it's worth, the actual definition of a measure in Lean is this: an `OuterMeasure`
on a type `α` is this:

```lean
structure OuterMeasure (α : Type*) where
  measureOf : Set α → ℝ≥0∞
  empty : measureOf ∅ = 0
  mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  iUnion_nat : ∀ s : ℕ → Set α, measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)
```

So it attaches an element of `[0,∞]` to *every* subset of α, satisfying some natural axioms;
note in particular it is countably *sub*additive, meaning that the measure of a countable
union of open sets, even if they're pairwise disjoint, is only assumed to be at most the sum of the measures.

And if `α` has a measurable space structure then a measure on `α` is an outer measure satisfying
some axioms, which boil down to "the restriction of the outer measure is a measure on the measurable
sets, and the extension of this measure to an outer measure agrees with the outer measure we started with".
The advantage of doing it this way is that given a measure, we can evaluate it on *any* subset
(getting the outer measure of the subset) rather than having to supply a proof that the subset
is measurable. This coincides with Lean's "make functions total" philosophy (the same reason that 1/0=0).

-/

section Section13Sheet3

open Filter

open scoped NNReal ENNReal MeasureTheory BigOperators Topology

-- note to self: removed `probability_theory`
namespace MeasureTheory

-- Let Ω be a set equipped with a sigma algebra.
variable {Ω : Type} [MeasurableSpace Ω]

-- Now let's add a measure `μ` on `Ω`
variable {μ : Measure Ω}

/-
Try proving the following:
-/
example (S T : Set Ω) (hS : μ S ≠ ∞) (hT : MeasurableSet T) :
    μ (S ∪ T) = μ S + μ T - μ (S ∩ T) := sorry

/-!
## Measurable functions

So far we've worked in the space `Ω` though with all mathematical objects, we
want to map between them. In measure theory, the correct notion of maps is
measurable functions. If you have seen continuity in topology, they are quite
similar, namely, a function `f` between two measurable spaces is said to be
measurable if the preimages of all measurable sets along `f` is measurable.
-/


/-
*Remark*: while proving the above, you might have noticed I've added the
condition `hS` (think about what is a + ∞ - ∞). In particular, subtraction in
extended non-negative reals (`ℝ≥0∞`) might not be what you expect,
e.g. 1 - 2 = 0 in `ℝ≥0∞`. For this reason, the above lemma is better phrased as
`μ (S ∪ T) + μ (S ∩ T) = μ S + μ T` for which we can omit the condition `hS`.
-/
/-
If you go to the definition of measurable you will find what you expect.
However, of course, measure theory in Lean is a bit more complicated. As we
shall see, in contrast to maths, there are 3 additional notions of measurability
in mathlib. These are:
- `AEMeasurable`
- `StronglyMeasurable`
- `AEStronglyMeasurable`
The reasons for their existence is technical but TLDR: `ae_foo f` is the predicate
that `f` is almost everywhere equal to some function satisfying `foo` (see the
a.e. filter section) while `StronglyMeasurable f` is saying `f` is the limit
of a sequence of simple functions.

Alongside `measurable`, we also see them quite often in the mathlib, although
all you have to know is in most cases (range is metrizable and second-countable),
`Measurable` and `StronglyMeasurable` are equivalent.
-/
example : Measurable (id : Ω → Ω) := sorry

example {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (f : X → Y) (g : Y → Z) (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) := sorry

/-!
## Integration

One of the primary motivations of measure theory is to introduce a more
satisfactory theory of integration. If you recall the definition of the
Darboux-Riemann integral, we cannot integrate the indicator function of
`ℚ ∩ [0, 1]` despite, intuitively, the set of rationals in the unit interval
is much "smaller" (rationals is countable while the irrationals are not.
In contrast, measure theory allows us to construct the Lebesgue integral
which can deal with integrals such as this one.

Lean uses a even more general notion of integration known as Bochner integration
which allows us to integrate Banach-space valued functions. Its construction
is similar to the Lebesgue integral.

Read page 5-6 of https://arxiv.org/pdf/2102.07636.pdf
if you want to know the details.
-/


-- Suppose now `X` is another measurable space
variable {X : Type} [MeasurableSpace X]

-- and suppose it's also a Banach space (i.e. a vector space and a complete metric space)
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

-- If `f : Ω → X` is a function, then the integral of `f` is written as
-- `∫ x, f x ∂μ`. If you want to integrate over the set `s : set Ω` then write
-- `∫ x in s, f x ∂μ`.
-- Try looking in mathlib
example {f g : Ω → X} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := sorry

example (a : X) (s : Set Ω) : ∫ _ in s, a ∂μ = (μ s).toReal • a := sorry

-- Harder
example
    {f : Ω → ℝ} (hf : Measurable f)
    (hint : Integrable f μ) (hμ : 0 < μ {ω | 0 < f ω}) :
    (0 : ℝ) < ∫ ω in {ω | 0 < f ω}, f ω ∂μ := by
  sorry

/-!
## ae filter

Now we have come to a very important section of working with measure theory
in Lean.

In measure theory we have a notion known as almost everywhere (a.e.). In
probability this is known as almost surely however we will stick with
almost everywhere in this project. Namely, a predicate `P` on `Ω` is said to
be true almost everywhere if the set for which `P` holds is co-null, i.e.
`μ {ω : Ω | P ω}ᶜ = 0`.

As examples, we say:
- given functions `f, g`, `f` equals `g` a.e. if `μ {ω : Ω | f ω ≠ g ω} = 0`;
- `f` is less equal to `g` a.e. if `μ {ω : Ω | ¬ f ω ≤ g ω} = 0` etc.

Often, showing that a property holds a.e. is the best we can do in
measure/probability theory.

In Lean, the notion of a.e. is handled by the `Measure.ae` filter.
Let's construct that filter ourselves.
-/


/-
*Remark* It's a common myth that Lebesgue integration is strictly better than
the Darboux-Riemann integral. This is true for integration on bounded intervals
though it is not true when considering improper integrals. A common example
for this is, while `∫ x in [0, ∞), sin x / x dx` is Darboux-Riemann integrable
(in fact it equals `π / 2`) it is not Lebesgue integrable as
`∫ x in [0, ∞), |sin x / x| dx = ∞`.
-/
example (X : Type) [MeasurableSpace X] (μ : Measure X) : Filter X := sorry

-- say `f` and `g` are measurable functions `Ω → X`
variable (f g : Ω → X)

-- The following is a proposition that `f` and `g` are almost everywhere equal
-- it's **not** a proof that `f` and `g` are a.e. equal but simply a statement
example : Prop :=
  ∀ᵐ ω ∂μ, f ω = g ω

-- Here's another example on how to state `f` is almost everywhere less equal
-- than `g`
-- To be able to formulate this we need a notion of inequality on `X` so we
-- will add the `LE` instance on `X`, i.e. equip `X` with a inequality
example [LE X] : Prop :=
  ∀ᵐ ω ∂μ, f ω ≤ g ω

-- Since the above two cases come up quite often, there are special notations
-- for them. See if you can guess what they mean
example : Prop :=
  f =ᵐ[μ] g

example [LE X] : Prop :=
  f ≤ᵐ[μ] g

-- In general, if `P : Ω → Prop` is a predicate on `Ω`, we write `∀ᵐ ω ∂μ, P ω`
-- for the statement that `P` holds a.e.
example (P : Ω → Prop) : Prop :=
  ∀ᵐ ω ∂μ, P ω

-- Sanity check: the above notation actually means what we think
example (P : Ω → Prop) : (∀ᵐ ω ∂μ, P ω) ↔ μ ({ω | P ω}ᶜ) = 0 := by rfl

-- Here's a more convoluted example. See if you can figure what it means
example (f : ℕ → Ω → ℝ) (s : Set Ω) :=
  ∀ᵐ ω ∂μ.restrict s, ∃ l : ℝ, Tendsto (fun n ↦ f n ω) atTop (𝓝 l)

-- Now to do some exercises: you will need to dig into the source code to see
-- what the definitions are and search for helpful lemmas
-- *Hint*: try out the `measurability` tactic. It should be able to solve simple
-- goals of the form `MeasurableSet s` and `Measurable f`
example (s : Set Ω) (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ ω ∈ s, f ω = g ω) : f =ᵐ[μ.restrict s] g := sorry

example (f g h : Ω → ℝ)
    (h₁ : f ≤ᵐ[μ] g) (h₂ : f ≤ᵐ[μ] h) : 2 * f ≤ᵐ[μ] g + h := sorry

example (f g : Ω → ℝ) (h : f =ᵐ[μ] g) (hg : ∀ᵐ ω ∂μ, 2 * g ω + 1 ≤ 0) :
    ∀ᵐ ω ∂μ, f ω ≤ -1 / 2 := sorry

example (f g : ℕ → Ω → ℝ) (a b : ℝ)
    (hf : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 a))
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 b)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω + g n ω) atTop (𝓝 (a + b)) := sorry

/-
I hope that you found the above examples slightly annoying, especially the
third example: why can't we just `rw h`?! Of course, while we often do do so on
paper, rigorously, such a rewrite require some logic. Luckily, what we normally
do on paper is most often ok and we would like to do so in Lean as well. While
we can't directly rewrite almost everywhere equalities, we have the next best
thing: the `filter_upwards` tactic. See the tactic documentation here:
https://leanprover-community.github.io/mathlib_docs/tactics.html#filter_upwards

The `filter_upwards` tactic is much more powerful than simply rewriting a.e.
equalities and is helpful in many situations, e.g. the above second, third
and fourth examples are all easily solvable with this tactic. Let us see how
it works in action.
-/
-- Hover over each line and see how the goal changes
example (f₁ f₂ g₁ g₂ : Ω → ℝ)
    (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ := by
  filter_upwards [h₁, h₂]
  intro ω hω₁ hω₂
  exact add_le_add hω₁ hω₂

-- Here's an even shorter proof using additional parameters of `filter_upwards`
example (f₁ f₂ g₁ g₂ : Ω → ℝ) (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ := by
  filter_upwards [h₁, h₂] with ω hω₁ hω₂ using add_le_add hω₁ hω₂

/-
Intuitively, what `filter_upwards` is doing is simply exploiting the fact that
the intersection of two full measure sets (i.e. complements are null) is also
a set of full measure. Thus, it suffices to work in their intersection instead.

Now, try the above examples again using the `filter_upwards` tactic.
-/
end MeasureTheory

end Section13Sheet3

open MeasureTheory Measure EMetric NNReal ENNReal

/-- If the restrictions of a measure to countably many open sets covering the space are
outer regular, then the measure itself is outer regular. -/
lemma of_restrict {ι α : Type*} [Nonempty ι] [Countable ι] [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} (s : ι → Set α)
    (h : ∀ n, OuterRegular (μ.restrict (s n))) (h' : ∀ n, IsOpen (s n))
    (h'' : Set.univ ⊆ ⋃ n, s n) :
    OuterRegular μ := by
  obtain ⟨f, hf⟩ := exists_surjective_nat ι
  let s' : ℕ → Set α := fun i ↦ s (f i)
  apply MeasureTheory.Measure.OuterRegular.of_restrict (s := s')
  · simp [s', h]
  · simp [s', h']
  · refine h''.trans ?_
    simp only [Set.iUnion_subset_iff, s']
    intro i
    obtain ⟨j, hj, rfl⟩ := hf i
    exact Set.subset_iUnion (fun z ↦ s (f z)) j

lemma iSup_nonempty_pos {E : Type*} [PseudoEMetricSpace E] {A : Set E} {s : ℝ} (hs : 0 < s) :
    ⨆ (h : A.Nonempty), diam A ^ s = diam A ^ s := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp [zero_rpow_of_pos hs]
  simp [hA]

lemma ENNReal.div_div_cancel' {a b : ℝ≥0∞} (h₀ : a = 0 → b = 0) (h₁ : a = ∞ → b = 0) :
    a / (a / b) = b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [h₀]
  obtain rfl | ha' := eq_or_ne a ∞
  · simp [h₁, top_div_of_lt_top]
  rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (Or.inr ha') (Or.inr ha),
    ENNReal.div_mul_cancel ha ha']

lemma ENNReal.div_div_cancel {a b : ℝ≥0∞} (h₀ : a ≠ 0) (h₁ : a ≠ ∞) :
    a / (a / b) = b :=
  ENNReal.div_div_cancel' (by simp [h₀]) (by simp [h₁])

lemma le_of_forall_mul_le {a b : ℝ≥0∞} (h : ∀ ε : ℝ≥0, 1 < ε → a ≤ b * ε) : a ≤ b := by
  obtain rfl | ha := eq_or_ne a ⊤
  · have : b * 2 = ⊤ := by
      specialize h 2
      norm_num at h
      assumption
    by_contra! hb
    exact ENNReal.mul_ne_top hb.ne (by simp) this
  apply le_of_forall_pos_nnreal_lt
  intro r hr hra
  generalize hε : a / r = ε
  have hε' : ε ≠ ⊤ := by
    rw [← hε]
    exact (ENNReal.div_lt_top ha (by positivity)).ne
  lift ε to ℝ≥0 using hε'
  have hε' : 1 < ε := by
    suffices (1 : ℝ≥0∞) < ε by simpa
    rwa [← hε, ENNReal.lt_div_iff_mul_lt (by simp) (by simp), one_mul]
  have : a / ε = r := by
    rw [← hε, ENNReal.div_div_cancel _ ha]
    exact (hra.trans_le' (by simp)).ne'
  rw [← this]
  apply ENNReal.div_le_of_le_mul
  exact h ε hε'

variable {X : Type*} [EMetricSpace X]

noncomputable def deltaHausdorffWith (p : Set (Set X)) (d : ℝ) (r : ℝ≥0∞) (S : Set X) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set X) (_ : S ⊆ ⋃ n, t n) (_ : ∀ n, diam (t n) ≤ r) (_ : ∀ n, t n ∈ p),
    ∑' n, ⨆ _ : (t n).Nonempty, diam (t n) ^ d

lemma deltaHausdorffWith_antitone_prop {r : ℝ≥0∞} {d : ℝ} {S : Set X} :
    Antitone (deltaHausdorffWith · d r S) :=
  fun _ _ hp ↦ iInf₂_mono fun U hU ↦ iInf₂_mono' fun hU' hU'' ↦ ⟨hU', fun n ↦ hp (hU'' n), le_rfl⟩

lemma deltaHausdorffWith_antitone {p : Set (Set X)} {d : ℝ} {S : Set X} :
    Antitone (deltaHausdorffWith p d · S) :=
  fun _ _ hr ↦ iInf₂_mono fun U hU ↦ iInf₂_mono' fun hU' hU'' ↦
    ⟨fun n ↦ (hU' n).trans hr, hU'', le_rfl⟩

open Filter Topology

lemma iSup₂_nnreal_deltaHausdorffWith (p : Set (Set X)) (d : ℝ) (S : Set X) :
    ⨆ (r : ℝ≥0) (_ : 0 < r), deltaHausdorffWith p d r S =
      ⨆ (r : ℝ≥0∞) (_ : 0 < r), deltaHausdorffWith p d r S := by
  refine le_antisymm (iSup₂_mono' ?_) (iSup₂_mono' ?_)
  · intro r hr
    exact ⟨r, by simpa⟩
  · intro r hr
    obtain rfl | hr' := eq_or_ne r ⊤
    · refine ⟨1, by simp, ?_⟩
      apply deltaHausdorffWith_antitone
      simp
    lift r to ℝ≥0 using hr'
    exact ⟨r, by simpa using hr⟩

lemma deltaHausdorffWith_isClosed (d : ℝ) (S : Set X) (r : ℝ≥0∞) :
    deltaHausdorffWith {U | IsClosed U} d r S = deltaHausdorffWith Set.univ d r S := by
  refine le_antisymm (iInf₂_mono' fun U hU ↦ ?_) (deltaHausdorffWith_antitone_prop (by simp))
  let U' (n : ℕ) : Set X := closure (U n)
  have hU' : S ⊆ ⋃ n, U' n := hU.trans (Set.iUnion_mono (by simp [U', subset_closure]))
  use U', hU'
  simp [U']

lemma Metric.thickening_nonempty_iff_of_pos
    {X : Type*} [PseudoEMetricSpace X] {ε : ℝ} {S : Set X} (hε : 0 < ε) :
    (thickening ε S).Nonempty ↔ S.Nonempty := by
  constructor
  · intro h
    contrapose! h
    simp [h]
  · intro h
    exact h.mono (Metric.self_subset_thickening hε _)

lemma Metric.thickening_nonempty_iff {X : Type*} [PseudoEMetricSpace X] {ε : ℝ} {S : Set X} :
    (thickening ε S).Nonempty ↔ 0 < ε ∧ S.Nonempty := by
  obtain hε | hε := lt_or_le 0 ε
  · simp [hε, thickening_nonempty_iff_of_pos]
  · simp [hε.not_lt, Set.not_nonempty_iff_eq_empty, thickening_of_nonpos hε]

lemma exists_isOpen_diam {E : Set X} (hE : E.Nontrivial) {δ : ℝ≥0} (hδ : 1 < δ) :
    ∃ U, E ⊆ U ∧ IsOpen U ∧ diam U ≤ δ * diam E := by
  have hδ₀ : δ ≠ 0 := by positivity
  obtain hE | hE := eq_or_ne (diam E) ⊤
  · use Set.univ
    simp [hE, hδ₀]
  lift diam E to ℝ≥0 using hE with dE hdE
  have hdE' : 0 < dE := by rwa [← EMetric.diam_pos_iff, ← hdE, ENNReal.coe_pos] at hE
  let ε : ℝ≥0 := (δ - 1) / 2 * dE
  have hε : 0 < ε := by
    have : 0 < δ - 1 := by simpa
    positivity
  refine ⟨Metric.thickening ε E, Metric.self_subset_thickening (by simpa) _,
    Metric.isOpen_thickening, ?_⟩
  calc diam (Metric.thickening ε E) ≤ diam E + 2 * ε := Metric.ediam_thickening_le _
    _ = dE + 2 * ε := by rw [hdE]
    _ = dE + 2 * ↑((δ - 1) / 2 * dE) := rfl
  norm_cast
  rw [← mul_assoc, ← one_add_mul, mul_div_cancel₀ _ (by simp), add_tsub_cancel_of_le hδ.le]

lemma deltaHausdorffWith_isOpen (S : Set X) (d : ℝ) (r : ℝ≥0) (ε : ℝ≥0)
    (hr : 0 < r) (hε : 1 < ε) (hd : 0 ≤ d) :
    deltaHausdorffWith {U | IsOpen U} d (ε * r) S ≤ ε ^ d * deltaHausdorffWith Set.univ d r S := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ν hν h
  have hε₀ : ε ≠ 0 := by positivity
  simp only [deltaHausdorffWith, mul_iInf_of_ne (a := ε ^ d) (by simp [hε₀]) (by simp [hε₀]),
    iInf_add, ← ENNReal.tsum_mul_left, ENNReal.mul_iSup]
  refine iInf₂_mono' fun U hU ↦ ?_
  obtain ⟨ν', hν', h'ν'⟩ := ENNReal.exists_pos_sum_of_countable (ε := ν) (by simp [hν.ne']) ℕ
  have U' (n : ℕ) : ∃ V, U n ⊆ V ∧ IsOpen V ∧ (V.Nonempty → (U n).Nonempty) ∧
      (diam V ≤ ε * diam (U n) ∨ diam (U n) = 0 ∧ diam V ≤ min (ε * r) (ν' n ^ d⁻¹)) := by
    obtain h' | h' := (U n).eq_empty_or_nonempty
    · use ∅
      simp [h']
    obtain ⟨x, hx⟩ | h' := h'.exists_eq_singleton_or_nontrivial
    · refine ⟨EMetric.ball x (min (ε * r) (ν' n ^ d⁻¹) / 2), ?_, ?_, by simp [hx], Or.inr ?_⟩
      · rw [hx, Set.singleton_subset_iff]
        apply mem_ball_self
        have : 0 < ν' n ^ d⁻¹ := NNReal.rpow_pos (hν' n)
        refine ENNReal.div_pos ?_ (by simp)
        positivity
      · exact isOpen_ball
      · simp only [hx, diam_singleton, true_and]
        refine diam_ball.trans_eq ?_
        rw [ENNReal.mul_div_cancel (by simp) (by simp)]
    obtain ⟨V, hV, hV', hV''⟩ := exists_isOpen_diam h' hε
    exact ⟨V, hV, hV', by simp [h'.nonempty], Or.inl hV''⟩
  choose V hUV hVopen hVne hVdiam using U'
  use V, hU.trans (Set.iUnion_mono hUV)
  refine iInf₂_mono' fun h'U h''U ↦ ?_
  have hVdiam_r (n : ℕ) : diam (V n) ≤ ε * r := by
    obtain h | h := hVdiam n
    · exact h.trans (mul_le_mul_left' (h'U n) ε)
    · exact h.2.trans (by simp)
  use hVdiam_r, hVopen
  have h₁ : ∑' (i : ℕ), ((⨆ (_ : (U i).Nonempty), ε ^ d * diam (U i) ^ d) + ν' i) ≤
      (∑' (i : ℕ), ⨆ (_ : (U i).Nonempty), ε ^ d * diam (U i) ^ d) + ν := by
    rw [ENNReal.tsum_add]
    gcongr
  refine h₁.trans' <| ENNReal.tsum_le_tsum fun n ↦ ?_
  simp only [iSup_le_iff]
  intro hn
  simp only [hVne _ hn, iSup_pos]
  obtain h | ⟨h, h'⟩ := hVdiam n
  · calc diam (V n) ^ d ≤ (ε * diam (U n)) ^ d := by gcongr
      _ = ε ^ d * diam (U n) ^ d := by rw [ENNReal.mul_rpow_of_nonneg _ _ hd]
      _ ≤ _ := le_self_add
  · obtain rfl | hd := hd.eq_or_lt
    · simp
    calc diam (V n) ^ d ≤ (min (ε * r) (ν' n ^ d⁻¹)) ^ d := by gcongr
      _ ≤ (ν' n ^ d⁻¹ : ℝ≥0) ^ d := by gcongr; exact min_le_right _ _
      _ = ν' n := by
        rw [ENNReal.coe_rpow_of_nonneg, ENNReal.rpow_inv_rpow hd.ne']
        positivity
      _ ≤ _ := le_add_self

variable [MeasurableSpace X] [BorelSpace X]

lemma hausdorffMeasure_eq_iSup₂_deltaHausdorffWith {d : ℝ} {S : Set X} :
    μH[d] S = ⨆ (r : ℝ≥0∞) (_ : 0 < r), deltaHausdorffWith Set.univ d r S := by
  simp only [hausdorffMeasure_apply, deltaHausdorffWith, Set.mem_univ, implies_true, iInf_pos]

lemma hausdorffMeasure_eq_iSup₂_deltaHausdorffWith_isOpen {d : ℝ} {S : Set X} (hd : 0 ≤ d) :
    μH[d] S = ⨆ (r : ℝ≥0∞) (_ : 0 < r), deltaHausdorffWith {U | IsOpen U} d r S := by
  rw [hausdorffMeasure_eq_iSup₂_deltaHausdorffWith,
    ← iSup₂_nnreal_deltaHausdorffWith, ← iSup₂_nnreal_deltaHausdorffWith]
  refine le_antisymm (iSup₂_mono fun r hr ↦ deltaHausdorffWith_antitone_prop (by simp)) ?_
  obtain rfl | hd := hd.eq_or_lt
  · refine iSup₂_mono' fun r hr ↦ ?_
    refine ⟨r / 2, by positivity, ?_⟩
    convert deltaHausdorffWith_isOpen S 0 (r / 2) 2 (by positivity) (by simp) le_rfl using 2
    · norm_cast
      rw [mul_div_cancel₀ _ (by simp)]
    simp
  apply le_of_forall_mul_le
  intro ε hε
  rw [mul_comm]
  simp only [ENNReal.mul_iSup]
  refine iSup₂_mono' fun r hr ↦ ?_
  have h₂ : 0 < ε ^ (-d⁻¹) * r := mul_pos (NNReal.rpow_pos (by positivity)) hr
  use ε ^ (-d⁻¹) * r, h₂
  convert deltaHausdorffWith_isOpen S d _ (ε ^ d⁻¹) h₂ (one_lt_rpow hε (by positivity)) hd.le
  · norm_cast
    rw [← mul_assoc, ← NNReal.rpow_add (by positivity)]
    simp
  · rw [ENNReal.coe_rpow_of_nonneg _ (by positivity), ENNReal.rpow_inv_rpow hd.ne']

lemma tendsto_deltaHausdorffWith_isOpen_hausdorffMeasure {d : ℝ} {S : Set X} (hd : 0 ≤ d) :
    Tendsto (deltaHausdorffWith {U | IsOpen U} d · S) (𝓝[>] 0) (𝓝 (μH[d] S)) := by
  rw [hausdorffMeasure_eq_iSup₂_deltaHausdorffWith_isOpen hd]
  convert deltaHausdorffWith_antitone.tendsto_nhdsGT 0
  rw [sSup_image]
  simp

open Topology
lemma iSup₂_eq_liminf {α β : Type*}
    [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [CompleteLattice β]
    (a : α) (hb : ∃ b, a < b) {f : α → β} (hf : Antitone f) :
    ⨆ r > a, f r = Filter.liminf f (𝓝[>] a) := by
  rw [(nhdsGT_basis_of_exists_gt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr ↦ ?_) (iSup₂_mono' fun r hr ↦ ?_)
  · use r, hr
    apply le_iInf
    simp only [Set.mem_Ioo, le_iInf_iff, and_imp]
    intro i hi0 hir
    exact hf hir.le
  · obtain ⟨b, hb⟩ := exists_between hr
    use b, hb.1
    exact iInf₂_le b hb


open Filter

theorem asdf {s : ℝ} (hs : 0 ≤ s) (E : Set X) :
    ∃ G : Set X, IsGδ G ∧ E ⊆ G ∧ μH[s] G = μH[s] E := by
  have h₁ : μH[s] E = ⊤ ∨ μH[s] E < ⊤ := by rw [← le_iff_eq_or_lt]; simp
  obtain h₁ | h₁ := h₁
  · exact ⟨Set.univ, by simp, by simp, le_antisymm (by rw [h₁]; simp) (measure_mono (by simp))⟩
  obtain ⟨φ, h₁φ, h₂φ, h₃φ⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ≥0∞) < 1 by norm_num)
  have h₄φ : Tendsto φ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_mono_right
      (Set.range_subset_iff.2 (by simp_all)) (tendsto_nhdsWithin_range.2 h₃φ)
  have hc (i : ℕ) : ∃ (U : ℕ → Set X) (hU : E ⊆ ⋃ j, U j)
      (hU' : ∀ j, diam (U j) ≤ φ i) (hU'' : ∀ j, IsOpen (U j)),
      ∑' j, ⨆ (_ : (U j).Nonempty), diam (U j) ^ s <
        deltaHausdorffWith {U | IsOpen U} s (φ i) E + φ i := by
    have h₂ :
        deltaHausdorffWith {U | IsOpen U} s (φ i) E <
          deltaHausdorffWith {U | IsOpen U} s (φ i) E + φ i := by
      apply ENNReal.lt_add_right _ _
      · rw [← lt_top_iff_ne_top]
        refine h₁.trans_le' ?_
        rw [hausdorffMeasure_eq_iSup₂_deltaHausdorffWith_isOpen hs]
        exact le_iSup₂ (α := ℝ≥0∞) _ (by simp_all)
      · simp only [ne_eq, ENNReal.coe_eq_zero, (h₂φ i).1.ne', not_false_eq_true]
    conv_lhs at h₂ =>
      simp only [deltaHausdorffWith]
    simp only [iInf_lt_iff, Set.mem_setOf_eq] at h₂
    exact h₂
  choose U hCov hDiam hOpen hU using hc
  let G : Set _ := ⋂ i, ⋃ j, U i j
  have hEG : E ⊆ G := Set.subset_iInter hCov
  have h₁ (i : ℕ) : deltaHausdorffWith {U | IsOpen U} s (φ i) G <
      deltaHausdorffWith {U | IsOpen U} s (φ i) E + φ i := by
    rw [deltaHausdorffWith]
    simp only [iInf_lt_iff]
    exact ⟨U i, Set.iInter_subset _ _, hDiam i, hOpen i, hU i⟩
  refine ⟨G, ?_, hEG, ?_⟩
  · apply IsGδ.iInter_of_isOpen
    intro i
    apply isOpen_iUnion
    intro j
    exact hOpen i j
  refine le_antisymm ?_ (measure_mono hEG)
  simpa using le_of_tendsto_of_tendsto'
    ((tendsto_deltaHausdorffWith_isOpen_hausdorffMeasure hs).comp h₄φ)
    (((tendsto_deltaHausdorffWith_isOpen_hausdorffMeasure hs).comp h₄φ).add h₃φ) (fun i ↦ (h₁ i).le)
