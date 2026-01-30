/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Filters and limits

The motivation for filters was to unify different ways of talking about limits, so to finish this
story we need to know how to use this filter language to talk about limits!

The key ingredients we'll need for this story are:
* the order relation on filters
* our two special filters `atTop` and `nhds`
* the pushforward of a filter: `Filter.map`

We've seen the first two of these, so let's talk about the third.

Given a filter `f : Filter α` and a map `m : α → β`, there's a reasonably natural way of making
a `Filter β`: a set `s : Set β` will be in our filter if its preimage under `m` (which
is `m ⁻¹' s : Set α`) is in `f`. Let's make this and check it's a filter.
-/

namespace Filter

variable {α β : Type*}

def map' (f : Filter α) (m : α → β) : Filter β where
  sets := {s | m ⁻¹' s ∈ f}
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

/-
Now I can write down what it means for a function `f` to tend to a filter `l₂` under a filter `l₁`.
Then if `f : ℕ → ℝ`, `l₁ = atTop`, and `l₂ = nhds 0`, I claim `Tendsto f l₁ l₂` means the same as
what we'd informally write as $lim_{x → ∞} f(x) = 0$.

Similarly, if `l₁ = nhds a` and `l₂ = nhds b`, then `Tendsto f l₁ l₂` will be that `f(x) → b` as
`x → a`.
-/

def Tendsto' (f : α → β) (l₁ : Filter α) (l₂ : Filter β) : Prop :=
  l₁.map f ≤ l₂

-- That felt too easy.
-- Let's make sure it does actually work.

#check Metric.tendsto_nhds_nhds
#check Metric.tendsto_atTop

lemma tendsto_atTop_atTop_iff {α β : Type*} [Nonempty α] [LinearOrder α] [LinearOrder β]
    (f : α → β) :
    Tendsto f atTop atTop ↔ ∀ M : β, ∃ N : α, ∀ a : α, N ≤ a → M ≤ f a := by
  rw [tendsto_atTop_atTop]

/-
With filters at hand, it's now really easy to talk about something being true "sufficiently close"
to a point, or for all "sufficiently large" numbers. Specifically, I can say that `p : ℕ → Prop`
is true for all sufficiently large `n` if the set of places where it's true `{n | p n}` is in the
`atTop` filter.
This has notation: ∀ᶠ n in atTop, p n, and it's called "eventually" or "eventually forall".
-/

example {p : ℕ → Prop} : (∀ᶠ n in atTop, p n) ↔ ∃ N, ∀ n ≥ N, p n := by
  rw [eventually_atTop]

/-
Now's a good time to mention that Lean usually doesn't like the `≥` symbol: most lemmas will be
stated in terms of `≤`, and some automation will work best with `≤`. So mathlib has a style
convention to use `≤` everywhere: it's a bit weird, I know! That means saying that `n > 1` would
usually be written as `1 < n`.
The exception to this rule is examples like the one above, where I'm using `∀ n ≥ N` notation:
if I were to write this as `∀ N ≤ n`, then it'd more sensibly mean that I'm quantifying over `N`
with fixed `n`, so `≥` is allowed to make `∀ n ≥ N` read nicely.
The `simp` tactic will usually do this lemma to make everything into a `≤`:
-/

example {a b : ℝ} : a ≥ b ↔ b ≤ a := by rw [ge_iff_le]

/-
The really useful part here is the intersection axiom for filters. In the context of eventually,
this says that if `p` is eventually true along the filter, and `q` is eventually true along the same
filter then `p ∧ q` is eventually true along the filter too.
-/

example {p q : ℕ → Prop} (hp : ∀ᶠ n in atTop, p n) (hq : ∀ᶠ n in atTop, q n) :
    ∀ᶠ n in atTop, p n ∧ q n :=
  hp.and hq

/-
In practice, we often use the `filter_upwards` tactic to handle things like this. Look at the goal
state after the `filter_upwards` here: it should be very easy!
Play around with what happens if you remove everything after the `with`, and then if you remove the
`hp` or `hq`.
The idea of `filter_upwards` is that if you're trying to prove something is eventually true, and
you know that other things are eventually true, it lets you safely assume those things are generally
true, and deduce that what you want holds too.
-/

example {p q : ℕ → Prop} (hp : ∀ᶠ n in atTop, p n) (hq : ∀ᶠ n in atTop, q n) :
    ∀ᶠ n in atTop, p n ∧ q n := by
  filter_upwards [hp, hq] with n hpn hqn
  sorry

example {x ε : ℝ} (hε : 0 < ε) : ∀ᶠ y in nhds x, |y - x| < ε := by
  exact eventually_abs_sub_lt x hε

example {N : ℕ} : ∀ᶠ n in atTop, N ≤ n := by
  exact eventually_ge_atTop N

example {p q : ℕ → Prop} {N M : ℕ} (hp : ∀ n ≥ N, p n) (hq : ∀ n ≥ M, q n) :
    ∀ᶠ n in atTop, p n ∧ q n := by
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop M] with n hN hM
  sorry

example {p q : ℕ → Prop} {N M : ℕ} (hp : ∀ n ≥ N, p n) (hq : ∀ n ≥ M, q n) :
    ∃ N', ∀ n ≥ N', p n ∧ q n := by
  rw [← eventually_atTop]
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop M] with n hN hM
  aesop

-- I don't need to use max any more!

/-
Finally, as promised, here's a really short proof about what happens when you add convergent
sequences.
-/
example {f g : ℕ → ℝ} {a b : ℝ} (hf : Tendsto f atTop (nhds a)) (hg : Tendsto g atTop (nhds b)) :
    Tendsto (fun n ↦ f n + g n) atTop (nhds (a + b)) :=
  hf.add hg

end Filter

-- For more about Filters and Topology, see
-- https://leanprover-community.github.io/mathematics_in_lean/C10_Topology.html
