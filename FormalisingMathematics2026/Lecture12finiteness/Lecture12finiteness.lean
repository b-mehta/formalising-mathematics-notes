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
# Lecture 12: Finiteness
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section

/-
There are many ways of expressing finiteness in Lean, but deciding between these
options requires understanding the sometimes subtle and technical differences.

One option is the predicate `Set.Finite` which asserts that a set is finite.
-/

#check Set.Finite

/-
You don't need to know how `Set.Finite` is defined since it comes with
well-developed API for all of the properties that you might expect.
-/

#check Set.finite_empty
#check Set.finite_singleton
#check Set.Finite.union
#check Set.Finite.subset

/-
In contrast to this "unbundled approach", there is also a "bundled approach"
where you work with the type `Finset α` of all finite set of elements of `α`.
-/

#check Finset

/-
Because this is now a type rather than a predicate, properties of
finiteness that were previously lemmas are now definitions or operations.
-/

example {α : Type*} : Finset α := ∅
example {α : Type*} (a : α) : Finset α := {a}
example {α : Type*} [DecidableEq α] (s t : Finset α) : Finset α := s ∪ t

/-
The `[DecidableEq α]` has to do with how `Finset α` is defined.

A `Finset` is a `Multiset` with no duplicates, and a `Multiset` is a `List` up
to permutation. This concrete definition allows operations to be computable.
For example, addition of multisets is given by concatenation of the lists.

But some operations like union of `Finset` or intersection of `Multiset`
require checking whether two numbers are equal. Whether this is possible
depends on whether the type `α` has an algorithm for checking equality.
This is captured by the data-carrying typeclass `[DecidableEq α]`.
For example, `ℕ` and `ℤ` have instances of `DecidableEq`, but `ℝ` does
not, because there is no algorithm for checking whether two (infinite)
equivalence classes of (infinite) Cauchy sequences are equal.

For formalizing mathematics, we usually do not care whether our operations
are compuable, so we can either assume `[DecidableEq α]` or use the tactic
`classical` inside a proof or write `open Classical` at the top of the file.

One other related quirk of `Finset` is that it has poor definitional equality.
For example, `x ∈ s ∩ t` is not definitionally equal to `x ∈ s ∧ x ∈ t`.
-/

example {α : Type*} [DecidableEq α] (s t : Finset α) (x : α) :
    x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := by
  exact Finset.mem_inter

/-
One prominent use of `Finset` is in writing down finite sums and products.
-/

#check Finset.sum
#check Finset.prod

/-
For example, with `Finset.range`, we can express basic summation identities.
-/

#check Finset.range

example (n : ℕ) :
    ∑ k ∈ Finset.range n, k ^ 3 = (∑ k ∈ Finset.range n, k) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => grind [Finset.sum_range_succ, Finset.sum_range_id_mul_two]

/-
There are also versions that work over an arbitrary type and use junk values
to handle to case where the function is not finitely supported.
-/

#check finsum
#check finprod

/-
There are also finiteness predicates on types themselves. The most standard
is the typeclass predicate `Finite` which asserts that a type is `Finite`.
-/

#check Finite

/-
Since `Finite` is a typeclass, many properties are instances that Lean will
synthesize automatically.
-/

example {α β : Type*} [Finite α] [Finite β] : Finite (α × β) := inferInstance

/-
There is also `Fintype` which expresses finiteness of a type by carrying
a `Finset` with the property that it contains every term of the type.
-/

#check Fintype

/-
In particular, `Fintype` is data-carrying, so a given type can have many
non-definitionally equal `Fintype` instances, leading to diamonds.

To avoid these diamonds, theorems should assume `[Finite α]` instead of
`[Fintype α]` unless the theorem statement itself requires `[Fintype α]`,
e.g., if the theorem involves summation over the type.
-/

example {α ι : Type*} [Semiring α] [Fintype ι] [DecidableEq ι] :
    ∑ i : ι, Matrix.single i i (1 : α) = 1 := by
  exact Matrix.sum_single_one

/-
There are also lots of options for talking about cardinality.
For natural number valued cardinalities of sets, there is
`Set.ncard` (with junk value `0`) and `Finset.card`.
-/

#check Set.ncard
#check Finset.card

/-
For natural number valued cardinalities of types, there is
`Nat.card` (with junk value `0`) and `Fintype.card`.
-/

#check Nat.card
#check Fintype.card

/-
Occasionally it is helpful to work in `ENat`, the natural numbers
with infinity, in which case there is `Set.encard` and `ENat.card`.
-/

#check Set.encard
#check ENat.card

/-
Finally, there is `Cardinal.mk` which returns a universe-dependent cardinal.
-/

#check Cardinal.mk
