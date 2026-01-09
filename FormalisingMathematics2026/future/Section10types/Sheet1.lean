import Mathlib.Tactic

/-!
Last time we talked about type theory in general

We saw a simple toy type theory, and showed how it can be used as a simple theorem prover for
a simplified version of propositional logic.

We saw how this type theory has a number of natural interpretations, or models: one of these
was constructive propositional logic (the Brouwer-Heyting-Kolmogorov interpretation), another was
sets and functions, and another was particular kinds of categories.

We discussed how this type theory can be extended to Martin-Löf Type Theory, which is an
extension of that type theory. A set-theoretic interpretation of this type theory is very
close to the set-theoretic universe that we're all used to. But MLTT has a number of other
interpretations, and some of these aren't set-theoretic at all.
As a consequence, some things which are true in the set theory model of MLTT (and true in the maths
you're all used to) are not provable in MLTT itself.
While the set-theoretic model of type theory has been our usual way of viewing it, it is not
the only way to think about MLTT, which can lead to confusion when some things which are true in
the set theory model don't work like you think they might.

Today we'll relate this back to Lean, and see what Lean has. We'll talk about the three ways of
making types in Lean: pi types, inductive types and quotient types.
We'll then talk about what axioms Lean additionally has on top of these, and why they're useful
to add.
As a result, Lean can be seen as a version of MLTT with _more axioms_ (even though this isn't
strictly true), which restricts the models which are valid. As such, the set theoretic model returns
to being the best way to think about what types in Lean are.

We'll also talk about universes, mention why these are necessary to have in Lean, and how they work.

We might talk about impredicativity and large elimination.

The third of these axioms - the axiom of choice - has a different status from the others. As such,
proving things in Lean + the first two axioms is usually pretty smooth, but choice can sometimes
add friction. It's still doable, and in some cases not noticably harder, but the distinction is
still present.
-/

-- In Martin-Löf Type Theory, this isn't provable:
-- It's called "Law of Excluded Middle"
theorem LEM {p : Prop} : p ∨ ¬ p := by sorry
-- Nor is this
-- It's called "Uniqueness of Identity Proofs"
theorem UIP {X : Type} {x y : X} {p q : x = y} : p = q := by rfl
-- but in Lean, both of these are true!
-- In fact, the second is true *by definition*, so the proof `rfl` will work.

-- The idea is that the type Prop, in the set theory model, corresponds to the set {∅, {•}}
-- But in MLTT in general, this might not even make sense
-- so Prop _could_ have other elements.

-- In Lean, we modify the underlying type theory so that UIP (and a few others like it) become true
-- and we add axioms so that LEM (and others like it) become provable.

-- So what is a type in Lean?
-- Just like a group is a set defining the group axioms, the type theory of Lean is a collection
-- which satisfies the axioms of LeanTT. But these are pretty complex and abstract to write down
-- so we'll just stick with our model of, a type is just a set, but they're all disjoint.
-- But now we have the deeper fact that while this is fair in Lean, it's not quite right in MLTT.

-- Let's now talk about the types of Lean
-- Pi types, inductive types, quotient types

-- Function types
variable {α β : Type}

#check α → β
-- Construction:
#check fun a : α ↦ (sorry : β)
-- Destruction:
example (f : α → β) (x : α) : β := f x
-- Computation:
example (f : α → β) (x : α) : (fun y ↦ f y) x = f x := rfl

-- Pi types
variable {α : Type} (Y : ℕ → Set α)
-- Y 0 : Set α
-- Y 1 : Set α
-- Y 2 : Set α
-- ...
-- We can then make a new type, whose elements are functions from the natural numbers to
-- ⋃ i : ℕ, Y i
-- i : ℕ, output of the function should be in Y i
-- A generalised function which takes in `i : I`, and returns a term of type `Y i`.
example : Type := Π i : ℕ, Y i
example : Type := (i : ℕ) → Y i

example : ∀ n : ℕ, n + n = 2 * n := by
  sorry

example : (n : ℕ) → n + n = 2 * n := by
  sorry

-- Inductive types
inductive Nat' : Type where
  | zero : Nat'
  | succ (n : Nat') : Nat'

#check ℕ

inductive True' : Prop where
  | intro : True'

inductive False' : Prop where

example (q : Prop) : False' → q := by
  intro h
  cases h

inductive And' (P Q : Prop) : Prop where
  | intro (hp : P) (hq : Q) : And' P Q

inductive Or' (P Q : Prop) : Prop where
  | inl (hp : P) : Or' P Q
  | inr (hq : Q) : Or' P Q

structure And'' (P Q : Prop) : Prop where
  left : P
  right : Q

#check And

-- inductive types generalise GADT

-- Quotient types
variable (α : Type) (R : α → α → Prop)
#check Quot R

#check Quot.mk

-- construction:
example : α → Quot R := Quot.mk R
-- Quot.sound
example (x y : α) (h : R x y) : Quot.mk R x = Quot.mk R y := Quot.sound h
-- destruction:
example (β : Type) (f : α → β) (h : ∀ x y : α, R x y → f x = f y) :
    Quot R → β := Quot.lift f h
-- computation rule:
example (β : Type) (f : α → β) (h : ∀ x y : α, R x y → f x = f y) (x : α) :
    Quot.lift f h (Quot.mk R x) = f x := rfl

-- propext
#check propext
#check Quot.sound
#check Classical.choice

-- Large elimination
inductive Nonempty' (α : Type) : Prop
  | intro (a : α) : Nonempty' α

theorem test1 : Nonempty' ℕ := ⟨1⟩
theorem test2 : Nonempty' ℕ := ⟨7⟩

-- If there's still time, get the list of sections from last year and discuss which ones to talk
-- about.
