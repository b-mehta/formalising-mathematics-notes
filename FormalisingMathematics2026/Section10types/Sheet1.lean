import Mathlib.Tactic

/-!
Today we'll talk a little about the type theory of Lean. We'll talk about the three ways of making
types in Lean: pi types, inductive types and quotient types.

We'll also talk about universes, mention why these are necessary to have in Lean, and how they work.

We'll then talk about what axioms Lean additionally has on top of these, and why they're useful
to add.

The third of the axioms - the axiom of choice - has a different status from the others. As such,
proving things in Lean + the first two axioms is usually pretty smooth, but choice can sometimes
add friction. It's still doable, and in some cases not noticably harder, but the distinction is
still present.
-/


-- So what is a type in Lean?
-- Just like a group is a set defining the group axioms, the type theory of Lean is a collection
-- which satisfies the axioms of LeanTT. But these are pretty complex and abstract to write down
-- so we'll just stick with our model of, a type is just a set, but they're all disjoint.

-- Let's now talk about the types of Lean
-- Pi types, inductive types, quotient types

-- # Pi types
-- We've already seen function types, when we talked about sequences, and also about implication
variable {α β : Type}

-- If α and β are types, then we can build a new type representing the functions from α to β
#check α → β
-- Here's how we can construct an element of this type (ie build a function).
-- This is called the construction rule
#check fun a : α ↦ (sorry : β)
-- And here's what we can do with an element of this type (ie use a function).
-- This is called the destruction rule, or eliminator
example (f : α → β) (x : α) : β := f x
-- The pair of construction and destruction rules work nicely together: in particular if you
-- construct then destruct a function, you just get the original function
example (f : α → β) (x : α) : (fun y ↦ f y) x = f x := rfl

-- In fact, function types generalise to Pi types
-- Suppose we have some `Y` which gives us a type for every natural number
variable (Y : ℕ → Type)
-- Y 0 : Type
-- Y 1 : Type
-- Y 2 : Type
-- ...
-- We can then make a new type, whose elements are functions from the natural numbers to
-- ⋃ i : ℕ, Y i
-- With the additional property that if we give the function some i : ℕ, the output of the function
-- should be in Y i
-- That is, we have a generalised function which takes in `i : I`, and returns a term of type `Y i`.
example : Type := Π i : ℕ, Y i
example : Type := (i : ℕ) → Y i

-- In fact, we've seen another example of Pi types in the past; with the `∀` quantifier
-- A term of type `∀ n : ℕ, n + n = 2 * n` represents a *function* which takes in a
-- natural number `n` and returns a term of type `n + n = 2 * n`
-- But remember that since `n + n = 2 * n` is a proposition, a term of type `n + n = 2 * n` is a
-- proof, and so `∀ n : ℕ, n + n = 2 * n` is a function which takes in a natural number `n` and
-- returns a proof that `n + n = 2 * n`
#check ∀ n : ℕ, n + n = 2 * n

-- here's another way of writing that type, but note that the output of the `#check` command is
-- telling me that Lean views it as identical to the previous
#check (n : ℕ) → n + n = 2 * n

-- # Inductive types
-- The next kind of type we'll look at is an inductive type
-- One way to remember their name is that they give us induction!
-- Here's (something equivalent) to the way Lean defines the natural numbers
inductive Nat' : Type where
  | zero : Nat'
  | succ (n : Nat') : Nat'

-- In fact, if you Ctrl+click (or Cmd+click on mac) on the `ℕ` symbol below, you can see the true
-- definition, and see that it's basically the same as this one, up to comments
#check ℕ
-- Also note that `ℕ` is just notation for `Nat`, but I had to call the above example `Nat'` so it
-- doesn't clash with the inbuilt one.

-- The way to read the `inductive` block is that it's defining a new type `Nat'`, declaring it
-- has type Type, and then saying the following three things:
-- * `Nat'.zero` has type `Nat'` (ie zero is a natural number)
-- * if `n` has type `Nat'` then `Nat'.succ n` has type `Nat'`
-- * that's it! (nothing else has type `Nat'`)

-- Quite a lot of the things we've already seen are actually defined as inductive types,
-- like the propositions True, False, And, and Or.
-- I've reproduced the definitions here, but remember you can cmd+click the actual definition to see
-- Lean's interpretation - it should look exactly the same, just with some more fluff around it

inductive True' : Prop where
  | intro : True'
-- * True'.intro has type True'
-- * that's it!

inductive False' : Prop where
-- * that's it!
-- ie there's nothing with type `False'`, which means there's no proof of false

inductive And' (P Q : Prop) : Prop where
  | intro (hp : P) (hq : Q) : And' P Q
-- * if we have a proof `hp` of `P` and a proof `hq` of `Q` then `And'.intro hp hq` is a proof
--   of `And' P Q`
-- * that's it!

inductive Or' (P Q : Prop) : Prop where
  | inl (hp : P) : Or' P Q
  | inr (hq : Q) : Or' P Q
-- * if we have a proof `hp` of `P` then `Or'.inl hp` is a proof of `Or' P Q`
-- * if we have a proof `hq` of `Q` then `Or'.inr hq` is a proof of `Or' P Q`
-- * that's it!

-- so there are two ways to make a proof of `P ∨ Q`, but only one way to prove `P ∧ Q` and it
-- needs two ingredients

-- inductive types which only have one "constructor", ie one way to make them, show up often enough
-- that they have a special name and syntax: they're called `structure`s
-- so `And` could alternatively be defined like this
structure And'' (P Q : Prop) : Prop where
  left : P
  right : Q
-- This says that `And''` is a `Prop` and it consists of two things: the `left` and the `right`
-- proofs.
-- We saw `structure`s earlier, when we talked about subgroups: there it consisted of a `Set`,
-- together with some properties about that set.

-- Connection: For those who know about algebraic data types and generalised algebraic data types,
-- the link here is that inductive types generalise GADTs.
-- (If you don't know about these, ignore this comment!)


-- # Quotient types
-- If we have a type `α` together with a relation `R` on that type
variable (α : Type) (R : α → α → Prop)
-- lean will give us a new type called `Quot`, which we should think of as the type `α` but
-- quotiented out by the equivalence relation generated by `R`.
#check Quot R

-- Here's how to map into a quotient type (ie the construction):
example : α → Quot R := Quot.mk R
-- That is, if we have an element of `α`, we can build an element of the quotient type.
-- This function `Quot.mk` has a key property, which is proved with the lemma `Quot.sound`.
-- That property is that if `x` and `y` are related by the relation `R`, then `Quot.mk R` maps
-- them to *equal* values
example (x y : α) (h : R x y) : Quot.mk R x = Quot.mk R y := Quot.sound h
-- Here's how to map out of a quotient type (the destruction)
example (β : Type) (f : α → β) (h : ∀ x y : α, R x y → f x = f y) :
    Quot R → β := Quot.lift f h
-- given any other type `β`, and a function `α → β`, if the function respects the equivalence
-- relation (by which I mean that the property `h` holds), then we get a function
-- `Quot R → β`

-- Just like before, the construction and destruction play nicely:
example (β : Type) (f : α → β) (h : ∀ x y : α, R x y → f x = f y) (x : α) :
    Quot.lift f h (Quot.mk R x) = f x := rfl
-- this property can also be seen as a commutative diagram
--      α     ⟶    β
--        ↘       ↗
--          α / R







-- propext
#check propext
#check Quot.sound
#check Classical.choice


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


-- Large elimination
inductive Nonempty' (α : Type) : Prop
  | intro (a : α) : Nonempty' α

theorem test1 : Nonempty' ℕ := ⟨1⟩
theorem test2 : Nonempty' ℕ := ⟨7⟩

-- If there's still time, get the list of sections from last year and discuss which ones to talk
-- about.
