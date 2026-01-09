/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib

open Real

/-!

# Types and terms

In this sheet we'll talk a bit more about how types work in Lean, as well as learning more about
the `rw` tactic.

Lean uses something called "types" instead of sets, as its foundational
way of saying a "collection of stuff". For example, the real numbers
are a type in Lean, a group `G` is a type `G` equipped with a multiplication
and satisfying some axioms, and so on.
-/

-- Lean is a dependently-typed language
-- Every expression has a type, and `#check` can tell you the type
#check 2
#check 17 + 4
#check π
#check rexp 1

-- You can read these as saying "2 has type ℕ", and note the `:` relation is definitely not
-- symmetric.

-- (If you get the Error Lens extension in VSCode, these show up nicely)

-- Types are expressions too!
#check ℕ
#check ℝ

/-- We can also make our own expressions, and give them names. -/
def myFavouriteNumber : ℕ := 7

/-- For any expression in Lean, I can use `sorry` as a placeholder to mean "I'll fill this in
later". Any definition or proof that uses `sorry` will give a warning. Let's fill this one in now
with your favourite number! -/
def yourFavouriteNumber : ℕ := sorry

#check myFavouriteNumber

-- or not give them a name
example : ℕ := 2

-- # But this isn't maths!

-- The type `Prop` contains `Prop`ositions...
-- They could be true:
#check 2 + 2 = 4
#check rexp 1 < π
-- or false:
#check 2 + 2 = 5
-- or open.
#check Irrational (rexp 1 + π)
-- This one was open, but now it's not!
-- I can use any definition that was made *earlier* in the file, or imported
#check myFavouriteNumber = yourFavouriteNumber

-- Here are some more propositions, this time with names. The first one is easy to see is true...
def MyVeryEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p
-- ...the second is a little trickier, but not hard to show it's false...
def MyEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)
-- ...and the last one is hopefully recognisable as an open problem!
def MyDifficultProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)

-- *Key!* If `p : Prop`, an expression of type `p` is a proof of `p`.

-- The syntax to make these expressions can be just like we saw before, except with `theorem`
-- rather than `def`.
theorem two_plus_two_equals_four : 2 + 2 = 4 := rfl
-- The keyword `theorem` might feel pretentious for a basic claim like this, and so `lemma` works
-- too:
lemma two_plus_two_equals_four_again : 2 + 2 = 4 := rfl
-- The `rfl` here refers to reflexivity of equality, and Lean here is checking that both sides
-- are actually the same, so this is true by reflexivity.

-- Here's another proof, this time slightly less trivial. We'll see `simp` in more detail later.
theorem two_plus_two_not_equals_five : 2 + 2 ≠ 5 := by simp

-- Finally, we can also use `sorry` for proofs, for example for the Erdős-Straus conjecture, which
-- is an open problem in number theory.
-- Just like before, this gives me a yellow warning, because I've used `sorry` here instead of
-- giving the proof.
theorem erdos_straus :
    ∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) :=
  sorry

-- # How can we make these expressions?
-- But now the real question is: now that we know certain expressions correspond to proofs, how can
-- we make such expressions?

-- The most basic way is via simple proof terms. Here are two examples of "built-in" proof terms:
theorem true : True := trivial
theorem two_equals_two : 2 = 2 := rfl
-- And here are two examples of proof terms I can take from the library:
theorem addition_commutes : ∀ (a b : ℕ), a + b = b + a := Nat.add_comm
theorem multiplication_commutes (a b : ℕ) : a * b = b * a := Nat.mul_comm a b
-- Observe the second example is stated slightly differently - I've moved `a` and `b` into the
-- "assumptions" for the theorem instead; and so the proof term changes a little to say I want to
-- use it for `a` and `b`.

def MySuperEasyProposition : Prop := 2 = 2
theorem my_proof : MySuperEasyProposition := rfl
-- Look closely at their types!
#check MyVeryEasyProposition
#check my_proof
-- my proposition "has type Proposition", or "is a proposition"
-- my proof "has type my proposition", or "has type 2 = 2",
--    or "is a proof of 2 = 2"

-- But just proof terms get ugly...
example (a b : ℕ) : a + a * b = (b + 1) * a :=
  (add_comm a (a * b)).trans ((mul_add_one a b).symm.trans (mul_comm a (b + 1)))

-- So we have very clever tactics to produce them instead
-- You can hover over the tactic to see some documentation for it, and there's more information
-- about `simp` later in this sheet.
example (a b : ℕ) : a + a * b = (b + 1) * a := by ring
example : 2 + 2 ≠ 5 := by simp
example : 4 ^ 25 < 3 ^ 39 := by norm_num

open Nat

-- There's also some very simple tactics
example (a b : ℝ) : a + b = b + a := by
  exact add_comm a b
example : 3 = 3 := by rfl

#check add_mul (R := ℕ)

-- In practice we write tactic proofs, and write them with help of the infoview
example (a b : ℕ) : a + a * b = (b + 1) * a := by
  rw [add_mul b 1 a, one_mul a, add_comm a (a * b), mul_comm a b]
  --> This sheet has many examples and some more information about using `rw`

open Nat

-- # Some more difficult proofs
-- Here's a definition of the factorial function: it shows how I can define a function on the
-- natural numbers inductively
def myFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n

#check myFactorial

-- Lean can compute too!
#eval myFactorial 10
-- This is sometimes useful for sanity-checking definitions, but only works for "computable" things

theorem myFactorial_add_one (n : ℕ) : myFactorial (n + 1) = (n + 1) * myFactorial n := rfl
theorem myFactorial_zero : myFactorial 0 = 1 := rfl

-- Here's an example of a more complex proof about the factorial function, see if you can follow
-- what's happening
-- Try putting your cursor at the end of the `induction n` line, and look at the two goals which
-- show up
theorem myFactorial_pos (n : ℕ) : 0 < myFactorial n := by
  induction n
  case zero =>
    rw [myFactorial_zero]
    simp
  case succ n ih =>
    rw [myFactorial_add_one]
    positivity -- this tactic tries to prove things of the form ≠ 0, ≥ 0 or > 0

-- Expressions and types, every expression has a type
-- A proof has type given by what it's proved!

-- ## Dependently typed
-- Lean is *dependently typed* (unlike C, Java, Haskell), which means that types can depend on
-- terms. Not every theorem proving language is dependently typed, but it's sometimes useful in
-- practice when formalising maths.
-- Take a look at the types of these two things:
-- `Fin` takes in a value, an element of the natural numbers, and *produces* a type.
-- (`Fin n` is the type whose elements are natural numbers less than `n`)
#check Fin 10
#check Fin

-- and here's a simple proof about the size of this (finite) type
example (n : ℕ) : Fintype.card (Fin n) = n := by simp

-- ## Simp
-- The `simp` tactic is Lean's simplifier. A bunch of lemmas throughout mathlib are tagged
-- `@[simp]`, meaning they're simplification lemmas, and so `simp` will try to use them to prove the
-- goal.

-- But this means that running `simp` can sometimes be quite slow, or more concerningly,
-- if a new lemma gets added to mathlib and tagged `simp`, it could break an old `simp` proof.
-- As a consequence, for maintainability of Lean proofs, a *non-terminal* use of the `simp` tactic
-- is strongly discouraged. Non-terminal here means that it's a tactic call which isn't the one
-- closing the goal. A terminal simp is usually fine, since new simp lemmas usually can't break
-- these, but non-terminal `simp`s are frowned upon.
-- Fortunately, however, there's a nice way to fix them: changing `simp` to `simp?` gives a code
-- action telling you which lemmas `simp` actually used, and produces a call to `simp only` instead.
-- This is a restricted version of `simp` which simplifies in the same way, but *only* uses the
-- lemmas listed.
-- Here's an example:
example (n : ℕ) : Fintype.card (Fin n) = n := by simp?
-- Changing `simp` to `simp?` is sometimes called "squeezing" it, and it has a secondary use of
-- helping you figure out what `simp` actually did, or finding lemmas which are useful in your
-- situation.

-- ## Practicing with the `rw` tactic
-- Let's get some practice with the `rw` tactic for equalities now.

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these using rw.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

-- Don't forget you can use ← to rewrite in the reverse direction!
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

-- The lemma `sub_self` could be helpful
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section
-- Instead of having to declare my six real numbers each time, I can say `variables` which will
-- include them everywhere _below_ the declaration. And to avoid them going too far, I can constrain
-- that to a section.

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- The calc keyword allows writing more structured proofs which are easier to read, and sometimes
-- easier to write as well, despite being longer.
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

-- For instance, you can start your proof by sketching the structure as follows, with the sorry
-- keyword in place of some subproofs.
-- (You don't need to fill these in, it's as above!)
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_add a b c
#check sub_self a
#check sub_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

-- The ring tactic can sometimes help a lot!
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  sorry

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  sorry

end

-- The nth_rw tactic allows you to be more precise about which occurrence of a subterm you want to
-- rewrite.
-- Usually this isn't necessary, but it's occasionally very helpful.
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
