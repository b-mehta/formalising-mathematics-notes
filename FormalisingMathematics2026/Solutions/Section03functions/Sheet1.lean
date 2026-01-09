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

-- (If you get the Error Lens extension in VSCode, these show up nicely)

-- Types are expressions too!

#check ℕ
#check ℝ

-- We can also make our own expressions, and give them names
def myFavouriteNumber : ℕ := 7

def yourFavouriteNumber : ℕ := sorry

#check myFavouriteNumber

-- or not give them a name
example : ℕ := 2

-- # But this isn't maths!

-- The type `Prop` contains `Prop`ositions...

#check 2 + 2 = 4
#check rexp 1 < π

#check 2 + 2 = 5
#check Irrational (rexp 1 + π)
#check myFavouriteNumber = yourFavouriteNumber

def MyDifficultProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)
def MyEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)
def MyVeryEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p

-- Key! If `p : Prop`, an expression of type `p` is a proof of `p`.

example : 2 + 2 = 4 := rfl
example : 2 + 2 ≠ 5 := by simp
example : ∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) := sorry
-- Erdős-Strauss conjecture

example (n : ℕ) (hn : 2 ≤ n) :
  ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) := sorry

-- # How can we make these expressions?

-- Simple proof terms
example : True := trivial
example : 2 = 2 := rfl
example (a b : ℕ) : a + b = b + a := Nat.add_comm a b

example (a b : ℕ) : a * b = b * a := Nat.mul_comm a b

theorem my_proof : MyVeryEasyProposition := fun n => ⟨n, le_rfl⟩

#check MyVeryEasyProposition
#check my_proof
-- my proposition "has type Proposition", or "is a proposition"
-- my proof "has type my proposition", or "has type ∀ n : ℕ, ∃ p, n ≤ p",
--    or "is a proof of ∀ n : ℕ, ∃ p, n ≤ p"

-- But just proof terms get ugly...
example (a b : ℕ) : a + a * b = (b + 1) * a :=
  (add_comm a (a * b)).trans ((mul_add_one a b).symm.trans (mul_comm a (b + 1)))

-- Very clever tactics
example (a b : ℕ) : a + a * b = (b + 1) * a := by ring

example : 2 + 2 ≠ 5 := by simp
example : 4 ^ 25 < 3 ^ 39 := by norm_num

open Nat

-- Simple tactics
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
def myFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * myFactorial n

#check myFactorial

-- Lean can compute too!
-- #eval myFactorial 10
-- sometimes useful for sanity-checking definitions

theorem myFactorial_add_one (n : ℕ) : myFactorial (n + 1) = (n + 1) * myFactorial n := rfl
theorem myFactorial_zero : myFactorial 0 = 1 := rfl

theorem myFactorial_pos (n : ℕ) : 0 < myFactorial n := by
  induction n
  case zero =>
    rw [myFactorial_zero]
    simp
  case succ n ih =>
    rw [myFactorial_add_one]
    positivity

-- Expressions and types, every expression has a type
-- A proof has type given by what it's proved!

-- ## Dependently typed
-- Lean is *dependently typed* (unlike C, Java, Haskell), which means that types can depend on
-- terms. Not every theorem proving language is dependently typed, but it's sometimes useful in
-- practice when formalising maths.
#check Fin 10
#check Fin

example (n : ℕ) : Fintype.card (Fin n) = n := by simp

-- ## terminal simps
example (n : ℕ) : Fintype.card (Fin n) = n := by simp?

-- ## naming
-- https://leanprover-community.github.io/contribute/naming.html

-- ## hierarchy!
#check 3
#check ℕ
#check 4 = 4
#check Prop
#check Type
#check Type 1
#check Type 2

#check Type 0

-- myproof : myVeryEasyProposition : Prop : Type : Type 1 : Type 2 : Type 3 : ...

-- ## Practicing with the `rw` tactic

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these using rw
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b, mul_assoc, mul_comm c a]

-- Don't forget you can use ← to rewrite in the reverse direction!
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, ← mul_assoc, mul_comm a]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a, h, ← mul_assoc]

-- The lemma `sub_self` could be helpful
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp, hyp', mul_comm, sub_self]

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
  rw [add_mul, mul_add, mul_add, ← add_assoc]

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [add_mul, mul_sub, mul_sub, add_sub, sub_add, mul_comm a b, sub_self, sub_zero, pow_two,
    pow_two]

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
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

-- The nth_rw tactic allows you to be more precise about which occurrence of a subterm you want to
-- rewrite.
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
