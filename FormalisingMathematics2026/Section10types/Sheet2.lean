import Mathlib.Tactic

/-
# Admin things

Marks should appear Friday 13th on blackboard

Mentimeter: 4629 8578

Away from 16th - 20th Feb: lectures and labs will still happen, with guest lecturers
  Kevin Buzzard (ask him about algebra and number theory)
  some of the postdocs (group theory, number theory, algebraic geometry)

Fewer lectures in the future!
-/

/-
Last time we saw the three main ways of making types in Lean:
Pi types, inductive types, and quotient types
We saw that these can be used to make many of the types we'd already seen up to this point,
and you can imagine that they can be composed to make many more.
But this misses out a big part of the story: universes!

Universes have actually been there the whole time.
`Prop` and `Type` are types but they don't fall into any of the above categories:
these are universes!
-/

example {P : Prop} : P → P := by
  intro hP
  revert hP
  intro hP
  exfalso
  sorry

example {a b c : ℝ} (ha : a ≤ b) (hb : a ≤ c) : a ≤ b := by
  grw [hb]

example {n : ℕ} (h : ((n + 1 : ℕ) : ℚ) ≠ n + 1) : False := by
  norm_cast at h

example {a b : ℝ} (h : 2 * a + 3 * b = 1) (h' : a + 2 * b = 0) :
    a = 2 := by
  linear_combination 2 * h - 3 * h'

example {a b : ℚ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have := sq_nonneg (a - b)
  linear_combination this

example {n : ℤ} (hn : 1 ≤ n) : False := by
  have hn' : 0 ≤ n := by grind
  lift n to ℕ using hn'
  norm_cast at hn
  sorry
