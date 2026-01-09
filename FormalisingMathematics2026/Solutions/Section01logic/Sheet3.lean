/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  change True → False at h -- you don't have to do this
  apply h
  trivial

example : False → ¬True := by
  intro h
  intro h2
  exact h

example : ¬False → True := by
  intro h
  trivial

example : True → ¬False := by
  intro h
  intro h2
  exact h2

example : False → ¬P := by
  intro h
  intro hP
  exact h

example : P → ¬P → False := by
  intro hP
  intro hnP
  apply hnP
  exact hP

example : P → ¬¬P := by
  intro hP
  intro hnP
  apply hnP
  exact hP

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ hP
  apply hnQ
  apply hPQ
  assumption

example : ¬¬False → False := by
  intro h
  apply h
  intro h2
  exact h2

example : ¬¬P → P := by
  intro h
  by_contra h2
  apply h
  exact h2

example : (¬Q → ¬P) → P → Q := by
  intro h hP
  change (Q → False) → P → False at h
  by_contra hnQ
  apply h
  · exact hnQ
  · exact hP
