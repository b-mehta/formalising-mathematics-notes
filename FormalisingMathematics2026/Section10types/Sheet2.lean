import Mathlib.Tactic

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
