.. _tac_choose:

choose
======

Summary
-------

The ``choose`` tactic is a relatively straightforward way to go from a proof of a proposition of the form ``∀ x, ∃ y, P(x,y)`` (where ``P(x,y)`` is some true-false statement depend on ``x`` and ``y``), to an actual *function* which inputs an ``x`` and outputs a ``y`` such that ``P(x,y)`` is true.


Basic usage
-----------

The simplest situation where you find yourself wanting to use ``choose`` is if you have a function ``f : X → Y`` which you know is surjective, and you want to write down a one-sided inverse ``g : Y → X``, i.e., such that ``f(g(y))=y`` for all ``y : Y``. Here's the set-up:

.. code-block::

   import Mathlib.Tactic

   /-
   `X` is an abstract type and `P` is an abstract true-false
   statement depending on an element of `X` and a real number.
   -/
   example (X : Type) (P : X → ℝ → Prop)
       /-
       `h` is the hypothesis that given some `ε > 0` you can find
       an `x` such that the proposition is true for `x` and `ε`
       -/
       (h : ∀ ε > 0, ∃ x, P x ε) :
     /-
     Conclusion: there's a sequence of elements of `X` satisfying the
     condition for smaller and smaller ε
     -/
     ∃ u : ℕ → X, ∀ n, P (u n) (1/(n+1)) := by
     choose g hg using h
     /-
     g : Π (ε : ℝ), ε > 0 → X
     hg : ∀ (ε : ℝ) (H : ε > 0), P (g ε H) ε
     -/
     -- need to prove 1/(n+1)>0 (this is why I chose 1/(n+1) not 1/n, as 1/0=0 in Lean!)
     let u : ℕ → X := fun n ↦ g (1/(n+1)) (by positivity)
     use u -- `u` works
     intro n
     apply hg
