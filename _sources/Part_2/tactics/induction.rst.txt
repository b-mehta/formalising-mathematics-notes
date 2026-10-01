.. _tac_induction:

induction
=========

Summary
-------

The ``induction`` tactic will turn a goal of the form ``⊢ P n`` (with ``P`` a predicate on naturals, and ``n`` a natural) into two goals ``⊢ P 0`` and ``⊢ ∀ d, P d → P (succ d)``.

Overview
--------

The ``induction`` tactic does exactly what you think it will do; it's a tactic which reduces a goal which depends on a natural to two goals, the base case (always zero, in Lean) and the step case. In computer science it is very common to see a lot of other so-called inductive types (for example ``List`` and ``Expr``) and the ``induction`` tactic can get quite a lot of use; however in this course we only ever use ``induction`` on naturals. 

Example
-------

We show :math:`\sum_{i=0}^{n-1}i^2=n(n-1)(2n-1)/6` by induction on :math:`n`.

.. code-block::
   
   import Mathlib.Tactic

   open BigOperators -- ∑ notation

   open Finset -- so I can say `range n` for the finite set `{0,1,2,...,n-1}`

   -- sum from i = 0 to n - 1 of i^2 is n(n-1)(2n-1)/6
   -- note that I immediately coerce into rationals in the statement to get the correct subtraction and
   -- division (natural number subtraction and division are pathological functions)
   example (n : ℕ) : ∑ i in range n, (i : ℚ) ^ 2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
   induction' n with d hd
   · -- base case says that an empty sum is zero times something, and this sort of goal
      -- is perfect for the simplifier
      simp
   ·  -- inductive step
      rw [sum_range_succ] -- the lemma saying 
                           -- `∑ i in range (n.succ), f i = (∑ i in range n, f i) + f n`
      rw [hd] -- the inductive hypothesis
      simp -- change `d.succ` into `d + 1`
      ring


Details
-------

The definition of the natural numbers in Lean is this:

.. code-block::
   
   inductive Nat
   | zero : Nat
   | succ (n : Nat) : Nat

When this code is run, four new objects are created: the type ``Nat``, the term ``Nat.zero``, the function ``Nat.succ : Nat → Nat`` and the *recursor* for the naturals, a statement automatically generated from the definition and which can be described as saying that to do something for all naturals, you only have to do it for ``zero`` and ``succ n``, and in the ``succ n`` case you can assume you already did it for ``n``. The ``induction`` tactic applies this recursor and then does some tidying up. This is why you end up with goals containing ``n.succ`` rather than the more mathematically natural ``n + 1``. In the example above I use ``simp`` to change ``n.succ`` to ``n + 1`` (and also to push casts as far in as possible).
