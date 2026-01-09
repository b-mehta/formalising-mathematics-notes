.. _tac_simp:

simp
====

Summary
-------

There are many lemmas of the form ``x = y`` or ``P ↔ Q`` in ``mathlib`` which are "tagged" with the ``@[simp]`` tag. Note that these kinds of lemmas are ones for which the ``rw`` tactic can be used. A lemma tagged with ``@[simp]`` is called a "simp lemma".

When Lean's simplifier ``simp`` is run, it tries to find simp lemmas for which the left hand side of the lemma is in the goal. It then uses a lemma to rewrite the goal and continues. Ultimately what happens is that the goal ends up simplified, and, ideally, solved.

Overview
--------

There are hundreds of lemmas in ``mathlib`` of the form ``x + 0 = x`` or ``x * 0 = 0``, where one side is manifestly simpler than the other (in the sense that a mathematician would instinctively replace the more complex side by the simpler side if they were trying to prove a theorem). In Lean, such a lemma might be tagged with the ``@[simp]`` tag. A tag on a lemma or definition does nothing mathematical; it is just a flag for certain tactics. The convention for ``@[simp]`` lemmas in Lean is that the left hand side of such a lemma should be the more complicated side. For example Lean has

.. code-block::

   @[simp] add_zero (x) : x + 0 = x := ...
   @[simp] zero_add (x) : 0 + x = x := ...

(proofs omitted). Because these lemmas are tagged with ``@[simp]``, the following proof works:

.. code-block::

   example (x : ℝ) : 0 + 0 + x + 0 + 0 = (x + (0 + 0)) := by
     simp

If you want to know which lemmas ``simp`` used, you can instead use ``simp?``, which gives an output listing the theorems which ``simp`` rewrote to make the progress which it made.

Examples
--------

1) If you are doing a proof by induction, then ``simp`` will often deal with the base case, because it knows lots of ways to simplify goals with a ``0`` in. Here is ``simp`` being used to prove that :math:`\sum_{i=0}^{n-1}i=n(n-1)/2`:

.. code-block::
   
   import Mathlib.Tactic

   open BigOperators Finset -- ∑ notation and access to `Finset.range`

   example (n : ℕ) :
      ∑ i in range n, (i : ℝ) = n * (n - 1) / 2 := by
   induction' n with d hd
   ·  -- base case: sum over empty type is 0 * (0 - 1) / 2
      simp
   · -- inductive step
      rw [sum_range_succ, hd]
      simp -- tidies up and reduces the goal to
            -- ⊢ ↑d * (↑d - 1) / 2 + ↑d = (↑d + 1) * ↑d / 2
      ring -- a more appropriate tactic to finish the job


Details
-------

Note that ``simp``, like ``rw``, works up to :ref:`syntactic equality <syneq>`. In other words, if your goal mentions ``x`` and there is a simp lemma ``h : x' = y`` where ``x'`` is definitionally, but not syntactically, equal to ``x``, then ``simp`` will not do the rewrite; this is because ``rw [h]`` fails.

You can use ``simp`` on hypotheses too: ``simp at h`` will run the simplifier on ``h``.

There's quite a lot to say about the ``simp`` tactic. More details of how to use it can be found in Theorem Proving In Lean, in the section "using the simplifier" `here <https://leanprover.github.io/theorem_proving_in_lean/tactics.html#using-the-simplifier>`_ .

Further notes
-------------

The related tactic ``simp?`` attempts to figure out exactly which lemmas ``simp`` used.
