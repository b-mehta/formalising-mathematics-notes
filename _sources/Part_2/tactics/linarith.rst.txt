.. _tac_linarith:

linarith
========

Summary
-------

The ``linarith`` tactic solves certain kinds of linear equalities and inequalities in concrete types such as the naturals or reals. Unlike the ``ring`` tactic, ``linarith`` uses hypotheses in the tactic state. It's very handy for epsilon-delta proofs.

Examples
--------

1) If your local context looks like this:

.. code-block::

   a b c d : ℝ
   h1 : a < b
   h2 : b ≤ c
   h3 : c = d
   ⊢ a + a < d + b

then you would like to say that the goal "obviously" follows from the conclusions. but actually proving it from first principles is a little bit messy, and will involve knowing or discovering the names of lemmas such as ``lt_of_lt_of_le`` and ``add_lt_add``. Fortunately, you don't have to do this: ``linarith`` closes this goal immediately. Note that in contrast to ``ring``, ``linarith`` does have access to the hypotheses in your local context.

2) If you have a goal of the form ``|x| < ε`` then ``linarith`` might not be much help yet, because it doesn't know about absolute values. So you could ``rw abs_lt`` and get a goal of the form ``-ε < x ∧ x < ε``. Well, ``linarith`` still won't be of any help, because it doesn't know about goals with ``∧`` in either! However after you try ``constructor``, perhaps ``linarith`` will be able to help you.

.. code-block::

   import Mathlib.Tactic

   example (x ε : ℝ) (hε : 0 < ε) (h1 : x < ε / 2) (h2 : -x < ε / 2) : |x| < ε := by
   rw [abs_lt] -- `⊢ -ε < x ∧ x < ε`
   constructor <;> -- <;> means "do next tactic on all the goals this tactic produces"
   linarith -- solves both goals


