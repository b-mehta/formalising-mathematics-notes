.. _tac_nlinarith:

nlinarith
=========

Summary
-------

The ``nlinarith`` tactic is a stronger version of :ref:`linarith <tac_linarith>` which can deal with some nonlinear goals (for example it can solve ``0 ≤ x^2`` if ``x : ℝ``). 

Just as for :ref:`linarith <tac_linarith>`, you can feed extra information into the mix (for example, explicit proofs ``h1`` and ``h2`` that various things are non-negative or other relevant information can be inserted into the algorithm with ``nlinarith [h1, h2]``).

Read the documentation of the ``linarith`` tactic to see the sorts of goals which this tactic can solve. In brief, it uses equalities and inequalities in the hypotheses to try and prove the goal (which can also be an inequality or an equality).
