.. _tac_by_contra:

by_contra
=========

Summary
-------

The ``by_contra`` tactic is a "proof by contradiction" tactic. If your goal is ``⊢ P`` then ``by_contra h`` introduces a hypothesis ``h : ¬P`` and changes the goal to ``False``.

Example
-------

Here is a proof of ``¬ ¬ P → P`` using ``by_contra``

.. code-block::

   example (P : Prop) : ¬ ¬ P → P := by
     intro hnnP -- assume ¬ ¬ P
     by_contra hnP -- goal is now `False`
     apply hnnP -- goal is now ¬ P
     exact hnP

Make a new Lean file in a Lean project and cut and paste the above code into it. See if you can understand the logic.

Further notes
-------------

The ``by_contra`` tactic is strictly stronger than the ``exfalso`` tactic in that not only does it change the goal to ``False`` but it also throws in an extra hypothesis.
