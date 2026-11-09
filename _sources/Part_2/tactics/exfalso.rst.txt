.. _tac_exfalso:

exfalso
=======

Summary
-------

The ``exfalso`` tactic changes your goal to ``False``. Why might you want to do that? Usually because at this point you can deduce a contradiction from your hypotheses (for example because you are in the middle of a proof by contradiction).

Examples
--------

If your tactic state is like this:

.. code-block::

   hP : P
   h : P → False
   ⊢ Q

then this might initially look problematic, because we don't have any facts about ``Q`` to hand. However, ``False → Q`` regardless of whether ``Q`` is true or false, so and ``hP`` and ``h`` between them are enough to prove ``False``. So you can solve the goal with

.. code-block::

   exfalso -- goal now `False`
   apply h -- goal now `P`
   exact hP -- goal solved

.. warning::

   Don't use this tactic unless you can deduce a contradiction from your hypotheses! If your hypotheses are not contradictory then ``exfalso`` will leave you with an unsolvable goal.

Details
-------

What is actually happening here is that there's a theorem in Lean called ``False.elim`` which says that for all propositions ``P``, ``False → P``. Under the hood this tactic is just doing ``apply False.elim``, but ``exfalso`` is a bit shorter.
