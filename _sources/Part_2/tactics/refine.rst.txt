.. _tac_refine:

refine
======

Summary
-------

The ``refine`` tactic is "``exact`` with holes". You can use an incomplete term containing one or more underscores ``?_`` and Lean will give you these terms as new goals.

Examples
--------

1) Faced with (amongst other things)

.. code-block::

   hQ : Q
   ⊢ P ∧ Q ∧ R

you can see that we already have a proof of ``Q``, but we might still need to do some work to prove ``P`` and ``R``. The tactic ``refine ⟨?_, hQ, ?_⟩`` replaces this goal with two new goals ``⊢ P`` and ``⊢ R``.

2) As well as being a generalization of the ``exact`` tactic, ``refine`` is also a generalization of the ``apply`` tactic. If your tactic state is

.. code-block::

   h : P → Q
   ⊢ Q

then you can change the goal to ``⊢ P`` with ``refine h ?_``.

3) ``refine ?_`` does nothing at all; it leaves the goal unchanged.

4) Faced with ``⊢ ∃ (n : ℕ), n ^ 4 = 16``, the tactic ``refine ⟨2, ?_⟩`` turns the goal into ``⊢ 2 ^ 4 = 16``, so it does the same as ``use 2``. In fact here, because ``⊢ 2 ^ 4 = 16`` can be solved with ``norm_num``, the entire goal can be closed with ``exact ⟨2, by norm_num⟩``.

5) If your tactic state looks (in part) like this:

.. code-block::

   f : ℝ → ℝ
   x y ε : ℝ
   hε : 0 < ε
   ⊢ ∃ δ > 0, |f y - f x| < δ

then ``refine ⟨ε^2, by positivity, ?_⟩`` changes the goal to ``⊢ |f y - f x| < ε ^ 2``. Here we use the :ref:`positivity <tac_positivity>` tactic to prove ``ε^2 > 0`` from the hypothesis ``0 < ε``.

Further notes
-------------

``refine`` works up to definitional equality.

