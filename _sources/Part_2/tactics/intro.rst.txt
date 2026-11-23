.. _tac_intro:

intro
=====

Summary
-------

The ``intro`` tactic makes progress on goals of the form ``⊢ P → Q`` or ``⊢ ∀ x, P x`` (where ``P x`` is any proposition that depends on ``x``). Mathematically, it says "to prove that ``P`` implies ``Q``, we can assume that ``P`` is true and then prove ``Q``", and also "to prove that ``P x`` is true for all ``x``, we can let ``x`` be arbitrary and then prove ``P x``.

Examples
--------

``intro h`` turns

.. code-block::

   ⊢ P → Q

into

.. code-block::

   h : P
   ⊢ Q

Similarly, ``intro x`` turns

.. code-block::

   ⊢  ∀ (a : ℕ), a + a = 2 * a

into

.. code-block::

   x : ℕ
   ⊢ x + x = 2 * x

Details
-------

``intro`` works when the goal is what is known as a "Pi type". This is a fancy computer science word for some kind of generalised function type. One Pi type goal which mathematicians often see is an implication type of the form ``P → Q`` where ``P`` and ``Q`` are propositions. The other common Pi type goal is a "for all" goal of the form ``∀ a, a + a = 2 * a``. Read more about Pi types in the Part 1 explanation of Lean's three different types.

Variants of ``intro`` include the :ref:`intros <tac_intros>` tactic (which enables you to ``intro`` several variables at once) and the :ref:`rintro <tac_rintro>` tactic (which enables you to do case splits on variables whilst introducing them).
