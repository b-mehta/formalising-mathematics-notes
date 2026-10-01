.. _tac_rintro:

rintro
======

Summary
-------

The ``rintro`` tactic can be used to do multiple ``intro`` and ``cases'`` tactics all in one line.

Examples
--------

1) Faced with the goal

.. code-block::

   ⊢ P → (Q ∧ R) → S

one could use the following tactics

.. code-block::

   intro hP
   intro h
   cases' h with hQ hR

to get the tactic state

.. code-block::

   hP : P
   hQ : Q
   hR : R
   ⊢ S

However, one can get there in one line with

.. code-block::

  rintro hP ⟨hQ, hR⟩

(the pointy brackets ``⟨⟩`` can be obtained by typing ``\<`` and ``\>`` in VS Code.)

2) Faced with a goal of the form

.. code-block::

   ⊢ P ∨ Q → R

the tactic ``rintro (hP | hQ)`` will do the same as ``intro h`` then ``cases' h with hP hQ``. In particular, after the application of the tactic there will be two goals, one with hypothesis ``hP : P`` and the other with hypothesis ``hQ : Q``. Note the round brackets for "or" goals.

3) There is a ``rfl`` easter egg with the ``rintro`` tactic. If the goal is

.. code-block::

   ⊢ a = 2 * b → 2 * a = 4 * b

then you can solve the goal with

.. code-block::

   intro h
   rw [h]
   ring

but there's a trick: ``rintro rfl`` will, instead of naming the hypothesis ``a = 2 * b`` and putting it in the tactic state, instead *define* ``a`` to be ``2 * b``, leaving the goal as

.. code-block::
   
   ⊢ 2 * (2 * b) = 4 * b

so now ``ring`` solves the goal immediately.

Details
-------

Note that ``rintro`` works up to :ref:`definitional equality <defeq>`, like ``intro``, so for example if the goal is ``⊢ ¬P`` then ``rintro hP`` works fine (because ``¬P`` is definitionally equal to ``P → False``), leaving the tactic state as

.. code-block::

   hP : P
   ⊢ False

Further notes
-------------

The syntax for ``rintro`` with pointy and round brackets is the same as the syntax for ``rcases``, where more examples are given.

