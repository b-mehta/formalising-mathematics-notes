.. _tac_change:

change
======

Summary
-------

If your goal is ``⊢ P``, and if ``P`` and ``Q`` are :ref:`definitionally equal <defeq>`, then ``change Q`` will change your goal to ``Q``. You can use it on hypotheses too: ``change Q at h`` will change ``h : P`` to ``h : Q``. Note: ``change`` can sometimes be omitted, as many (but not all) tactics "see through" definitional equality.

Example
-------

1) In Lean, ``¬P`` is *defined* to mean ``P → False``, so if your goal is ``⊢ ¬P`` then ``change P → False`` will change it the goal to ``⊢ P → False``.

2) The ``rw`` tactic works up to syntactic equality, not definitional equality, so if your tactic state is

.. code-block::

   h : ¬P ↔ Q
   ⊢ P → False

then ``rw h`` doesn't work, even though the left hand side of ``h`` is definitionally equal to the goal. However

.. code-block::

   change ¬P,
   rw h

works, and changes the goal to ``Q``.

3) ``change`` also works on hypotheses: if you have a hypothesis ``h : ¬P`` then ``change P → False at h`` will change ``h`` to ``h : P → False``.
   
Details
-------

Definitionally equal propositions are logically equivalent (indeed, they are equal!) so Lean allows you to change a goal ``P`` to a definitionally equal goal ``Q``, because ``P`` is true if and only if ``Q`` is true.

Further notes
-------------

Many tactics work up to definitional equality, so sometimes ``change`` is not necessary. For example if your goal is ``⊢ ¬P`` then ``intro h`` works fine anyway, as ``intro`` works up to definitional equality.

``show`` does the same thing as ``change`` on the goal, but it doesn't work on hypotheses.

