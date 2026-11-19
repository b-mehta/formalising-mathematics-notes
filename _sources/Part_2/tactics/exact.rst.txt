.. _tac_exact:

exact
=====

Summary
-------

If your goal is ``⊢ P`` then ``exact h`` will close the goal if ``h : P`` has type ``P``.

Examples
--------

1) If the local context is


.. code-block::

   h : P
   ⊢ P

then the tactic ``exact h`` will close the goal.

2) ``exact`` works up to :ref:`definitional equality <defeq>`. So for example, if the local context is

.. code-block::

   h : ¬ P
   ⊢ P → False

then ``exact h`` will work, because the type of ``h`` is definitionally equal to the goal.

Further notes
-------------

A common mistake amongst beginners is trying ``exact P`` to close a goal of type ``P``. The goal is a type, but the ``exact`` tactic takes a term of that type, not the type itself. Remember : ``P`` is the *statement* of the problem. To solve the goal you need to supply the *proof*.
