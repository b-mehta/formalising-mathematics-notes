.. _tac_use:

use
===

Summary
-------

The ``use`` tactic can be used to make progress with ``∃`` goals; if the goal is to show that there exists a number ``n`` with some property, then ``use 37`` will reduce the goal to showing that ``37`` has the property.

Examples
--------

1) Faced with the goal

.. code-block::

   ⊢ ∃ (n : ℝ), n + 37 = 42

progress can be made with ``use 5``. Note that ``use`` is a tactic which can leave you with an impossible goal; ``use 6`` would be an example of this, where a goal which was solvable becomes unsolvable.

2) You can give ``use`` a list of things, if the goal is claiming the existence of more than one thing. For example

.. code-block::

   import Mathlib.Tactic

   example : ∃ (a b : ℝ), a + b = 37 := by
   use 5, 32
   -- ⊢ 5 + 32 = 37
   norm_num

Further notes
-------------

The :ref:`refine <tac_refine>` tactic can do what ``use`` does; for example instead of ``use 5, 32`` in the above example, one can try ``refine ⟨5, 32, ?_⟩``. The ?underscore means "I'll do the proof later".


