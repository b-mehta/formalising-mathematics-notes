.. _tac_simpa:

simpa
=====

Summary
-------

If you have a goal and a hypothesis ``h``, and if Lean's simplifier ``simp``, if run on both of them, will turn them into the same thing, then you could solve the goal in three lines with ``simp``, ``simp at h``, ``exact h``, or even in two lines with ``simp at *``, ``exact h``. But you could also solve it in one line with ``simpa using h``. In fact ``h`` doesn't need to be a hypothesis, it can be any proof you like (e.g. a proof you made using some lemmas and some hypotheses).

Examples
--------

1) 

.. code-block::

   import Mathlib.Tactic

   example (x y z : ℝ) (h : x = y + z + 0) : x * 1 = y + z := by
     -- Lean's simplifier knows that a + 0 = 0 and a * 1 = a
     simpa using h

Here the simplifier can do some work on both the hypothesis ``h`` (removing the ``+ 0``) and on the goal (removing ``* 1``). Once this work is done, ``h`` and the goal become equal. 

2) Like with ``simp``, you can also feed ``simpa`` a list of extra lemmas for the simplifier to use. For the example below ``simpa using h`` won't work because the simplifier doesn't know ``hxy`` (the simplifier doesn't use hypotheses in the tactic state).

.. code-block::
   
   import Mathlib.Tactic

   example (x y z : ℕ) (hxy : x = y) (h : z = y + 0) : z = x * 1 := by
   simpa [hxy] using h

Further notes
-------------

Easter egg: If your hypothesis is called ``this`` then you don't have to write ``using this`` at all, you can just write ``simpa``.

