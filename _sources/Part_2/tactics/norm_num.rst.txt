.. _tac_norm_num:

norm_num
========

Summary
-------

The ``norm_num`` tactic solves equalities and inequalities which involve only normalised numerical expressions. It doesn't deal with variables, but it will prove things like ``2 + 2 = 4``, ``2 ≤ 3``, ``3 < 15/2`` and ``3 ≠ 4``. We emphasize that this is a tool which closes goals involving *numbers*.

Note
----

I often see students misusing this tactic. If your goal has a variable like `x` in, then
`norm_num` is not the tactic you should be using. Note that `norm_num` calls `simp`
under the hood so it might solve a goal like `(x : ℝ) + 0 = x` anyway -- but this is not
the correct usage of `norm_num` -- all that's happening here is that it is solving the
goal using `simp` but taking longer to do so.

Examples
--------

(with ``import Mathlib.Tactic`` imported)

.. code-block::

   example : (1 : ℝ) + 1 = 2 := by
     norm_num

   example : (1 : ℚ) + 1 ≤ 3 := by
     norm_num

   example : (1 : ℤ) + 1 < 4 := by
     norm_num

   example : (1 : ℂ) + 1 ≠ 5 := by
     norm_num

   example : (1 : ℕ) + 1 ≠ 6 := by
     norm_num

   example : (3.141 : ℝ) + 2.718 = 5.859 := by 
     norm_num

``norm_num`` also knows about a few other things; for example it seems to know about the absolute value on the real numbers.

.. code-block::

   example : |(3 : ℝ) - 7| = 4 := by
     norm_num