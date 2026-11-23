.. _tac_convert:

convert
=======

Summary
-------

If a hypothesis ``h`` is nearly but not quite equal to your goal, then ``exact h`` will fail, because theorem provers are fussy about details. But ``convert h`` might well succeed, and leave you instead with goals corresponding to the places where ``h`` and the goal did not quite match up.

Examples
--------

1) Here the hypothesis ``h`` is really close to the goal; the only difference is that one has a ``d`` and the other has an ``e``. If you already have a proof ``hde : d = e`` then you can ``rw hde at h`` and then ``exact h`` will close the goal. But if you don't have this proof to hand and would like Lean to reduce the goal to ``d = e`` then ``convert`` is exactly the tactic you want.

.. code-block::

   import Mathlib.Tactic

   example (a b c d e : ℝ) (f : ℝ → ℝ) (h : f (a + b) + f (c + d) = 37) :
       f (a + b) + f (c + e) = 37 := by
     convert h
     -- ⊢ e = d
     sorry

2) Sometimes `convert` can go too far. For example consider the following (provable) goal:

.. code-block::
   
   a b c d e : ℝ
   f : ℝ → ℝ
   h : f (a + b) + f (c + d) = 37
   ⊢ f (a + b) + f (d + c) = 37

If you try ``convert h`` you will be left with two goals ``⊢ d = c`` and ``⊢ c = d`` (and these goals are not provable from what we have). You can probably guess what happened; ``convert`` was too eager. You can "tone ``convert`` down" with ``convert h using 2`` or some other appropriate small number, to tell it when to stop converting. Experiment with the number to get it right. Here is an example.

.. code-block::

   import Mathlib.Tactic

   example (a b c d : ℝ) (f : ℝ → ℝ) (h : f (a + b) + f (c + d) = 37) :
       f (a + b) + f (d + c) = 37 := by
     convert h using 3 -- `using 4` gives unprovable goals
     -- ⊢ d + c = c + d
     ring
