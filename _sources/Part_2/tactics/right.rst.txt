.. _tac_right:

right
=====

Summary
-------

There are two ways to prove ``⊢ P ∨ Q``; you can either prove ``P`` or you can prove ``Q``. If you want to change the goal to ``Q`` then use the ``right`` tactic.

Details
-------

It's a theorem in Lean that ``Q → P ∨ Q``, and the ``right`` tactic applies this theorem.

Further notes
-------------

See also ``left``. More generally, if your goal is an inductive type with two constructors, ``left`` applies the first constructor, and ``right`` applies the second one.


