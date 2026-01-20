.. _tac_left:

left
====

Summary
-------

There are two ways to prove ``⊢ P ∨ Q``; you can either prove ``P`` or you can prove ``Q``. If you want to prove ``P`` then use the ``left`` tactic, which changes ``⊢ P ∨ Q`` to ``⊢ P``.

Details
-------

It's a theorem in Lean that ``P → P ∨ Q``. The ``left`` tactic applies this theorem, thus reducing a goal of the form ``⊢ P ∨ Q`` to the goal ``⊢ P``.

Further notes
-------------

See also ``right``. More generally, if your goal is an inductive type with two constructors, ``left`` applies the first constructor, and ``right`` applies the second one.


