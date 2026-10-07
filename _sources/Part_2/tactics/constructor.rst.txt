.. _tac_constructor:

constructor
===========

Summary
-------

If your goal is a proof which is "made up of subproofs" (for example a goal like ``⊢ P ∧ Q``; to prove this you have to prove ``P`` and ``Q``) then the ``constructor`` tactic will turn your goal into these multiple simpler goals.

Examples
--------

1) Faced with the goal ``⊢ P ∧ Q``, the ``constructor`` tactic will turn it into two goals ``⊢ P`` and ``⊢ Q``.

2) Faced with the goal ``⊢ P ↔ Q``, ``constructor`` will turn it into two goals ``⊢ P → Q`` and ``⊢ Q → P``.

3) Something which always amuses me -- faced with ``⊢ True``, ``constructor`` will solve the goal. This is because ``True`` is made up of 0 subproofs, so ``constructor`` turns it into 0 goals.

Further notes
-------------

The ``refine`` tactic is a more refined version of ``constructor``; faced with a goal of ``⊢ P ∧ Q``, ``constructor`` does the same as ``refine ⟨?_, ?_⟩,``. In fact ``refine`` is more powerful than ``constructor``; faced with ``⊢ P ∧ Q ∧ R`` you would have to use ``constructor`` twice to break it into three goals, whereas ``refine ⟨?_, ?_, ?_⟩`` does the job in one go.

Historical remark
-----------------

``constructor`` was called ``split`` in Lean 3, but ``split`` in Lean 4 now does what Lean 3's ``split_ifs`` tactic does.
