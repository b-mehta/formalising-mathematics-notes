.. _tac_rfl:

rfl
===

Summary
-------

The ``rfl`` tactic proves goals of the form ``⊢ x = y`` where ``x`` and ``y`` are :ref:`definitionally equal <defeq>`. It also proves goals of the form ``P ↔ Q`` if ``P`` and ``Q`` are definitionally equal.

Examples
--------

1) ``rfl`` will prove ``⊢ x = x``.

2) ``rfl`` will prove ``⊢ P ↔ P``.

3) ``rfl`` will prove ``⊢ ¬ P ↔ (P → False)`` because even though the two sides of the iff are not syntactically equal, they are definitionally equal.

4) ``rfl`` will prove ``⊢ 2 + 2 = 4`` if the 2s and the 4 are natural numbers (i.e. have type ``ℕ``). This is because both sides are definitionally equal to ``succ(succ(succ(succ(0))))``. It will not prove ``⊢ 2 + 2 = 4`` if the ``2``s and the ``4`` are real numbers however; one would have to use a more powerful tactic such as ``norm_num`` to do this.

Further notes
-------------

Checking definitional equality can be extremely difficult. In fact it is a theorem of logic that checking definitional equality in Lean is undecidable in general. Of course this doesn't necessarily mean that it's hard in practice; in the examples we will see in this course ``rfl`` should work fine when it is supposed to work. There is a pathological example in Lean's reference manual of three terms ``A``, ``B`` and ``C`` where ```⊢ A = B`` and ```⊢ B = C`` can both be proved by ``rfl``, but ``rfl`` fails to prove ``⊢ A = C`` (even though they are definitionally equal). Such pathological examples do not show up in practice when doing the kind of mathematics that we're doing in this course though.

If you're doing harder mathematics in Lean then you can be faced with goals which look simple but which under the hood are extremely long and complex terms; sometimes ``rfl`` can take several seconds (or even longer) to succeed in these cases. In this course I doubt that we will be seeing such terrifying terms. 
