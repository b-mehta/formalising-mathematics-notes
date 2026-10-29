.. _tac_obtain:

obtain
======

Summary
-------

The ``obtain`` tactic can be used to do ``have`` and ``cases`` all in one go. It uses the same ``⟨x, y⟩`` / ``(x | y)`` syntax as the :ref:`rcases <tac_rcases>` tactic.

Example
-------

If you have a hypothesis ``h : ∀ ε > 0, ∃ (N : ℕ), (1 : ℝ) / (N + 1) < ε``, then you could specialize ``h`` to the case ``ε = 0.01`` with ``have h2 := h 0.01 (by norm_num)`` (or ``specialize h 0.01 (by norm_num)`` if you're prepared to change ``h``) and then you can get to ``N`` and the hypothesis ``hN : 1 / (N + 1) < ε`` with ``cases' h2 with N hN`` or ``rcases h2 with ⟨N, hN⟩``. But you can do both steps in one go with ``obtain ⟨N, hN⟩ := h 0.01 (by norm_num)``.

To make your code more readable you can explicitly mention the type of ``⟨N, hN⟩``. In the above example you could write ``obtain ⟨N, hN⟩ : ∃ (N : ℕ), (1 : ℝ) / (N + 1) < 0.01 := h 0.01 (by norm_num)``, meaning that the reader can instantly see what the type of ``hN`` is.

Notes
-----

Note that, like ``rcases`` and ``rintro``, ``obtain`` works up to :ref:`definitional equality <defeq>`.

As with ``rcases`` and ``rintro``, there is a ``rfl`` trick, where you can eliminate a variable using ``rfl`` instead of a hypothesis name.
