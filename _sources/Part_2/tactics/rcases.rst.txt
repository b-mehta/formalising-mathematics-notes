.. _tac_rcases:

rcases
======

Summary
-------

The ``rcases`` tactic can be used to do multiple ``cases'`` tactics all in one line. It can also be used to do certain variable substitutions with a ``rfl`` trick.

Examples
--------

1) If ``ε : ℝ`` is in your tactic state, and also a hypothesis ``h : ∃ δ > 0, δ^2 = ε`` then you can take ``h`` apart with the ``cases'`` tactic. For example you can do this:

.. code-block::

   cases' h with δ h1 -- h1: δ > 0 ∧ δ ^ 2 = ε
   cases' h1 with hδ h2

which will leave you with the state

.. code-block::

    ε δ : ℝ
    hδ : δ > 0
    h2 : δ ^ 2 = ε

However, you can get there in one line with ``rcases h with ⟨δ, hδ, h2⟩``.

2) In fact you can do a little better. The hypothesis ``h2`` can be used as a *definition* of ``ε``, or a *formula* for ``ε``, and the ``rcases`` tactic has an extra trick which enables you to completely remove ``ε`` from the tactic state, replacing it everywhere with ``δ ^ 2``. Instead of calling the hypothesis ``h2`` you can instead type ``rfl``. This has the effect of rewriting ``← h2`` everywhere and thus replacing all the ``ε`` s with ``δ ^ 2``. If your tactic state contains this:

.. code-block::

   ε : ℝ
   h : ∃ δ > 0, δ ^ 2 = ε
   ⊢ ε < 0.1

then ``rcases h with ⟨δ, hδ, rfl⟩`` turns the state into

.. code-block::

   δ : ℝ
   hδ : δ > 0
   ⊢ δ ^ 2 < 0.1
   
Here ``ε`` has vanished, and all of the other occurrences of ``ε`` in the tactic state are now replaced with ``δ ^ 2``.

3) If ``h : P ∧ Q ∧ R`` then ``rcases h with ⟨hP, hQ, hR⟩`` directly decomposes ``h`` into ``hP : P``, ``hQ : Q`` and ``hR : R``. Again this would take two moves with ``cases'``.

4) If ``h : P ∨ Q ∨ R`` then ``rcases h with (hP | hQ | hR)`` will replace the goal with three goals, one containing ``hP : P``, one containing ``hQ : Q`` and the other ``hR : R``. Again ``cases'`` would take two steps to do this. Note: the syntax is different for ``∧`` and ``∨`` because doing cases on an ``∨`` turns one goal into two (because the inductive type ``Or`` has two constructors).

Notes
-----

``rcases`` works up to :ref:`definitional equality <defeq>`.

Other tactics which use the ``⟨hP, hQ, hR⟩`` / ``(hP | hQ | hR)`` syntax are the :ref:`rintro <tac_rintro>` tactic (``intro`` + ``rcases``) and the :ref:`obtain <tac_obtain>` tactic (``have`` + ``rcases``).
