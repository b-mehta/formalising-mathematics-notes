.. _tac_cases:

cases
=====

Summary
-------

``cases`` is a general-purpose tactic for "deconstructing" hypotheses. If ``h`` is a hypothesis which somehow "bundles up" some pieces of information, then ``cases' h with h1 h2`` (note the dash!) will make hypothesis ``h`` vanish and will replace it with the two "components" which made the proof of ``h`` in the first place. Variants are ``cases`` (which does the same thing but with a different syntax) and ``rcases`` (which is "recursive ``cases``" and which has its own page here: :ref:`tac_rcases` )

Here are four ways they might look for deconstructing ``h : P ∧ Q``. In each example, this removes the hypothesis ``h`` and replaces it with two hypotheses ``hP : P`` and ``hQ : Q``.

.. code-block::

   cases' h with hP hQ

   cases h with
   | intro hP hQ =>

   cases h
   case intro hP hQ =>

   rcases h with ⟨hP, hQ⟩

And here are four ways they might look for ``h : P ∨ Q``. In each example, this removes the hypothesis ``h`` and replaces it either hypotheses ``hP : P`` or ``hQ : Q``.

.. code-block::

   cases' h with hP hQ

   cases h with
   | inl hP =>
   | inr hQ =>

   cases h
   case inl hP =>
   case inr hQ =>

   rcases h with hP | hQ

Examples
--------

1) The way to make a proof of ``P ∧ Q`` is to use a proof of ``P`` and a proof of ``Q``. If you have a hypothesis ``h : P ∧ Q``, then ``cases' h`` will delete the hypothesis and replace it with hypotheses ``left✝ : P`` and ``right✝ : Q``. That weird dagger symbol in those names means that you can't use these hypotheses explicitly! It's better to type ``cases h' with hP hQ``.

2) The way to make a proof of ``P ↔ Q`` is to prove ``P → Q`` and ``Q → P``. So faced with ``h : P ↔ Q`` one thing you can do is ``cases' h with hPQ hQP`` which removes ``h`` and replaces it with ``hPQ: P → Q`` and ``hQP: Q → P``. Note however that this might not be the best way to proceed; whilst you can ``apply hPQ`` and ``hQP``, you lose the ability to rewrite ``h`` with ``rw h``. If you really want to deconstruct ``h`` but also want to keep a copy around for rewriting later, you could always try ``have h2 := h`` then ``cases' h with hPQ hQP``.

3) There are two ways to make a proof of ``P ∨ Q``. You either use a proof of ``P``, or a proof of ``Q``. So if ``h : P ∨ Q`` then ``cases' h with hP hQ`` has a different effect to the first two examples; after the tactic you will be left with *two* goals, one with a new hypothesis ``hP : P`` and the other with ``hQ : Q``. One way of understanding why this happens is that the :ref:`inductive type <ind_types>` ``Or`` has two constructors, whereas ``And`` only has one.

4) There are two ways to make a natural number ``n``. Every natural number is either ``0`` or ``succ m`` for some natural number ``m``. So if ``n : ℕ`` then ``cases' n with m`` gives two goals; one where ``n`` is replaced by ``0`` and the other where it is replaced by ``succ m ``. Note that this is a strictly weaker version of the ``induction`` tactic, because ``cases'`` does not give us the inductive hypothesis.

5) If you have a hypothesis ``h : ∃ a, a^3 + a = 37`` then ``cases' h with x hx`` will give you a number ``x`` and a proof ``hx : x^3 + x = 37``.

Further notes
-------------

Note that ``∧`` is right associative: ``P ∧ Q ∧ R`` means ````P ∧ (Q ∧ R)``. So if ``h : P ∧ Q ∧ R`` then ``cases' h with h1 h2`` will give you ``h1 : P`` and ``h2 : Q ∧ R`` and then you have to do ``cases' h2`` to get to the proofs of ``Q`` and ``R``. The syntax ``cases' h with h1 h2 h3`` doesn't work (``h3`` just gets ignored). A more refined version of the ``cases`` tactic is the :ref:`tac_rcases` tactic (although the syntax is slightly different; you need to use pointy brackets ``⟨,⟩`` with ``rcases``). For example if ``h : P ∧ Q ∧ R`` then you can do ``rcases h with ⟨hP, hQ, hR⟩``.

