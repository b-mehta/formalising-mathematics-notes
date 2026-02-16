.. _tac_specialize:

specialize
==========

Summary
-------

The ``specialize`` tactic can be used specialize hypotheses which are :ref:`function types <fn_types>`, by giving some or all of the inputs to the function. Its two main uses are with hypotheses of type ``P → Q`` and of type ``∀ x, ...`` (that is, hypotheses where you might use ``intro`` if their type was the goal).

Examples
--------

1) If you have a hypothesis ``h : P → Q`` and another hypothesis ``hP : P`` (that is, a proof of ``P``) then ``specialize h hP`` will change the type of ``h`` to ``h : Q``.

Note: ``h`` is a function from proofs of ``P`` to proofs of ``Q`` so if you just want to quickly access a proof of ``Q`` for use elsewhere, then you don't have to use ``specialize`` at all, you can make a proof of ``Q`` with the term ``h (hP)`` or, as the functional programmers would prefer us to write, ``h hP``.

2) If you have a hypothesis ``h : ∀ x, f x = 37`` saying that the function ``f (x)`` is a constant function with value 37, then ``specialize h 10`` will change ``h`` to ``h : f 10 = 37``.

Note that ``h`` has now become a weaker statement; you have *lost* the hypothesis that ``∀ x, f x = 37`` after this application of the ``specialize`` tactic. If you want to keep it around, you could make a copy by running ``have h2 := h`` beforehand.

3) You can specialize more than one variable at once. For example if you have a hypothesis ``h : ∀ (x y : ℕ), ...`` then ``specialize h 37 42`` sets ``x = 37`` and ``y = 42`` in ``h``.
   
4) If you have a hypothesis ``h : ∀ ε > 0, ∃ δ > 0, ...``, it turns out that internally this is ``∀ (ε : ℝ), ε > 0 → ...``. If you also have variables ``ε : ℝ`` and ``hε : ε > 0`` then you can do ``specialize h ε hε`` in which case ``h`` will change to ``∃ δ > 0, ...`` .

5) If again you have a hypothesis ``h : ∀ ε > 0, ∃ δ > 0, ...`` but you would like to use ``h`` in the case where ``ε = 37`` then you can ``specialize h 37`` and this will change ``h`` to ``h : 37 > 0 → (∃ δ...``. Now obviously ``37 > 0`` but ``h`` still wants a proof of this as its next input. You could make this proof in a couple of ways. For example (assuming that ``37`` is the real number ``37 : ℝ``, which it probably is if you're doing epsilon-delta arguments) this would work:

.. code-block::

   have h37 : (37 : ℝ) > 0 -- two goals now
   · positivity
   specialize h h37

However you could just drop the proof in directly:

.. code-block::

   specialize h (by positivity)

or

.. code-block::

   specialize h (by norm_num)

or

.. code-block::

   specialize h (by linarith)

In fact going back to the original hypothesis ``h : ∀ ε > 0, ∃ δ > 0, ...``, and remembering that Lean actually stores this as ``h : ∀ (ε : ℝ), ε > 0 → ∃ δ ...``, you could specialize to ``ε = 37`` in one line with ``specialize h 37 (by positivity)``.

Further notes
-------------

You don't always have to ``specialize``. For example if you have ``h : ∀ ε > 0, ∃ N, some_fact`` where ``some_fact`` is some proposition which depends on ``ε`` and ``N``, and you also have ``ε : ℝ`` and ``hε : ε > 0`` in your tactic state, you can just get straight to ``N`` and the fact with ``cases' h ε hε with N hN`` or ``obtain ⟨N, hN⟩ : some_fact := h ε hε``.

