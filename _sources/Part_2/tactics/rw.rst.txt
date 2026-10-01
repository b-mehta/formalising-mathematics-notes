.. _tac_rw:

rw
==

Summary
-------

The ``rw`` or ``rewrite`` tactic is a "substitute in" tactic. If ``h : x = y`` is a hypothesis then ``rw [h]`` changes all of the ``x`` s in the goal to ``y`` s. ``rw`` also works with iff statements: if ``h : P ↔ Q`` then ``rw [h]`` will replace all the ``P`` s in the goal with ``Q`` s. 

Notes
-----

``rw`` works up to syntactic equality, i.e. if ``h : x = y`` then ``rw [h]`` will only work if the goal contains something which is literally the same as ``x``.

A common mistake I see is people trying ``rw [h]`` when ``h`` is *not* an equality, or an iff statement; most commonly people try it when ``h`` has type ``P → Q``. This won't work; you use the :ref:`apply <tac_apply>` tactic in this situation.

Examples
--------

1) Faced with

.. code-block::

   h : x = y
   ⊢ x ^ 2 = 1369

the tactic ``rw [h]`` will turn the goal into ``y ^ 2 = 1369``.

2) ``rw`` works with ``↔`` statements as well. Faced with

.. code-block::

   h : P ↔ Q
   ⊢ P ∧ R

the tactic ``rw [h]`` will turn the goal into ``⊢ Q ∧ R``.

3) ``rw`` can also be used to rewrite in hypotheses. For example
   given ``h : x = y`` and ``h2 : x ^ 2 = 289``, the tactic ``rw [h] at h2`` will turn ``h2`` into ``h2 : y ^ 2 = 289``. You can rewrite in multiple places at once -- for example ``rw [h] at h1 h2 h3`` will change all occurrences of the left hand side of ``h`` into the right hand side, in all of ``h1``, ``h2`` and ``h3``. If you want to rewrite in a hypothesis and a goal at the same time, try ``rw [h] at h1 ⊢`` (type the turnstile ``⊢`` symbol with ``\|-``).

4) ``rw`` doesn't just eat hypotheses -- the theorem ``zero_add`` says ``∀ x, 0 + x = x``, so if you have a goal ``⊢ 0 + t = 37`` then ``rw [zero_add]`` will change it to ``t = 37``. Note that ``rw`` is smart enough to fill in the value of ``x`` for you.

5) If you want to replace the right hand side of a hypothesis ``h`` with the left hand side, then ``rw [← h]`` will do it. Type ``←`` with ``\l``, noting that ``l`` is a small letter ``L`` for left, and not a number ``1``. 

6) You can chain rewrites in one tactic. Equivalent to ``rw [h1]``, ``rw [h2]``, ``rw [h3]`` is ``rw [h1, h2, h3]``.

7) ``rw`` will match on the first thing it finds. For example, ``add_comm`` is the theorem that ``∀ x y, x + y = y + x``. If the goal is ``⊢ a + b + c = 0`` then ``rw add_comm`` will change it to ``⊢ c + (a + b) = 0``, because if we strip away the notation then ``a + b + c = add (add a b) c``, which gets changed to ``add c (add a b)``. If you wanted to switch ``a`` and ``b`` then you can tell Lean to do this explicitly with ``rw add_comm a b``.

Further notes
-------------

1) ``rw`` tries a weak version of ``rfl`` when it's finished. Beginners can find this confusing; indeed I disabled this in the natural number game because users found it confusing. As an example, if your tactic state is

.. code-block::

   h : P ↔ Q
   ⊢ P ∧ R ↔ Q ∧ R

then ``rw [h]`` will close the goal, because after the rewrite the goal becomes ``⊢ Q ∧ R ↔ Q ∧ R`` and ``rfl`` closes this goal.

2) A variant of ``rw`` is ``rwa``, which is ``rw`` followed by the ``assumption`` tactic. For example if your tactic state is

.. code-block::

   h1 : P ↔ Q
   h2 : Q ↔ R
   ⊢ P ↔ R

then ``rwa [h1]`` closes the goal, because it turns the goal into ``Q ↔ R`` which is one of our assumptions.

3) If ``h : x = y`` and your goal is ``⊢ x * 2 + z = x``, then ``rw [h]`` will turn *both* ``x``s into ``y``s. If you only want to turn one of the ``x``s into a ``y`` then you can use ``nth_rw 1 [h]`` (for the first one) or ``nth_rw 2 [h]`` (for the second one).

4) ``rw`` works up to :ref:`syntactic equality <syneq>`. This means that if ``h : (P → False) ↔ Q`` and the goal is ``⊢ ¬P`` then ``rw [h]`` will fail, even though ``P → False`` and ``¬P`` are definitionally equal. The left hand side has to match *on the nose*.

5) ``rw`` does not work under binders. Examples of binders are ``∀`` and ``∃``. For example, if your goal is ``⊢ ∀ (x : ℕ), x + 0 = 0 + x`` then ``rw [add_zero]`` will not work. In situations like this you can either do ``intro x`` first, or you can use the more powerful ``simp_rw`` tactic; ``simp_rw [add_zero]`` works and changes the goal to ``∀ (x : ℕ), x = 0 + x``.



