.. _tac_apply:

apply
=====

.. warning::

   The ``apply`` tactic does *two very specific things*, which I explain below. I have seen students trying to use this tactic to do all sorts of other things, based solely on the fact that they want to "apply a theorem" or "apply a technique". The English word "apply" has **far more uses** than the Lean ``apply`` tactic. 
   
   Used alone, the ``apply`` tactic "argues backwards", using an implication to reduce the goal to something closer to the hypotheses. ``apply h`` is like saying "because of ``h``, it suffices to prove this new simpler thing".

   Used "at" another hypothesis, it "argues forwards", using the proof of an implication ``P → Q`` to change a hypothesis of ``P`` to one of ``Q``.

Summary
-------

If your local context is

.. code-block::

   h : P → Q
   ⊢ Q

then ``apply h`` changes the goal to ``⊢ P``.

And if you have two hypotheses like this:

.. code-block::

   h : P → Q
   h2 : P

then ``apply h at h2`` changes ``h2`` to ``h2 : Q``.

.. note::

   ``apply h`` and ``apply h at h'``  will *not work* unless ``h`` is of the form ``P → Q``. ``apply h`` will also *not work* unless the goal is equal to the conclusion ``Q`` of ``h``, and ``apply h at h2`` will *not work* unless ``h2`` is a proof of the premise ``P`` of ``h``. You will get an obscure error message if you try using ``apply`` in situations which do not conform to the pattern above.

Mathematically, ``apply ... at ...`` is easy to understand; we have a hypothesis saying that ``P`` implies ``Q``, so we can use it to change a hypothesis ``P`` to ``Q``. The bare ``apply`` tactic is a little harder to understand. Say we're trying to prove ``Q``. If we know that ``P`` implies ``Q`` then of course it would suffice to prove ``P`` instead, because ``P`` implies ``Q``. So ``apply`` *reduces* the goal from ``Q`` to ``P``. If you like, ``apply`` executes the *last* step of a proof of ``Q``, rather than what many mathematicians would think of as the "next" step. 

If instead of an implication you have an iff statement ``h : P ↔ Q`` then ``apply h`` won't work. You might want to "apply" ``h`` by using the :ref:`rw <tac_rw>` (rewrite) tactic.

Examples
--------

1) If you have two hypotheses like this:

.. code-block::

   h : x = 3 → y = 4
   h2 : x = 3

then ``apply h at h2`` will change ``h2`` to a proof of ``y = 4``.

2) If your tactic state is
   
.. code-block::
   
   h : a ^ 2 = b → a ^ 4 = b ^ 2
   ⊢ a ^ 4 = b ^ 2

then ``apply h`` will change the goal to ``⊢ a ^ 2 = b``.

3) ``apply`` works up to :ref:`definitional equality <defeq>`. For example if your local context is

.. code-block::
   
   h : ¬P
   ⊢ False

then ``apply h`` works and changes the goal to ``⊢ P``. This is because ``h`` is definitionally equal to ``P → False``.

4) ``apply`` can also be used in the following situation:

.. code-block::

   import Mathlib.Tactic

   example (X Y : Type) (φ ψ : X → Y) (h : ∀ a, φ a = ψ a) (x : X) :
      φ x = ψ x := by
   apply h
   done

Here ``h`` can be thought of as a function which takes as input an element of ``X``
and returns a proof, so ``apply`` makes sense.

5) The ``apply`` tactic does actually have one more trick up its sleeve: in the situation

.. code-block::

   h : P → Q → R
   ⊢ R

the tactic ``apply h`` will work (even though the brackets in ``h`` which Lean doesn't print are ``P → (Q → R)``), and the result will be two goals ``⊢ P`` and ``⊢ Q``. Mathematically, what is happening is that ``h`` says "if ``P`` is true, then if ``Q`` is true, then ``R`` is true", hence to prove ``R`` is true it suffices to prove that ``P`` and ``Q`` are true.

Further notes
-------------

The :ref:`refine <tac_refine>` tactic is a more refined version of ``apply``. For example, if ``h : P → Q`` and the goal is ``⊢ Q`` then ``apply h`` does the same thing as ``refine h ?_``.
