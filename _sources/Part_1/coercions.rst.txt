.. _coercions:

Coercions
=========

Sometimes you have a term of a type, and you really want it to have another type (because that's what we do in maths; we are liberal with our types, unlike Lean). For example you might have a natural number ``n : ℕ`` but a function ``f : ℝ → ℝ`` (like ``Real.sqrt`` or similar), and you want to consider ``f n``. This is problematic in a strongly typed language like Lean: ``n`` has type ``Nat`` and not ``Real``, so ``f n`` does not make sense. However, if you try it...

.. code-block::

   import Mathlib.Tactic

   def a : ℕ := 37

   #check Real.sqrt a -- real.sqrt ↑a : ℝ

...it works anyway! But actually looking more closely, something funny is going on; what is that ``↑`` by the ``a``? That up-arrow is Lean's notation for the completely obvious function from ``ℕ`` to ``ℝ`` which doesn't have a name in mathematics but which Lean needs to apply in order for everything to typecheck.

Coercion to function
--------------------

Here's another example of something which shouldn't work but which does:

.. code-block::

   import Mathlib.Tactic

   variable (G H : Type) [Group G] [Group H] (φ : G →* H) (g : G)

   #check φ g -- ↑φ g : H

Here ``φ`` is a group homomorphism, so in particular it is *not a function*, it is a pair consisting
of a function and a proof that the function preserves multiplication. But we treat it as a function
and it works anyway, because there is a coercion from the type ``G →* H`` to the type ``G → H``,
indicated by an arrow.

Coercion to type
----------------

A subset of the reals is a term, not a type. The type is ``Set ℝ`` of *all* subsets of the reals,
so here ``s : Set ℝ`` is a term, not a type, and so ``a : s`` shouldn't even make sense. But if
you look carefully, you see that the type of ``a`` is in fact ``↑s``, because ``s`` has been
coerced from a term to the corresponding subtype ``{x : ℝ // x ∈ s}``. 

.. code-block::

   import Mathlib.Tactic

   example (s : Set ℝ) (a : s) : a = a := by
     /-
     s : Set ℝ
     a : ↑s
     ⊢ a = a
     -/
     rfl

A term of the subtype ``{x : ℝ // x ∈ s}`` is a pair consisting of a term ``x : ℝ`` and a proof
that ``x ∈ s``.
