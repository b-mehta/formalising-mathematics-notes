The axiom of choice
===================

The axiom of choice was something I found quite complicated as an undergraduate; it was summarised as "you can make infinitely many choices at the same time" but because I didn't really know much about set theory it took me a while before this description made any sense.

In Lean's type theory, the situation is much simpler (at least in my mind). There are two universes in Lean (at least for the purposes of this course) -- ``Prop`` and ``Type``. The ``Prop`` universe is for proofs, and the ``Type`` universe is for data. The axiom of choice is a route from the ``Prop`` universe to the ``Type`` universe. In other words, it is a way of getting data from a proof.

``Nonempty X``
--------------

If ``X : Type`` then ``Nonempty X : Prop`` is the true-false statement asserting that ``X`` is nonempty, or equivalently, that there's a term of type ``X``. For example here's part of the API for ``Nonempty``:

.. code-block::
   
   import Mathlib.Tactic

   example (X : Type) : (∃ x : X, True) ↔ Nonempty X := by
     exact exists_true_iff_nonempty

This example shows that given a term of type ``Nonempty X``, you can get a term of type ``∃ x : X, True`` (i.e., "there exists an element of ``X`` such that a true statement is true"). We would now like to go from this to actually *get* a term of type ``X``! In constructive mathematics this is impossible: because ``h`` lives in the ``Prop`` universe, Lean forgot how it was proved. However in classical mathematics we can pass from the ``Prop`` universe to the ``Type`` universe with ``Classical.choice h``, a term of type ```X```. This gives us a "noncomputable" term of type ``X``, magically constructed only from the proof ``h`` that ``X`` was nonempty. Mathematically, "noncomputable" means "it exists, but we don't actually have an algorithm or a formula for it". This is a subtlety which is often not explicitly talked about in mathematics courses, probably because it is often not relevant in a mathematical argument; a proof in classical mathematics is not a program, so we don't need an algorithm or formula for the terms involved.

You might wonder what the code for this ``Classical.choice`` function looks like, but in fact there isn't any code for it; Lean simply declares that ``Classical.choice`` is an ``axiom``, just like how in set theory the axiom of choice is declared to be an axiom.

When I first saw this axiom, it felt to me like it was way weaker than the set theory axiom of choice; in set theory you can make infinitely many choices of elements of nonempty sets all at once, whereas in Lean we're just making one choice. But later on I realised that in fact you could think of it as much *stronger* than the set theory axiom of choice, because you can interpret ``Classical.choice`` as a function which makes, once and for all, a choice of an element of *every single nonempty type*, so it easily implies the usual set-theoretic axiom of choice.

Classical.choose
----------------

In my experience, the way people want to use the axiom of choice when doing mathematics in Lean is to get an element of X not from a hypothesis ``∃ x : X, true``, but from a hypothesis like ``∃ x : ℝ, x^2 = 2`` or more generally ``∃ x : X, p x`` where ``p : X → Prop`` is a predicate on ``X``. The way to do this is as follows: you run ``Classical.choose`` on ``h : ∃ x : X, p x`` to get the element of ``X``, and the proof that this element satisfies ``p`` is ``Classical.choose_spec h``. Here's a worked example.

.. code-block::

   import Mathlib.Tactic
   import Mathlib.Analysis.Complex.Polynomial -- import proof of fundamental theorem of algebra

   open Polynomial -- so I can use notation ℂ[X] for polynomial rings
                   -- and so I can write `X` and not `polynomial.X`

   suppress_compilation -- because everything is noncomputable

   def f : ℂ[X] := X^5 + X + 37 -- a random polynomial

   lemma f_degree : degree f = 5 := by
     unfold f
     compute_degree -- polynomial degree computing tactic
     norm_num

   theorem f_has_a_root : ∃ (z : ℂ), f.IsRoot z := by
     apply Complex.exists_root -- the fundamental theorem of algebra
     -- ⊢ 0 < degree f
     rw [f_degree]
     -- ⊢ 0 < 5
     norm_num

   -- let z be a root of f (getting data from a theorem)
   def z : ℂ := Classical.choose f_has_a_root

   -- proof that z is a root of f (the "API" for `Classical.choose`)
   theorem z_is_a_root_of_f : f.IsRoot z := by
     exact Classical.choose_spec f_has_a_root
