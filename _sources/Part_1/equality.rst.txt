Equality
========

.. tip::

   "Syntactic equality is they look identical, definitional equality is they are the same, propositional equality is they turn out to be the same."

As mathematicians we tend not to fuss too much about equality, at least at undergraduate level. When formalising mathematics in Lean's type theory, it turns out that one has to think a bit more carefully about what is going on. In Lean there are three different kinds of equality which one has to be aware of, and the differences between them are "non-mathematical". The strongest kind of equality is syntactic equality; this is the kind of equality that tactics like ``rw`` and ``simp`` care about. Then there is definitional equality; this is he kind of equality that tactics like ``exact`` and ``intro`` and ``rfl`` care about. Finally, there is propositional equality; this is the "usual" kind of equality as understood by mathematicians.

Overview
--------

To give you a flavour of what this document is about, and in particular to indicate that these refined notions of equality are in some sense not "mathematical", here is an example. Let ``x`` be a natural number. As mathematicians we would all agree that ``0 + x = x`` and ``x + 0 = x``. Both of these are propositional equalities. However only one is a definitional equality, and neither of them are syntactic equalities.

.. _syneq:

Syntactic equality
------------------

Syntactic equality is the strongest kind of equality there is. Two expressions are *syntactically equal* if they are literally made by pressing the same keys on your keyboard in the same order.

Example: ``x + 0`` and ``x + 0`` are syntactically equal.

Non-example: ``x + 0`` and ``x`` are not syntactically equal (even though they are mathematically equal).

The ``rewrite`` tactic works at the syntactic equality level. For example, let's say that your tactic state looks like this:

.. code-block::

   a b x : ℕ
   h : x + 0 = a
   ⊢ x = b

Then ``rw [h]`` will *fail*, even though ``x + 0 = x``. The reason it will fail is that ``x + 0`` and ``x`` are not *syntactically* equal, so the ``rw`` tactic will fail to find the left hand side of ``h`` in the goal.

.. _defeq:

Definitional equality
---------------------

Definitional equality is a weaker kind of equality than syntactic equality -- two things can sometimes be definitionally equal without being syntactically equal. A simple example is the following. In Lean, ``¬P`` is notation for ``not P``, and ``not P`` is *defined* to mean ``P → False``. So whilst ``¬P`` and ``P → False`` are not syntactically equal, they are definitionally equal.

As the name suggests, definitional equality depends on definitions, and in particular depends on implementation details (that is, on exactly how things are defined under the hood). As such, definitional equality is in some sense "not a mathematical concept". Here is an example to show you what I mean.

Addition on the natural numbers is defined "by induction", or, more precisely, by recursion. If ``x`` and ``y`` are natural numbers, then in the definition of ``x + y`` we have to choose which one to induct on. The designers of Lean chose to induct on ``y``. This means that ``x + 0`` is *defined* to be ``x``, and ``x + succ(y)`` is *defined* to be ``succ(x + y)``.

This means that ``x + 0`` and ``x`` are equal by the very definition of ``+``. To put it another way, ``x + 0`` and ``x`` are *definitionally equal*.

However, players of the `Natural number game <https://adam.math.hhu.de/>`_ will know, if we use this as the definition of addition, then to prove that ``0 + x = x`` we need to use induction. The problem is that we cannot "unfold" the definition of ``0 + x`` any further; the definition of ``0 + x`` depends on whether ``x = 0`` or ``x = succ y`` for some ``y``, so to make any progress in the proof of ``0 + x = x`` we need to use more than just unfolding definitions; we need to use induction (to split into the cases ``x=0`` and ``x=succ y``, when we can start simplifying ``0 + x``). As a result, although ``0 + x = x`` is true, it is not *definitionally* true.

The fact that ``x + 0 = x`` is a definitional equality, but ``0 + x = x`` is not, means that definitional equality is in some sense not a mathematical concept. Furthermore, if the designers of Lean had decided to define addition by recursion on the first variable instead of the second, then of course our conclusions would be the other way around.

Note also: the fact that ``x + 0`` and ``x`` are definitionally equal is specific to the natural numbers. Addition of real numbers is not defined by induction, it is defined in a far more complicated way using Cauchy sequences and quotients, and if ``r : ℝ`` then none of ``r + 0``, ``r`` or ``0 + r`` are definitionally equal to each other.

Tactics like ``exact`` and ``rfl`` work up to definitional equality. For example, the following proof works in Lean:

.. code-block:: console

   example (x : ℕ) : x + 0 = x := by
     rfl

which is perhaps not what you would expect if you have played the natural number game; I explicitly disabled this hack there. However the following does not work:

.. code-block:: console

   example (x : ℕ) : 0 + x = x := by
     rfl -- type mismatch

Similarly, this code works:

.. code-block:: console

   example (x y : ℕ) (h : x + 0 = y) : x = y := by
     exact h

because hypothesis ``h`` is definitionally equal to the goal ``x = y``.

``intro`` is another tactic which works up to definitional equality. If
``P`` is a proposition, then ``¬ P`` is notation for ``not P``, and the
*definition* of ``not P`` is ``P → False``, so the ``intro`` tactic
works here:

.. code-block:: console

   example (P : Prop) : ¬ P := by
     intro h
     /-
     tactic state now

     P : Prop
     h : P
     ⊢ False
     -/
     sorry

(although the goal is of course not provable).

Propositional equality
----------------------

This is the weakest kind of equality, and the kind most familiar to mathematicians. Two terms ``a`` and ``b`` are *propositionally equal* if you can prove ``a = b``, or equivalently if you can construct a term ``h : a = b`` of type ``a = b``. For example, if ``x`` is a natural then ``x``, ``x + 0``, ``0 + x`` and ``x + 3 - 3`` are all propositionally equal.

Appendix: syntactic equality again
----------------------------------

What I said about syntactic equality is not strictly speaking true. The below paragraph fixes it, but can be ignored by everyone other then pedants.

There are actually a couple of ways that things can be syntactically equal without literally being made by pressing the same keys in the same order. Firstly, *notation* can be unfolded without breaking syntactic equality. For example the ``=`` sign in ``x = y`` is actually notation for the ``eq`` function, and the terms ``x = y`` and ``eq x y`` are syntactically equal. Secondly, the names of globally quantified variables can change without breaking syntactical equality; for example ``∃ x, x^2 = 4`` and ``∃ y, y^2 = 4`` are syntactically equal. This is because Lean "uses de Bruijn indices" under the hood, something we won't
be talking about.
