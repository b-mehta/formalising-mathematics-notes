The three kinds of types
========================

This is some background on Lean's type theory.

Introduction
------------
Recall that every expression in Lean lives at one of three "levels" -- it is either a universe, a type or a term. The universes are easy to understand; as far as this course is concerned, there are only two, namely ``Type`` and ``Prop``. This document is about the next level down -- types. It turns out that at the end of the day there are only three kinds of ways that you can make types; there are function types, inductive types and quotient types. I will go through these three kinds of types in this section, explaining abstractly how to make the type, how to make terms of that type, and how to make functions whose domain is the type.

[A technical footnote about the "meaning" of this section. You might be wondering about the sets and theorem statements you know in mathematics (recall that in Lean the type plays the role of both), and asking yourself which kind of type each of these things is. However such a question is not really mathematically meaningful; for example the type of group homomorphisms between two groups can be made either as an inductive type or a function type, and the quotient of a group by a subgroup can be made as either an inductive type or a quotient type. In fact, it is not completely clear to me that mathematicians need to know the ins and outs of these constructions if all they want to do is to prove theorems, but here is a brief overview anyway. For more detailed information, read Lean's type theory bible, `Theorem Proving In Lean <https://leanprover.github.io/theorem_proving_in_lean4/>`_ (sections 2, 3, 7 and 12).]

[A technical footnote about universes. if you look in the `source code <https://github.com/leanprover-community/mathlib4/>`_ of ``mathlib`` you will find more general Type universes called ``Type u`` (our ``Type`` is just ``Type 0``), and you might even see ``Sort u``, which means "either ``Type u`` or ``Prop``. These "higher universes" are a consequence of the fact that *everything* in Lean has to have a type, so ``Type`` has to have a type, and this type is called ``Type 1``, which has type ``Type 2`` etc etc. We're not doing any category theory in this course, so we will ignore these higher universes.]

.. _fn_types:
   
Function types (a.k.a. Pi types)
--------------------------------

Set-theoretically, if ``X`` and ``Y`` are sets, we can consider the set ``Hom(X,Y)`` of maps from ``X`` to ``Y``. In Lean the corresponding type is called ``X → Y`` so you can think of the ``→`` symbol as "the way to make this type".

We make terms of this type using something called ``fun``. You can also use ``λ`` (they
keep meaning to deprecate it but it doesn't seem to have happened yet. with the annoying
consequence that nobody can use ``λ`` as a variable -- it is a *reserved symbol* in Lean -- it means one thing, and one thing only: it's the  ``λ`` in "lambda-calculus", if you've ever heard of that). We'll use ``fun`` below.

If you want to make the function ``f(x)`` from the reals to the reals sending ``x`` to ``x^2+3`` then in Lean the definition of ``f`` looks like this:

.. code-block::

   def f : ℝ → ℝ := fun x ↦ x^2+3

The "mapsto" symbol ``↦`` is typeset with ``\mapsto``.

In fact Lean has a slightly more general kind of function type. The idea (expressed set-theoretically) is that if we have infinitely many sets ``Y₀``, ``Y₁``, ``Y₂``,... then we can make the type of functions from the natural numbers to the union of the ``Yₙ``, but with the condition that the natural number ``i`` is sent to an element of ``Yᵢ``. More generally (and switching back to type-theoretic language), say  ``I`` is some index type, and for each ``i : I`` we have a type ``Y i``. Then Lean will let you make the type of "generalised functions" which take as input a term ``i`` of type ``I`` and which spit out a term of type ``Y i`` -- so the type of the output depends on the term which is input. Lean's notation for the type of these functions is ``∀ (i : I), Y i``, or ``∀ i, Y i`` for short. If ``f`` is such a function, then the fact that the type of the output of ``f`` depends on the term ``i`` which is input means that ``f`` is called a "dependent function", and the type ``∀ i, Y i`` of ``f`` is called a "dependent type", or a "Pi type". Not all theorem provers have dependent types -- for example the Isabelle/HOL theorem prover uses a logic called Higher Order Logic, which does not have dependent types.

Dependent types in the ``Type`` universe started showing up in mathematics in the middle of the 20th century. Those of you who have done some differential geometry might have seen this sort of thing before (if you haven't then perhaps ignore this paragraph!). The tangent space ``Tₓ`` of a manifold at a point ``x`` is a vector space, and these tangent spaces "glue together" to make a tangent bundle, the union of the tangent spaces; a section ``s`` of the tangent bundle is a function from the manifold to the union of the tangent spaces with the extra hypothesis that ``s(x)`` is an element of ``Tₓ`` for all ``x``. So a section of the tangent bundle is a term of type ``Π (x : X), T x``. They also show up in algebraic geometry when you start doing scheme theory (for example Hartshorne's definition of the structure sheaf on an affine scheme involves the dependent type of functions sending a prime ideal of a commutative ring to an element of the localisation of the ring at this prime ideal).

If the simplest examples I can come up with in mathematics are some fancy differential geometry and algebraic geometry examples, you might wonder whether we need to think about Pi types at all in this course. But in fact in the ``Prop`` universe they show up all the time! Let's consider a proof by induction. We have infinitely many true-false statements ``P 0``, ``P 1``, ``P 2 ``,..., and we want to prove them all. In other words, we want to prove the proposition ``∀ n, P n``. This proposition, like all propositions, is a type (in the ``Prop`` universe) and in fact it is a Pi type, because to give a term of this type, we need to come up with a function which takes as input a natural number ``n`` and gives as output a proof of ``P n``, that is, a term of type ``P n``. So different input terms give terms in different output types. In short, whilst you can do a lot of mathematics without dependent types, we see dependent propositions everywhere. In fact the statement of Fermat's Last Theorem is a dependent type, because the type ``x ^ n + y ^ n = z ^ n`` depends on the terms ``x``, ``y``, ``z`` and ``n``. Of course it's possible to state Fermat's Last Theorem in Isabelle/HOL or another HOL system, however the lack of dependent types might make doing modern algebraic geometry in such a system far more inconvenient.

.. _ind_types:

Inductive types
---------------

Inductive types are an extremely flexible kind of type; you make them by basically listing the rules which you will allow to make terms of this type. For example, if you want Lean's version of "a set ``X`` with three elements ``a``, ``b``, and ``c``" then you can make it like this:

.. code-block::

   inductive X : Type
   | a : X
   | b : X
   | c : X

We now have a new type ``X`` in the system, with three terms ``X.a : X``, ``X.b : X`` and ``X.c : X``.
   
So that's now to make an inductive type, and how to make terms of this type. The remaining question is how to define functions from this type, or equivalently how to use terms of this type. If you want to make a function from this type, then instead of using ``fun`` you can use Lean's "equation compiler". Here's how to define the function from ``X`` to the naturals sending ``X.a`` to ``37``, ``X.b`` to ``42`` and ``X.c`` to 0:

.. code-block::

   def f : X → ℕ
   | X.a => 37
   | X.b => 42
   | X.c => 0

Note that if you ``open X`` then you don't have to keep putting ``X.`` everywhere. It is
a source of some annoyance to some people that you can't use ``\mapsto`` here, and have
to use this ASCII art ``=>`` instead.

You might think that this kind of construction can only make finite types, but in fact the theory of inductive types is far more powerful than this, and in particular we can make many infinite types with them. For example the definition of the natural numbers in Lean looks like this:

.. code-block::

   inductive Nat : Type where
     | zero : Nat
     | succ (n : Nat) : Nat

(Peano observed that these two constructions were enough to define all natural numbers) and then mathlib sets up the notation ``ℕ`` for ``Nat`` later. If you've played the natural number game you'll know that we can define addition and multiplication on the natural numbers, and once one has these set up one can define functions from the naturals to the naturals or other types using ``fun``, for example ``fun (n : ℕ) ↦ 2*n+3`` defines a function from ``ℕ`` to ``ℕ``. However we can also use the equation compiler to inductively define (or more precisely, recursively define) functions from the naturals. For example the sequence defined by ``a(0)=3`` and ``a(n+1)=a(n)^2+37`` could be defined like this:

.. code-block::

   def a : ℕ →  ℕ
   | Nat.zero => 3
   | Nat.succ n => (a n)^2 + 37

You can make inductive propositions too. For example here are the definitions of ``True`` and ``False`` in Lean:

.. code-block::

   inductive True : Prop where
     | intro : True

   inductive False : Prop

The inductive type ``True`` has one constructor (called ``True.intro``); the inductive type ``False`` has no constructors. Remember that we model truth and falsehood of propositions in Lean by whether the corresponding type has a term or not. Faced with a goal of ``⊢ True`` you can prove it with ``exact True.intro``. You cannot make a term of type ``False`` "absolutely" -- the only time it can happen is if you are in a "relative" situation where you have hypotheses, some of which are contradictory.

If ``P`` and ``Q`` are Propositions, then you can use inductive types to make the propositions ``And P Q`` and ``Or P Q``, with notations ``P ∧ Q`` and ``P ∨ Q``. Here are their definitions:

.. code-block::

   inductive And (P Q : Prop) : Prop where
   | intro (hp : P) (hq : Q) : And P Q

   inductive Or (P Q : Prop) : Prop where 
   | intro_left (hP : P) : Or P Q
   | intro_right (hQ : Q) : Or P Q

If you do ``cases h`` with ``h : P ∧ Q`` then, because ``And`` has one constructor (``And.intro``), you end up with one goal. If you do ``cases h`` with ``h : P ∨ Q`` then you end up with two goals, because ``Or`` has two constructors (``Or.intro_left`` and ``Or.intro_right``). If you do ``cases h`` with ``h : False`` then you end up with no goals, because ``False`` has no constructors. When Lean sees that there are no goals left, it prints ``no goals``; if you have no goals left, you've proved the result you were trying to prove. It took me some time to recalibrate my thinking to this "inductive" way of thinking about logic.

We say "let ``G`` be a group" in Lean using inductive types, but the types involved are very simple inductive types with only one constructor. The type ``Group G`` is the type of group structures on ``G``. There is only way to make a term of type ``Group G`` -- you have to give a multiplication on ``G``, an identity and an inverse function, and then check that it satisfies the group axioms. So the inductive type ``Group G`` has just one constructor which takes all of this data as input and then outputs a term of type ``Group G``. We will talk more about how to make the inductive type ``Group G`` when we get on to groups in section 5.

Quotient types
--------------

The third kind of type which you can make in Lean is a quotient type, which I mention here only for completeness. Lean does not actually need this kind of type -- it is possible to make quotient types explicitly using inductive types. However for technical reasons (which mathematicians don't need to worry about) they are a distinct primitive kind of type in Lean. The basic set-up is that you have a type ``X`` and an equivalence relation ``R`` on ``X`` (for some reason this is referred to as a term of type ``Setoid X`` in Lean), and you want to make the quotient of ``X`` by ``R``. This is the type which mathematicians would typically refer to as "the set of equivalence classes of ``R``". In Lean it's called ``Quotient R``, and the map from ``X`` to ``Quotient R`` is called ``Quotient.mk R : X → Quotient R``. In particular you can make terms of type ``Quotient R`` by applying ``Quotient.mk`` to terms of type ``X`` (this is just the construction sending an element of ``X`` to its equivalence class). To define a function *from* ``Quotient R`` we use the ``Quotient.lift`` function; more on this later, when we construct some quotient types familiar to mathematicians.
