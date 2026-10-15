Types and terms
===============

Sets and their elements
-----------------------

In mathematics you have seen many examples of sets and their elements. For example the real numbers ``ℝ`` is a set, and it has elements such as ``37`` and ``12345``. It is difficult to give a formal definition of a set. Typically a student thinks of a set as a "collection of things", and the elements of the set are the things.

Lean uses something called type theory as a foundation of mathematics rather than set theory. We will not be launching into a deep study of type theory in this course; the idea of this section is to give you a working knowledge of the key differences between type theory and set theory.

In Lean the *type* plays the role of the "collection of things", and the things in the type are called *terms*. For example, in Lean the real numbers ``ℝ`` are a type, not a set, and specific real numbers like ``37`` and ``12345`` are called terms of this type.

The notation used is also different to what you have usually seen. In set theory, we write ``37 ∈ ℝ`` to mean that ``37`` is a real number. More formally we might say "``37`` is an element of the set of real numbers". In type theory the notation is different. In type theory we express the idea that ``37`` is a real number by writing ``37 : ℝ``, and more formally we would say "``37`` is a term of the type of real numbers". Basically the colon ``:`` in type theory plays the role of the "is an element of" symbol ``∈`` in set theory.

The universe of all types
-------------------------

Some of you might know that whilst it's unproblematic to talk about the set of real numbers in set theory, it *is* problematic to talk about the set of all sets. Russell's Paradox is the observation that if ``X`` is the set of all sets which are not elements of themselves, then ``X ∈ X`` if and only if ``X ∉ X``, a contradiction. For similar reasons one cannot expect there to be a type of all types -- this type of "self-referentiality" can lead to logical problems. In Lean, there is a *universe* of all types, and this universe is called ``Type``. The statement that the real numbers are a type can be expressed as ``ℝ : Type``.

Here is another example. If ``G`` is a group, and ``g`` is an element of this group, then in set theory one might say that ``G`` is a set and ``g ∈ G`` is an element of the set. In type theory one says instead that ``G : Type`` and that ``g : G``.

The mental model which you should have in your mind is that in Lean, every object exists at one of three "levels". There are universes, such as ``Type``, there are types such as ``ℝ`` or ``G`` and there are terms such as ``37`` and ``g``. Every mathematical object you know fits neatly into this hierarchy. For example rings, fields and topological spaces are all types in Lean, and their elements are terms.

Function types
--------------

Say ``X`` and ``Y`` are types. The standard notation which you have seen for a function from ``X`` to ``Y`` is ``f : X → Y``. This is also the notation used in Lean. A mathematician might write ``Hom(X,Y)`` for the set of all functions from ``X`` to ``Y``. In Lean this set is of course a type, and the notation for this type is ``X → Y``. So ``f : X → Y`` says that ``f`` is a term of type ``X → Y``, i.e., the type theory version of the idea that ``f`` is an element of the set ``Hom(X,Y)``, or equivalently that ``f`` is a function from ``X`` to ``Y``.

The universe `Prop`
-------------------

Mathematicians define objects such as the real numbers and groups, but they also prove theorems about these objects. What is a theorem? It has two parts, a *statement* and a *proof*. Lean needs to be able to manipulate theorem statements and proofs as well as being able to manipulate objects such as the real numbers and groups. How do theorem statements and theorem proofs fit into the picture?

The answer to this question is beautifully simple. Lean regards a theorem statement as a type, not living in the ``Type`` universe, but in another universe called ``Prop`` -- the universe of true-false statements. A true-false statement, otherwise known as a *proposition* in this course, is a statement such as ``2+2=4`` or ``2+2=5`` or the Riemann hypothesis. Note in particular that we are reclaiming the word "proposition" from its traditional usage in other mathematics courses. You might have seen the word "proposition" being used to mean the same thing as "lemma" or "theorem" or "corollary" or "sublemma" or... . We don't need so many words to express the same idea, so in this course we will use the word "proposition" to mean the same thing as the logicians and the computer scientists: propositions, unlike theorems, can be false! A proposition is the same thing as a true-false statement. The notation ``P : Prop`` means that  ``P`` is a proposition. For example ``2 + 2 = 4 : Prop`` and ``2 + 2 = 5 : Prop``.

The idea that a proposition can be thought of as a type means in particular that a proposition has somehow got "elements". This is not the way that true-false statements are usually thought of by mathematicians, but it is a key idea in Lean's type theory. The "elements" (or, to use Lean's language, the terms) of a proposition are its proofs! Every proposition in Lean has *at most one term*. The true propositions have one term, and the false propositions have no terms. To give a concrete example, we have ``2 + 2 = 4 : Prop``, because 2+2=4 is a true-false statement. we will learn in this course how to make a term ``h : 2 + 2 = 4``; this term ``h`` should be thought of as a proof that 2+2=4. You could read it as the hypothesis that ``2 + 2 = 4`` or however you like, but under the hood what is happening is that ``h`` is a term of the type ``2 + 2 = 4``.

We also have the proposition ``2 + 2 = 5 : Prop``. It is however impossible to make a term whose type is ``2 + 2 = 5``, because 2+2=5 is a false proposition. If you like, you can think of ``2 + 2 = 4`` as a set with one element, and ``2 + 2 = 5`` as a set with no elements. This is initially a rather bizarre way of thinking about true-false statements, however you will soon get used to it.

The reason it is important to start thinking of elements of sets and proofs of propositions as "the same sort of thing", is that when formalising mathematics one frequently runs into things like the type of non-negative real numbers. To give a term of this type is to give a pair ``(x,h)`` consisting of a real number ``x`` and a proof ``h`` that ``x ≥ 0``, or, to put it in Lean's language, a term ``x : ℝ`` and a term ``h : x ≥ 0``. When doing mathematics like this in Lean, one just gets used to the fact that some variables are representing elements of sets and others are representing proofs of propositions.

``P ⇒ Q`` is ``P → Q``
----------------------

Here's an interesting analogy.

In the usual set-theoretic language which mathematicians use, we might say the following: If ``X`` and ``Y`` are sets, then we can consider the set ``Hom(X,Y)`` of functions from ``X`` to ``Y``, and an element ``f ∈ Hom(X,Y)`` is a function from ``X`` to ``Y``.

In Lean's type theory we say it like this: if ``X`` and ``Y`` are types in the ``Type`` universe, then we can consider the type ``X → Y`` of functions from ``X`` to ``Y``, and a term ``f : X → Y`` of this type is a function from ``X`` to ``Y``.

In usual mathematical logic, we might say the following: If ``P`` and ``Q`` are true-false statements, then ``P ⇒ Q`` is also a true-false statement (for example if ``P`` is true and ``Q`` is false, then ``P ⇒ Q`` is false). If we have a hypothesis ``h`` that says that ``P ⇒ Q`` is true, we might write ``h : P ⇒ Q``.

In Lean's type theory we say it like this. If ``P`` and ``Q`` are types in the ``Prop`` universe, i.e., propositions, then we can consider the type ``P → Q`` of functions from proofs of ``P`` to proofs of ``Q``. If we have such a function ``h``, which takes as input a proof of ``P`` and spits out a proof of ``Q``, then ``h`` can be thought of as a proof that ``P ⇒ Q``. In Lean the function type ``P → Q`` lives in the ``Prop`` universe -- it's also a true-false statement.

What Lean's type theory is suggesting here is that an interesting model for a true/false statement is a set with at most one element. If the set has an element, it corresponds to a true statement, and if it has no elements then it corresponds to a false statement.

As an exercise, imagine that ``P`` and ``Q`` are sets with either 0 or 1 element, and try and work out in each of the four cases the size of the set ``Hom(P,Q)``, which in Lean we would write as ``P → Q``. The answer you should get is that the size of ``Hom(P,Q)`` should be either 0 or 1, and it is 0 if ``P ⇒ Q`` is false, and 1 if ``P ⇒ Q`` is true.

Summary
-------

Types and their terms unify two mathematical concepts: sets and their elements,
and theorem statements and their proofs. The universe ``Type`` is where
the sets/elements types live, and the universe ``Prop`` is where the
theorems/proofs types live. An implication ``h : P ⇒ Q`` can be thought
of as a function ``h : P → Q`` from proofs of ``P`` to proofs of ``Q``.
