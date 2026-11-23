.. _structures:

Structures
==========

A lot of the time in this course we are concerned with proving theorems. However sometimes it's interesting to make a new definition, and then prove theorems about the definition. In section 3 we made things like groups, subgroups, and group homomorphisms from first principles, even though mathlib has them already. We made them using structures and classes. 

Let's start by talking about the structure ``Equiv X Y``, with notation ``X ≃ Y``.

`Equiv` -- two inverse bijections
---------------------------------

Let `X` and `Y` be types. Here's how ``mathlib`` defines a type ``X ≃ Y``
whose elements are bijections from ``X`` to ``Y``.

.. code-block::

   /-- `X ≃ Y` is the type of functions from `X` to `Y` with a two-sided inverse. -/
   structure Equiv (X Y : Type) where
     toFun : X → Y
     invFun : Y → X
     left_inv : LeftInverse invFun toFun
     right_inv : RightInverse invFun toFun

   infixl:25 " ≃ " => Equiv

What's going on here? The actual name of the type is ``Equiv X Y``, and we set up
a (left-associative, binding power 25) notation ``X ≃ Y`` for it (as a rule of thumb,
if it's a funny maths character then it's notation, and if it's spelt out in normal
letters it's the official name). The line starting with ``/--`` is the docstring
for the definition; this ensures that when you hover over ``Equiv`` you can
see its definition. Note that every definition you write should have a docstring!

The structure we're defining here has four *fields*: two functions and two proofs.
To make a term of this type, you have to supply four things: 

(1) a map from ``X`` to ``Y``
(2) a map from ``Y`` to ``X``
(3) a proof that if you do the map from ``X`` to ``Y`` and then the map from ``Y`` to ``X`` you get back to where you started;
(4) same as (3) but start at ``Y`` then go to ``X`` then back to ``Y``.

In other words, you need to supply two maps and then a proof that one is the two-sided inverse
of the other.

If you have read something about inductive types -- ``X ≃ Y`` is an inductive type,
with one constructor (called ``Equiv.mk`` internally) which takes as inputs the four
things above, and then outputs a term of type ``X ≃ Y``.

Let's let ``X`` and ``Y`` both be the integers, and let's let the map from ``X`` to ``Y``
send ``n`` to ``n+37``. Then the inverse map sends ``n`` to ``n-37``, and the ``ring``
tactic will be able to prove that ``(n+37)-37=n``, so we should be able to make a term
of type ``ℤ ≃ ℤ`` using this data. Let's call it ``e``. By the way, I started writing
this definition by typing ``def e : ℤ ≃ ℤ := _`` and then clicking on the blue lightbulb
and selecting the option which mentioned structures.

.. code-block::

   def e : ℤ ≃ ℤ where
     toFun n := n + 37 
     invFun m := m - 37 
     left_inv := by
       intro n
       -- some messy goal with a bunch of ``fun`` in
       dsimp only -- tidy up
       -- ⊢ n + 37 - 37 = n
       ring
     right_inv := by
       intro m
       ring -- don't actually need to tidy up

You can think of ``e`` as a 4-tuple: two functions, and two proofs. How do you get this information
from the term ``e``? You can use functions like ``Equiv.toFun`` etc, which were created under
the hood when ``Equiv`` was defined. Here are some examples of how to use the "parts" of ``e``.
Note that because the type of ``e`` is ``Equiv [something]``, ``e.toFun`` is short for
``Equiv.toFun e``. This is Lean's :ref:`dot notation <dot_notation>` in action.

.. code-block::

   #check Equiv.toFun e -- ℤ → ℤ
   #check e.toFun -- ℤ → ℤ

   example : e.toFun 1 = 38 := by
     simp only [e] -- replace ``e`` with its definition
     -- ⊢ 1 + 37 = 38
     norm_num

   example (x : ℤ) : e.invFun x = x - 37 := by
     rfl

   example : ∀ x : ℤ, e.invFun (e.toFun x) = x := 
     e.left_inv  

The final thing I'll explain is the *coercion* associated to the bijection. We sometimes want to think of
``e`` as a function from ``ℤ`` to ``ℤ``, and forget the fact that it's really an ``Equiv``. We could
do this by talking about ``e.toFun`` all the time, but Lean will just let you use ``e`` as a function:

.. code-block::

   example : e 1 = 38 := by
     dsimp [e]
     -- ⊢ 1 + 37 = 38
     norm_num

Lean has things called :ref:`coercions <coercions>`. This is a way that given a term ``x`` of one type, you can "pretend" that it has a different type. What is actually happening is that a function which is essentially invisible to mathematicians is being called; it sends a bijection to the associated function! There's a coercion defined from ``Equiv X Y``
to ``X → Y`` and this coercion is applied automatically when ``e`` receives the "input" ``1``.

