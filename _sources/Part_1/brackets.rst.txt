Brackets in function inputs
===========================

This is about the different types of brackets which we see in Lean's functions.

If we type ``#check mul_assoc`` into Lean (assuming we've done ``import Mathlib.Tactic`` or some other import which imports some group theory) then we get the following output:

.. code-block::

   mul_assoc.{u_1} {G : Type u_1} [inst✝ : Semigroup G] (a b c : G) : a * b * c = a * (b * c)

At first glance, this makes some kind of sense: ``a * b * c`` means by definition ``(a * b) * c`` so we can see that this is some sort of claim that multiplication is associative. Looking more carefully, what is going on is that ``mul_assoc`` is a function, which takes as input a type ``G``, a semigroup structure with the weird name ``inst✝`` on ``G`` and three terms ``a``, ``b`` and ``c`` of ``G``, and returns a proof that ``(a * b) * c = a * (b * c)``. But what's with all the different kinds of brackets? We can see `{}`, `[]` and `()`. There's even a fourth kind, although it's rarer: try ``#check DirectSum.linearMap_ext`` to even see some ``⦃⦄`` brackets. These are the four kinds of brackets which you can use for function input variables. Here's a simple explanation of what they all mean.

``()`` brackets
---------------

These brackets are the easiest to explain. An input to a function in ``()`` brackets is an input which the user is expected to apply. For example, if we have a theorem ``double (x : ℕ) : 2 * x = x + x`` then ``double 37`` is the theorem that ``2 * 37 = 37 + 37``.

``{}`` and ``⦃⦄`` brackets
--------------------------

These brackets exist because Lean's type theory is dependent type theory, meaning that some inputs to functions can be completely determined by other inputs.

For example, the term ``Subgroup.mul_mem`` is a proof of the theorem stating that if two elements of a group are in a given subgroup, then their product is also in this subgroup. The type of this term is the following:

.. code-block::

   Subgroup.mul_mem.{u} {G : Type u} [inst✝ : Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H


So ``subgroup.mul_mem`` takes as input the following rather long list of things. First it wants a type ``G`` (the `u` is a universe -- ignore it). Then it wants a group structure on ``G``. Next it wants a subgroup ``H`` of ``G``, then two elements ``x`` and ``y`` of ``G``, and finally two proofs; first a proof that ``x ∈ H`` and second a proof that ``y ∈ H``. Given all of these inputs, it then outputs a proof that ``x * y ∈ H``.

Now let's imagine we're actually going to use this proof-emitting function to prove some explicit statement. We have some explicit group, for example the symmetric group :math:`S_5`, and some explicit subgroup `H` and some explicit permutations ``x`` and ``y`` in :math:`S_5`, and proofs ``hx`` and ``hy`` that ``x ∈ H`` and ``y ∈ H``. At the point where we feed in the input ``hx`` into ``subgroup.mul_mem``, Lean can look at ``hx`` and see immediately what ``x`` is (by looking at the type of ``hx``) and what ``G`` is (by looking at the type of ``x``). So, when you think about it, it's a bit pointless asking the *user* to explicitly supply
``G`` and ``x`` as inputs, even though the function needs them as inputs, because actually the type of the input ``hx`` (namely ``x ∈ H``) contains enough information to uniquely determine them.

Calculations like are what Lean's *unifier* does, and the ``{}`` and ``⦃⦄`` brackets are for this purpose; they mean that they are inputs to the function which the user need not actually supply at all; Lean will figure them out.

Technical note: The difference between ``{}`` and ``⦃⦄`` is that one is more *eager* than the other; this is all about the exact timing of the unifier. Basically if you have ``f (a : X) {b : Y} (c : Z)`` and ``g (a : X) ⦃b : Y⦄ (c : Z)`` then the unifier will attempt to figure out ``b`` in ``f`` the moment you have given it ``f a``, but it will only start worrying about ``b`` in ``g`` when you have given it ``g a c``. For an example where this matters, see `section 6.5 of Theorem Proving In Lean <https://lean-lang.org/theorem_proving_in_lean4/interacting_with_lean.html#more-on-implicit-arguments>`_ . If you want a rule of thumb: use ``{}``.

``[]`` brackets
---------------

Like ``{}`` brackets, these square brackets are inputs which the user does not supply, but which the system is going to figure out by itself. The ``{}`` brackets above were figured out by Lean's unification system. The ``[]`` brackets in this section are figured out by Lean's type class inference system.

Lean's type class inference system is a big list of facts. For example Lean knows that the reals are a field, that the natural numbers are an additive monoid, that the rationals have a 0 and a 1, etc etc. Which facts does this system know? The facts it knows are "instances of classes", or "instances of typeclasses" to give them their full name.

Let's take a look at ``add_comm``, the proof that addition is commutative. You can see its type with ``#check add_comm``. Its type is this:

.. code-block::

   add_comm.{u} {G : Type u} [inst✝ : AddCommMagma G] (a b : G) : a + b = b + a

An ``AddCommMagma`` is something a bit weaker than an additive commutative group; any abelian group with group law ``+`` is an ``AddCommMagma``.

The only inputs in round brackets to this proof are ``a`` and ``b``. Here's a short script which gives ``add_comm`` all the inputs it needs.

.. code-block::

   import Mathlib.Tactic

   def a : ℝ := 37
   def b : ℝ := 42

   #check add_comm a b -- add_comm a b : a + b = b + a

The ``add_comm`` function was given ``a``, and Lean knows that ``a`` has type ``ℝ`` because that's part of the definition of ``a``. So the unifier figures out that ``G`` must be ``ℝ``. The one remaining input to the function is a variable with the weird name of ``inst✝``, whose type is ``AddCommMagma ℝ``; you can think of it as "a proof that the reals are an additive commutative magma" but it's actually more than just a proof -- it's the data of the addition as well; the functions and constants as well as the proofs. Where does Lean get this variable ``inst✝`` from?

The answer is that in ``mathlib`` somewhere, someone proved that the real numbers were a field, and they tagged that result with the ``@[instance]`` attribute, meaning that the typeclass inference system now knows about it. The typeclass inference system knows that every field is an additive commutative group, and that every additive commutative group is an additive commutative magma. So the system throws this package together and fills in the ``inst✝`` input automatically for you. Basically this system is in charge of keeping all the group and ring proofs which we don't want to bother about ourselves.

You can add new facts into the typeclass system. Here's a way of telling Lean that you want to work with an abstract additive commutative group ``G``.

.. code-block::

   import Mathlib.Tactic

   variable (G : Type) [AddCommGroup G] (x y : G)

   #check add_comm x y -- add_comm x y : x + y = y + x

Instead of using concrete types like the reals, we make a new abstract type ``G``, give it the structure of an additive commutative group, and let ``x`` and ``y`` be abstract elements of ``G`` (or more precisely terms of type ``G``). The ``variable`` line has square brackets in too -- this means "add the fact that ``G`` is an additive commutative group to the typeclass system". Then when ``add_comm`` runs, the system will supply the proof that ``G`` is an additive commutative magma, so the function ``add_comm x y`` runs successfully and outputs a proof that ``x + y = y + x``.

Overriding brackets
-------------------

You may well never need to do this in this course, but I put it here for completeness.

Sometimes the system goes wrong, and Lean cannot figure out the inputs it was supposed to figure out by itself. If this happens, you can override the system like this:

.. code-block::

   import Mathlib.Tactic

   /-
   add_comm {G : Type} [inst✝ : AddCommMagma G] (a b : G) : a + b = b + a
   -/

   -- override `{}` input
   #check add_comm (G := ℝ) -- add_comm : ∀ (a b : ℝ), a + b = b + a

Alternatively, you can write `@add_comm`, and then every bracket will be treated as if it's `()`.