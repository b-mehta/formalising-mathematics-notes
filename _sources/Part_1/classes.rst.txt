.. _classes:

Classes
=======

In the previous section, we saw how to make structures. Here is another example of a structure:
the structure of a group homomorphism.

.. code-block:: lean

   import Mathlib.Tactic

   structure GroupHom (G H : Type) [Group G] [Group H] where
   /-- The underlying function -/
   toFun : G → H
   /-- The proposition that the function preserves multiplication -/
   map_mul : ∀ x y : G, toFun (x * y) = toFun x * toFun y

If ``G`` and ``H`` are groups, then a to give a group homomorphism from ``G`` to ``H`` is to give a function from ``G`` to ``H`` which preserves multiplication, so a term of type ``GroupHom G H`` is a *pair*, consisting of a function and a proof. But what does that ``[Group G]`` mean and why is it in weird brackets?

So the deal is that ``Group`` is a *class*, which is simply a structure tagged with the ``@[class]`` attribute. The definition of a group might look like this (I'll call it ``MyGroup`` because ``Group`` is already used):

.. code-block:: lean

   import Mathlib.Tactic

   class MyGroup (G : Type) extends Mul G, One G, Inv G where
   mul_assoc (a b c : G) : (a * b) * c = a * (b * c)
   one_mul (a : G) : 1 * a = a
   mul_one (a : G) : a * 1 = a
   mul_left_inv (a : G) : a⁻¹ * a = 1
   mul_right_inv (a : G) : a * a⁻¹ = 1
   
The ``extends Mul G`` etc stuff just means "assume ``G`` already has a ``*`` defined on it", so ``a * b`` makes sense if ``a b : G``. 
Similarly we assume there's an element of ``G`` called ``1``, and that if ``a : G`` then there's an element ``a⁻¹ : G``. The structure
of a group on ``G`` is then, on top of this data, proofs of the axioms of a group.

So why is this a ``class``, whereas group homomorphisms were a ``structure``? Mathematically a group and a group homomorphism are just the same sort of object: both are a "list of stuff". The difference is in how we want to use this stuff. If ``φ`` is a group homomorphism then we would expect to mention ``φ`` explicitly when talking about it, and there can be more than one group homomorphism between two groups. In contrast, we would only usually expect one group structure (with group law ``*``) on a type ``G``, rather than the option of moving between several. Furthermore, if we have a group structure ``i`` on a type ``G`` then we would *not* expect to keep having to mention ``i`` (which is a big list consisting of a multiplication, identity, inverse and proof of five axioms) explicitly, we just want to write ``g * h`` if ``g h : G`` and don't want to talk about ``i.mul`` or whatever it would be called. We just want the multiplication notation to *work*.

Lean's *typeclass inference system* (or "square bracket system") informally keeps track of classes and instances, meaning that we can write mathematics naturally without having to write down names of structures which are invisible to mathematicians. We don't say "let ``G`` be a set and let ``i`` be a group structure on ``G``"; similarly we don't have to name ``i : Group G`` here; we just write ``[Group G]`` and Lean assigns some internal name like ``inst✝ : Group G`` to the package. Let's take a look at the type of ``mul_left_inv``:

.. code-block:: lean

  mul_left_inv {G : Type} [inst✝ : Group G] (a : G) : a⁻¹ * a = 1

If we try to use this theorem (e.g. with ``rw [mul_left_inv]`` when our goal is ``x = a⁻¹ * a``) then Lean looks at the type of ``a`` (which could be an abstract type like ``G`` or a concrete type like ``ℕ``, supplies the type of ``a`` as the first input ``G`` to ``mul_left_inv``, and then asks the square bracket machine to look through its big list of *instances* to see if it can find a term of type ``Group G``. If it can, then it will use that term to fill in the second input to ``mul_left_inv``. If it can't, then it will complain that it can't find a group structure on ``G``. So the square bracket system is a way of telling Lean "I want to use the group structure on ``G``" without having to name it.

Summary
-------

We use structures when there is likely to be more than one term of the relevant type (e.g. it's fine to consider several group homomorphisms from ``G`` to ``H``) and we use classes when there is likely to be only one term of the relevant type (e.g. it would be very confusing to have two group structures on ``G`` both with group law written ``*``, so it's safe to make ``Group G`` into a class). Under the assumption that there is only ever going to be at most one instance of a class, the typeclass inference system (or square bracket system) can be used to find it.
