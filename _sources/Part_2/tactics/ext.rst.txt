.. _tac_ext:

ext
===

Summary
-------

The ``ext`` tactic applies "extensionality lemmas". An extensionality lemma says "two things are the same if they are built from the same stuff". Examples: two subsets of a type are the same if they have the same elements, two subgroups of a group are the same if they have the same elements, two functions are the same if they take the same values on all inputs, two group homomorphisms are the same if they take the same values on all inputs. 

Examples
--------

1) Here we use the ``ext`` tactic to prove that two group homomorphisms are equal if they take the same values on all inputs.

.. code-block::

   import Mathlib.Tactic

   example (G H : Type) [Group G] [Group H] (φ ψ : G →* H)
       (h : ∀ a, φ a = ψ a) : φ = ψ := by
     -- ⊢ φ = ψ
     ext g
     -- ⊢ φ g = ψ g
     apply h -- goals accomplished

2) Here we use it to prove that two subgroups of a group are equal if they contain the same elements.

.. code-block::

   import Mathlib.Tactic

   example (G : Type) [Group G] (K L : Subgroup G)
       (h : ∀ a, a ∈ K ↔ a ∈ L) : K = L := by
     -- ⊢ K = L
     ext g
     -- ⊢ g ∈ K ↔ g ∈ L
     apply h
     done

Details
-------

What the ``ext`` tactic does is it tries to ``apply`` lemmas which are tagged with the `@[ext]` attribute. For example if you try ``#check Subgroup.ext`` you can see that it's exactly the theorem that if ``∀ (x : G), x ∈ H ↔ x ∈ K`` then ``H = K``. This theorem was tagged with ``@[ext]`` when it was defined, which is why the ``ext`` tactic makes progress on the goal.

Further notes
-------------

Sometimes ``ext`` applies more lemmas than you want it to do. In this case you can use the less aggressive tactic ``ext1``, which only applies one lemma.

