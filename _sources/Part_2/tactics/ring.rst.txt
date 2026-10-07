.. _tac_ring:

ring
====

Summary
-------

The ``ring`` tactic proves identities in commutative rings such as ``(x+y)^2=x^2+2*x*y+y^2``. It works on concrete rings such as ``ℝ`` and abstract rings, and will also prove some results in "semirings" such as ``ℕ`` (which isn't a ring because it doesn't have additive inverses).

Note that ``ring`` does not and cannot look at hypotheses. See the examples for various ways of working around this.

Examples
--------

1) A basic example is

.. code-block::

   example (x y : ℝ) : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by
   ring

2) Note that ``ring`` cannot use hypotheses -- the goal has to be an
identity. For example faced with

.. code-block::

   x y : ℝ
   h : x = y ^ 2
   ⊢ x ^ 2 = y ^ 4

the ``ring`` tactic will not close the goal, because it does not know about ``h``. The way to solve this goal is ``rw [h]`` and *then* ``ring``.

3) Sometimes you are in a situation where you cannot ``rw`` the hypothesis you want to use. For example if the tactic state is

.. code-block::

   x y : ℝ
   h : x ^ 2 = y ^ 2
   ⊢ x ^ 4 = y ^ 4

then ``rw h`` will fail (of course we know that ``x^4=(x^2)^2``, but ``rw`` works up to syntactic equality and it cannot see an ``x^2`` in the goal). In this situation we can use ``ring`` to prove an intermediate result and then rewrite our way out of trouble. For example this goal can be solved in the following way.

.. code-block::

   example (x y : ℝ) (h : x ^ 2 = y ^ 2) : x ^ 4 = y ^ 4 := by
     rw [show x ^ 4 = (x ^ 2) ^ 2 by ring] -- prove x^4=(x^2)^2, rewrite with it, forget it
     -- goal now `⊢ (x ^ 2) ^ 2 = y ^ 4`
     rw [h]
     -- goal now `⊢ (y ^ 2) ^ 2 = y ^ 4`
     ring

It can also be solved in the following way:

.. code-block::

   example (x y : ℝ) (h : x ^ 2 = y ^ 2) : x ^ 4 = y ^ 4 := by
   convert_to (x ^ 2) ^ 2 = y ^ 4
   -- creates new goal ⊢ x ^ 4 = (x ^ 2) ^ 2
   · ring -- solves this new goal
   -- goal now `⊢ (x ^ 2) ^ 2 = y ^ 4`
   rw [h]
   -- goal now `⊢ (y ^ 2) ^ 2 = y ^ 4`
   ring

Further notes
-------------

``ring`` is a "finishing tactic"; this means that it should only be used to close goals. If ``ring`` does not close a goal it will issue a warning that you should use the related tactic ``ring_nf``.

The algorithm used in the ``ring`` tactic is based on the 2005 paper "Proving Equalities in a Commutative Ring Done Right in Coq" by Benjamin Grégoire and Assia Mahboubi.