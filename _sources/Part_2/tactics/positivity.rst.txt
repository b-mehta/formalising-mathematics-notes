.. _tac_positivity:

positivity
==========

Summary
-------

This a tactic which solves certain goals of the form ``0 ≤ x``, ``0 < x`` and ``x ≠ 0``.

Details
-------

``positivity`` knows certain "tricks" (for example it knows that if ``a>0`` and ``b>0`` then ``a+b>0``), and tries to solve the goal using only these tricks. More generally it takes the goal apart, tries to prove the relevant analogue of the goal for all the pieces, and then tries to find lemmas which glue everything together.

Examples
--------

1) ``positivity`` will solve this:

.. code-block::

   x y : ℝ
   hx : x > 37
   hy : y > 42
   ⊢ x * y > 0

2) It will also solve this:

.. code-block::

   x y : ℝ
   hx : x ≠ 0
   hy : y ≠ 0
   ⊢ 2 * x * y ≠ 0

3) And this:

.. code-block::

   x y : ℝ
   hy : y ≥ 0
   ⊢ 37 * x ^ 2 * y ≥ 0


