.. _tac_intros:

intros
======

Summary
-------

The ``intros`` tactic is a variant of the ``intro`` tactic, which can be used if the user wants to use ``intro`` several times. The tactic ``intros a b c`` is equivalent to ``intro a, intro b, intro c``.

Examples
--------

``intros h`` turns

.. code-block::

   ⊢ P → Q

into

.. code-block::

   h : P
   ⊢ Q

just as ``intro h`` would do. However

``intros hP hQ hR`` turns

.. code-block::

   ⊢ P → Q → R → S

into

.. code-block::

   hP : P
   hQ : Q
   hR : R
   ⊢ S

Similarly, ``intros x y z`` turns

.. code-block::

   ⊢ ∀ (a b c : ℕ), a + b + c = c + b + a

into

.. code-block::

   x y z : ℕ
   ⊢ x + y + z = z + y + x

Further notes
-------------

A variant of ``intros`` is :ref:`rintro <tac_rintro>`, which also enables multiple intros at once, as well as allowing the user do case splits on variables.

