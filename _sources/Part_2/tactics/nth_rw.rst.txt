.. _tac_nth_rw:

nth_rw
======

Summary
-------

If ``h : a = b`` then ``rw h`` turns *all* ``a`` s in the goal to ``b`` s. If you only want to turn one of the ``a`` s into a ``b``, use ``nth_rw``. For example ``nth_rw 2 [h]`` will change only the second ``a`` into ``b``.

Examples
--------

1) Faced with

.. code-block::

   h : x = y
   ⊢ x * x = a

the tactic ``nth_rw 1 [h]`` will turn the goal into ``⊢ y * x = a`` and ``nth_rw 2 [h]`` will turn it into ``⊢ x * y = a``. Compare with ``rw [h]`` which will turn it into ``⊢ y * y = a``.

2) ``nth_rw`` works on hypotheses too. If ``h : x = y`` is a hypothesis and ``h2 : x * x = a`` then ``nth_rw 1 [h] at h2`` will change ``h2`` to ``y * x = a``.

3) Just like ``rw``, ``nth_rw`` accepts ``← h`` if you want to change the right hand side of ``h`` to the left hand side.
   