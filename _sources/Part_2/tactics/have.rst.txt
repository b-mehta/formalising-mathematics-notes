.. _tac_have:

have
====

Summary
-------

The ``have`` tactic lets you introduce new hypotheses into the system.

Examples
--------

1) If you have hypotheses

.. code-block::

   hPQ : P → Q
   hP : P

then from these hypotheses you know that you can prove ``Q``. If your *goal* is ``Q`` then you can just ``apply hPQ`` then ``exact hP``, or ``exact hPQ hP``. But if you need ``Q`` for some other reason (e.g. perhaps ``Q`` is of the form ``x = y`` and you want to rewrite it) then one way of making it is by writing ``have hQ : Q := by``. This creates a *new goal* of ``Q``, which you can prove with ``apply hPQ``, ``exact hP``, and after this you'll find that you have a new hypothesis ``hQ : Q`` in your tactic state.

2) If you can directly write the term of the type that you want to have, then you can do it using ``have hQ : Q := ...``. For instance, in the example above you could write ``have hQ : Q := hPQ hP``, because ``hPQ`` is a function from proofs of ``P`` to proofs of ``Q`` so you can just feed it a proof of ``P``.

Further notes
-------------

The ``let`` and ``set`` tactics are related; they are however used to construct data rather than proofs.
