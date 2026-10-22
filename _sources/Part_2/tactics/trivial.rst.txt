.. _tac_triv:

triv
====

Summary
-------

The ``triv`` tactic proves ``⊢ True``.

It also proves goals of the form ``x = x`` and more generally of the form ``x = y`` when ``x`` and ``y`` are definitionally equal, but traditionally people use ``rfl`` to do that.

Examples
--------

If your goal is

.. code-block::

   ⊢ True

then it's pretty triv, so try ``trivial``.

Details
-------

Note that ``True`` here is the true proposition. If you know a proof in your head that the goal is true, that's not necessarily good enough.

Further notes
-------------

The ``constructor`` tactic also proves a ``True`` goal, although you would have to learn a bit about inductive types to understand why.



