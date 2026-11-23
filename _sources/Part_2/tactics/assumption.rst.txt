.. _tac_assumption:

assumption
==========

Summary
-------

The ``assumption`` tactic closes a goal ``⊢ P`` when there is a hypothesis ``h : P``. Note that ``exact h`` also closes this goal, and is shorter too, so only use this when the name of the hypothesis is five or more letters long ;-) Other uses include when one is trying to be clever and using ``<;>`` to solve more than one goal at once.

Examples
--------

1) Faced with the goal

.. code-block::

   reallylonghypothesisname : P
   h1 : Q
   h2 : 2 + 2 = 5
   ...
   h100 : x = x
   ⊢ P

you could do ``exact reallylonghypothesisname`` but ``assumption`` works as well. Although what are you doing with a really long hypothesis name?

2) If your tactic state is

.. code-block::

   hP : P
   hQ : Q
   ⊢ P ∧ Q

you can do ``constructor <;> assumption``. The ``<;>`` means "do ``constructor`` and then do ``assumption`` on all goals produced by ``constructor``".

Further notes
-------------

If you decide that you are interested in learning how to *write* tactics then ``assumption`` is usually a good one to try and write
(you loop through the hypotheses, trying to close the goal with each one). Note that there will be nothing about tactic writing in this course because the author doesn't have the first clue about it.
