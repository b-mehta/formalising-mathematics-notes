.. _tac_by_cases:

by_cases
========

Summary
-------

All propositional logic problems can in theory be solved by just throwing a truth table at them. The ``by_cases`` tactic is a simple truth table tactic: ``by_cases P`` turns one goal into two goals, with ``P`` is assumed in the first, and ``¬P`` in the second.

Examples
--------

1) If ``P`` is a proposition, then ``by_cases hP : P`` turns your goal into two goals, and in each of your new tactic states you have one extra hypothesis. In the first one you have a new hypothesis ``hP : P`` and in the second you have a new hypothesis ``hP : ¬P``.

2) Note that if you just write ``by_cases P`` then Lean will call the hypothesis ``h✝`` which is its way of saying "if you don't name your hypotheses then I will give them names which you can't use".

Details
-------

For those of you interested in constructive mathematics (a weakened form of mathematics much beloved by some computer scientists), the ``by_cases`` tactic (like the :ref:`tac_by_contra` tactic) is not valid constructively. We are doing a case split on ``P ∨ ¬P``, and to prove ``P ∨ ¬P`` in general we need to assume the law of the excluded middle. In this course we will not be paying any attention to any logic other than classical logic, meaning that this case split is mathematically valid.

Further notes
-------------

There's a much higher powered tactic which does case splits on all propositions and grinds everything out: the ``tauto`` tactic. The ``tauto`` tactic probably proves every goal in all the questions in section 1 of the course repo, however you won't learn any other tactics if you keep using it!


