.. _tac_cheatsheet:

Tactic cheatsheet
=================

If you think you know which part of the tactic state your "next move"
should relate to (i.e. you know whether you should be manipulating the goal
or using a hypothesis) then the below table might give you a hint
as to which tactic to use.

.. list-table:: Cheat sheet
   :widths: 25 25 50
   :header-rows: 1

   * - Form of proposition
     - In the goal?
     - Hypothesis named ``h``?
   * - ``P → Q``
     - ``intro hP``
     - ``apply h`` (if goal is ``Q``) or ``apply h at...``
   * - ``True``
     - ``trivial``
     - (can't be used)
   * - ``False``
     - (can't be used)
     - ``exfalso, exact h`` or ``cases h``
   * - ``¬P``
     - ``intro hP``
     - ``apply h`` (if goal is ``False``)
   * - ``P ∧ Q``
     - ``constructor``
     - ``cases' h with hP hQ``
   * - ``P ↔ Q``
     - ``constructor``
     - ``rw h`` (or ``cases' h with h1 h2``)
   * - ``P ∨ Q``
     - ``left`` or ``right``
     - ``cases' h with hP hQ``
   * - ``∀ (a : X), ...``
     - ``intro x``
     - ``specialize h x``
   * - ``∃ (a : X), ...``
     - ``use x``
     - ``cases' h with x hx``
