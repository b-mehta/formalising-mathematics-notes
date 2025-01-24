.. _wellformattedcode:

How to format your code well
============================

The first time this course ran I did not emphasize good code layout and when I was marking the projects I regretted this. Formatting your code correctly helps a great deal with readability (as I discovered) and so I now look more favourably on people who do this properly. The code I write in the course repository should always conform to the correct standards. Here are the basics.

Indentation
-----------

Code in a tactic block gets indented two spaces.

.. code-block::

   import Mathlib.Tactic

   example (a b : ℕ) : a = b → a ^ 2 = b ^ 2 := by -- `by` at the end
     intro h -- proof is indented two spaces in
     rw [h]

If you have a long theorem statement and want to write it over two or more lines
then you should indent subsequent lines with *four* spaces, for example:

.. code-block::

   import Mathlib.Data.Nat.Basic

   theorem le_induction {P : Nat → Prop} {m}
       (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) :
       ∀ n, m ≤ n → P n := by
     apply Nat.le.rec
     · exact h0
     · exact h1 _

Spaces between operators
------------------------

``a = b``, not ``a=b``. See above. Similarly ``a + b``, ``a ^ b`` and so on. Also ``x : T`` not ``x:T``, and ``foo := bar`` not ``foo:=bar``.

Comments
--------

You don't have to put a comment on every line of code, but please feel free to put comments at points where something is actually happening. Code with comments is easier to read. Just one line ``-- write explanation here`` above a tactic is already helpful. For multi-line
comments, use ``/-`` and ``-/``

Have only one goal
------------------

Sometimes you can end up with more than one goal. This can happen for two reasons. Firstly, perhaps you manually created a new goal. For example, perhaps you wrote ``have intermediate_result : a = b + c := by `` or ``suffices h : a = b + c by``. You just created an extra goal on top of the goal which was already there, so the proof should be indented two more spaces.

.. code-block::

   import Mathlib.Tactic

   example (a b c : ℕ) (h : a = b) : a ^ 2 + c = b ^ 2 + c := by
     have h2 : a ^ 2 = b ^ 2 := by -- you made a second goal
       rw [h]
       -- other lines of code would go here, also indented
     rw [h2] -- back to only two space indentation

The other way it can happen is if you use a tactic or apply a function which changes your old goal into more than one goal.

.. code-block::

   import Mathlib.Tactic

   example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
     constructor -- this tactic replaced the goal we were working on with two goals
     · -- so use the right kind of dot (`\.`) and work with one goal at a time
       exact hP
     · exact hQ -- note also extra indentation

Module docstrings
-----------------

For your projects, you might want to consider writing "module docstrings", which is a fancy
name for "a big comment at the top of each file explaining what happens in the file." Look
at any file in mathlib to see an example, or you can see one `here <https://leanprover-community.github.io/contribute/doc.html>`_ .

Want to know more?
------------------

Check out the mathlib library style guidelines `on the Lean community pages <https://leanprover-community.github.io/contribute/style.html>`_ -- not all of it applies to us, but most of the section on tactic mode does.
