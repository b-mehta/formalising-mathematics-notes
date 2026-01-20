Installing Lean
===============

Here's an example of a simple logic proof in Lean.
It's a proof that that if ``P`` and ``Q`` are propositions
(that is, true/false statements), and if ``P``
is true and ``P ⇒ Q`` is true, then ``Q`` is true.

.. code-block:: console

   example (P Q : Prop) (h1 : P) (h2 : P → Q) : Q := by
     apply h2 at h1
     exact h1

The first line of the code states the theorem. Hypothesis
``h1`` is that ``P`` is true, and hypothesis ``h2`` is
that ``P`` implies ``Q`` (note that Lean uses a regular
arrow for implication rather than the more common ``⇒``
sign). The conclusion, after the colon,
is that ``Q`` is true. The proof is after the ``by``,
which puts Lean into "tactic mode" (``apply`` and ``exact`` are tactics),
and it's clear that it somehow uses
both hypothesis ``h1`` and hypothesis ``h2``. But
just reading the proof, it's hard to see exactly what
is going on. We can't learn Lean this way.

The whole point of using a theorem prover is that it makes
proofs like this *interactive*. So, before we get going,
we need to get this and other proofs running on your computer somehow.
There are several ways to do it.

The best way: install Lean on your computer
-------------------------------------------

If you are doing this course in 2026 at Imperial, and your computer
is powerful enough to run Lean reasonably quickly, and you have about 4.5
gigabytes of space available to install Lean and the course repository, then I recommend
this method.

You will first need to install Lean, and then you'll need to
install the course repository.

Instructions on how to get Lean installed on your computer
are `here <https://leanprover-community.github.io/get_started.html>`_
(right click and open in new tab if you don't want to lose your place).

Once you have Lean up and running, you can install the repository
``b-mehta/formalising-mathematics-notes`` associated with this
course. Fire up VS Code, click on the upside-down `A` in the bar at the top,
hover on "Open Project",
click on "Project: Download project", and then in the text box type
``https://github.com/b-mehta/formalising-mathematics-notes``.
Navigate to the directory where you want to put the course repository,
type in a name (e.g. ``formalising-mathematics``), click on "Create project folder",
and then for a minute or two for everything to download.

You can now use VS Code's "open folder" functionality to open the
course repository and it should all work fine.

Lean in a web browser
----------------------

If your computer is too slow to run Lean satisfactorily, or you don't have enough
space on your computer, you can use Lean via a web browser. Note: I am not in any
position to guarantee that with either of the approaches below, any code you write
will survive between browser sessions. I recommend that if you write your course
projects using a browser approach then you *save all your work locally*.
You will probably need to register an account of some form (for example a GitHub account)
with either of the two approaches below.

Browser approach 1: via gitpod.
-------------------------------

Right click here
<https://gitpod.io/#/https://github.com/b-mehta/formalising-mathematics-notes>`_
and "open link in new tab" to access the repository using Gitpod. At some point it will give
you some options and ask you to continue; accepting the default options is fine.
I strongly recommend that you do not do *anything* until all the downloading has finished
and the output in the terminal window has completely stopped; this may take several minutes.
When it's done, you should see a VS Code session in your browser, and the output
should end with something like ``Decompressing 4053 file(s)``
and ``unpacked in 21359 ms`` as the last couple of lines. Open the
file `FormalisingMathematics2026/Section01logic/Sheet1.lean` to check it's working.
Wait to check that the orange bars disappear and the infoview responds as you click
between the different examples in the file.

Note: I believe there is some time limit for the amount that you can use gitpod
for free. You might find that you can extend this limit by registering as a student
on github.com

Browser approach 2: via Codespaces
----------------------------------

Right click here
<https://github.com/b-mehta/formalising-mathematics-notes>`_
and "open link in new tab" to go to the github page where the course
repository is stored. I think that you'll need to have an account on github
for this to work? Click on the green "Code" button and then click on
"Codespaces". Then click on the green "Create codespace on main".
Again, wait for several minutes until everything is completely finished. Open the
file `FormalisingMathematics2026/Section01logic/Sheet1.lean` to check it's working.
Wait to check that the orange bars disappear and the infoview responds as you click
between the different examples in the file.

