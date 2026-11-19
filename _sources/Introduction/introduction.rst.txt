.. _introduction:

Introduction
============

These are the notes for a course which is delivered to final year undergraduates and MSc students in
the mathematics department at Imperial College London. I hope that they will also be useful to other
mathematicians.

Aims and objectives
-------------------

The aim of the course is to teach people how to *formalise* undergraduate and MSc level mathematics
in a *computer proof assistant*. A computer proof assistant is a computer program which knows the
axioms of mathematics and is capable of understanding and checking mathematical proofs. To formalise
mathematics means to type it into a computer proof assistant.

Another way of looking at it is that a computer proof assistant turns the statement of a theorem of
mathematics into a level of a puzzle game, and proving the theorem corresponds to solving the level.
Hence another way of thinking about the aims and objectives of this course are that I am teaching
you how to set and how to solve levels of a computer puzzle game.

The methods used in this course are extremely "hands-on". You will be learning by doing. Every topic
will be introduced via examples and you will be expected to learn it by solving problems.


Why formalise?
--------------

My personal belief is the following. Software of this nature will become more normalised in
mathematics departments, and libraries of formalised theorems will begin to grow quite large.
Computer theorem provers will ultimately give rise to tools which will help humans to learn and to
do mathematics, from undergraduate level to the `frontiers of modern research
<https://github.com/teorth/pfr>`_. Complex tactics, perhaps backed by AI, will in the future start
to help human researchers. PhD students will be able to search these libraries to get hints on how
to proceed, or find references for claims which they hope are true. Other applications will appear
as mathematicians begin to understand the potential of formalised libraries of mathematics and of
computer programs which can understand them.

The Lean Theorem Prover
-----------------------

There are many computer proof assistants out there; the one we shall be using is called
`Lean <https://lean-fro.org/>`_. We will be using not just Lean, but also Lean's `mathematics
library <https://github.com/leanprover-community/mathlib4/>`_, ``mathlib``, which contains a
substantial number of proofs of mathematical theorems already, as well as many high-powered
*tactics*, tools which make theorem proving easier. There are many other theorem provers out
there; Isabelle/HOL and Coq are two other provers which have also been used to formalise a
substantial amount of mathematics. The reason we are using Lean is simply that it is the prover
which I myself am most familiar with; I do not see any obstruction in theory to porting this entire
course over to another theorem prover.

Prerequisites
-------------

Experience has shown that trying to teach people new mathematics at the same time as teaching them
Lean is asking too much from most people. I will hence be assuming that the reader/player is
comfortable with the material covered in the first and second year of a traditional mathematics
degree. Later on, when the reader is more familiar with Lean I will introduce more mathematically
challenging material.

This course is focussed on mathematics, or to be more precise, classical mathematics. We will not be
concentrating on the non-mathematical side of the story. Examples of topics we will say very little
about are: type theories, functional programming, the lambda calculus, and constructivism.


How to read this document
-------------------------

These notes comes in two parts: Part 1, Part 2.

Part 1 is the non-mathematical background which you will find helpful in order to make sense of what
is going on. It covers basic material of a more "computer-science" nature. I will flag in the
exercises the time when it might be helpful to read sections from this part.

Part 2 is a glossary of many common tactics. The problem sheets in the course repository will flag
which tactics you need to learn about and when.