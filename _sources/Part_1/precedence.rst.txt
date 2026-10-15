Notation and precedence
=======================

This is about why ``a + b + c`` means ``(a + b) + c`` but why ``a + b * c`` means ``a + (b * c)`` in Lean.

Functions and brackets
----------------------

As you might have spotted, functions in Lean don't need brackets for their inputs.

.. code-block::

   example (f : ℕ → ℕ) (a : ℕ) : f (a) = f a := by
     rfl

In fact Lean is keen to drop brackets wherever they are not required: if you look at the goal before ``rfl`` in the proof above it says ``⊢ f a = f a``. Similarly if you check that multiplication is associative on the naturals:

.. code-block::

   import Mathlib.Tactic
   
   example (a b c : ℕ) : (a * b) * c = a * (b * c) := by
     ring

then the goal before ``ring`` is displayed as ``⊢ a * b * c = a * (b * c)``, with ``a * b * c`` instead of ``(a * b) * c``. What's going on here?

Lean's `parser` has the job of changing human input (strings) into abstract Lean terms, and for reasons we'll get to later, it parses ``a * b * c`` as ``(a * b) * c``. Lean's *pretty printer* has the job of changing Lean terms back into strings so that the tactic state can be displayed on the screen, and it will drop brackets wherever possible, so it will change ``(a * b) * c`` back into ``a * b * c``. If you try the above example in VS Code and hover over each of the ``*`` s in the infoview (the tactic state), you will see a way of figuring out where Lean internally puts the brackets (try it to see what I mean).

So what is going on here? When are brackets needed, and where does Lean put them?

Functions are greedy
--------------------

Lots of things in Lean are functions (in fact probably more things than you expect are functions). And in Lean, functions are *greedy* -- they will eat the next thing they see. So here is an example where one pair of brackets are needed:

.. code-block::

   example (X Y Z : Type) (f : X → Y) (g : Y → Z) (x : X) : Z := g (f x)

If you just write `g f x` then `g` will eat `f` instead of `f x`, and then it will complain that what it ate didn't have the right flavour, i.e. the right type. Try the example above in Lean, and then remove the brackets and read the error message -- this is an error message you will see a lot as you're learning Lean, so it's a good one to understand.

Of course it's fine to put in too many brackets: Lean will be happy with ``g (f (x))``, it's just that the brackets around the ``x`` are not necessary.

Functions vs notation
---------------------

In Lean ``+`` is a thing, but it's not actually the name of a function. There is no ``definition + : X → X → X`` anywhere in Lean because ``+`` is just *notation*. The actual function is called ``hAdd`` (or, to be completely pedantic, ``HAdd.hAdd``), and then somewhere in core Lean there is the line

.. code-block::

   infixl:65 " + "   => HAdd.hAdd

which assigns *notation* to the ``hAdd`` function. Basically this just means that if the parser sees ``a + b`` it will parse it as ``hAdd a b`` (or, to be completely pedantic, ``HAdd.hAdd a b``). Now all functions are equally greedy -- but notation is not. Both addition and multiplication are functions, but as we know from BIDMAS, we want Lean to parse multiplication before addition, so the system will somehow need to know that notation for multiplication has a higher "score" than notation for addition. And if we look in core Lean, in the file `Notation.lean`, just below the definition of `+` we see

.. code-block::

   infixl:70 " * "   => HMul.hMul
   
which should give you a clue. The *binding power* of a notation is a number associated to it when the notation is defined, and the larger the number, the more tightly the notation binds. Functions are greedy -- function application has binding power 1024. Because ``1024 > 70 > 65``, this is why Lean's parser parses ``f x * y`` as ``f(x) * y`` and ``a + b * c`` as ``a + (b * c)``. Also the ``l`` in ``infixl`` means "make this notation left associative"; compare this to 

.. code-block::

   infixr:80 " ^ "   => HPow.hPow

which makes exponentiation right associative (the reason for this is that ``(a^b)^c`` can be simplified to ``a^(b*c)`` so is not as useful as ``a^(b^c))``.  

Examples of binding power
-------------------------

As we've seen, ``+`` has binding power 65, and binary ``-`` (that is, the function which takes two variables ``a`` and ``b`` and returns ``a - b``) also has binding power 65. There is also unary ``-``, which is notation for the function which takes one variable ``a`` and returns ``-a``, and this has binding power 75. Multiplication and division have binding power 70. As a result, ``-b / c`` means ``(-b) / c`` but ``a - b / c`` means ``a - (b / c)``.

All notation has a binding power! Lean's version of BIDMAS does not just work for arithmetic operators like `+` and `*`, notation like `∧` and even `=` has a binding power. 
Here are some examples of binding powers:

.. code-block::

  ∨ : 30
  ∧ : 35
  ¬ : 40
  = : 50
  + : 65
  - : 65 (binary)
  * : 70
  / : 70
  - : 75 (unary)
  ^ : 80
  ⁻¹ : 1024




