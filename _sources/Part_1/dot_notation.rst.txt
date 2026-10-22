.. _dot_notation:

Dot notation
============

Say you have a type, like ``Subgroup G``, and a term of that type, like ``H : Subgroup G``. Say you have a function in the ``Subgroup`` namespace which takes as input a term of type ``Subgroup G``, for example ``Subgroup.inv_mem``, which has as an explicit input a term ``H : Subgroup G`` and spits out a proof that ``x ∈ H → x⁻¹ ∈ H``. Then instead of writing ``Subgroup.inv_mem H : x ∈ H → x⁻¹ ∈ H`` you can just write ``H.inv_mem : x ∈ H → x⁻¹ ∈ H``.

In general the rule is that if you have a term ``H : Foo ...`` of type ``Foo`` or ``Foo A B`` or whatever, and then you have a function called ``Foo.bar`` which has an explicit (i.e., round brackets) input of type ``Foo ...``, then instead of ``Foo.bar H`` you can just write ``H.bar``. This is why it's a good idea to define theorems about ``Foo``s in the ``Foo`` namespace.

This sort of trick can be used all over the place; it's surprisingly powerful. For example Lean has a proof ``Eq.symm : x = y → y = x``. If you have a term ``h : a = b`` then, remembering that ``=`` is just notation for ``Eq`` so that ``h`` really has type ``Eq a b``, you can write ``h.symm : b = a`` as shorthand for ``Eq.symm h``.

