/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!
# Lecture 8: Classes
-/

set_option linter.style.longLine.maxLineLength 80 -- for lectures

@[expose] public section

/-
In this lecture we will discuss how algebraic structures like groups and rings
are formalized in Lean and mathlib. Perhaps the most obvious approach would be
to define a type of all groups, a type of all rings, and so on. The problem with
this approach is that every term has a unique type so every mathematical object
(e.g., the real numbers) would either need to pick a type once and for all or
would need to be duplicated for every possible type. You might think that there
might always be a reasonable choice of type for any given mathematical object.
For instance, the real numbers are characterized as being the unique complete
linearly ordered field, so perhaps the real numbers should be a term of the
type of all complete linearly ordered fields. The problem is that the real
numbers are also a normed field (to the analysts), an archimedean local field
(to the number theorists), and so on. There is just no natural choice of type.

For this reason, rather than having "the type of all groups", we instead have
"the type of all group structures on X". This is implemented as a structure
that bundles together all of the algebraic data and axioms about that data.
-/

/-- `Group G` is the type of all group structures on `G`. -/
structure MyGroup₁ (G : Type*) where
  one : G
  inv (a : G) : G
  mul (a b : G) : G
  one_mul (a : G) : mul one a = a
  inv_mul_cancel (a : G) : mul (inv a) a = one
  mul_assoc (a b c : G) : mul (mul a b) c = mul a (mul b c)

/-
One problem with this setup is that the algebraic data and axioms all
carry the group structure as an explicit argument.
-/

#check MyGroup₁.one_mul

/-
This means that any usage of the group operations and axioms requires
constantly referring back to the group structure by name.
-/

theorem MyGroup₁.mul_left_cancel {G : Type*} (hG : MyGroup₁ G)
    (a b c : G) (h : hG.mul a b = hG.mul a c) : b = c := by
  rw [← hG.one_mul b, ← hG.inv_mul_cancel a,
    ← hG.one_mul c, ← hG.inv_mul_cancel a,
    hG.mul_assoc, hG.mul_assoc, h]

/-
But in practice, a given object will only ever have one group structure defined
on it. Ideally, Lean would be able to recall the group structure automatically.
Lean supports this through classes and instances. If a type in Lean defined by
the `structure` command has the property that in practice you will never want to
consider more than one term of that type, then you can mark the structure as a
typeclass by using the `class` command instead of `structure`. Definitions can
be marked as instances by using the `instance` command instead of `definition`.
-/

class MyGroup (G : Type*) extends One G, Inv G, Mul G where
  one_mul (a : G) : 1 * a = a
  inv_mul_cancel (a : G) : a⁻¹ * a = 1
  mul_assoc (a b c : G) : (a * b) * c = a * (b * c)

instance {α : Type*} : MyGroup (Equiv α α) where
  one := Equiv.refl α
  inv := Equiv.symm
  mul e1 e2 := e2.trans e1
  one_mul := Equiv.trans_refl
  inv_mul_cancel := Equiv.self_trans_symm
  mul_assoc e1 e2 e3 := (e3.trans_assoc e2 e1)

/-
There are many things to explain here. First, `One`, `Inv`, and `Mul` are
existing typeclasses for types with a "one", an inverse, and a multiplciation.
These are notation typeclasses, allowing you to write `1`, `a⁻¹`, and `a * b`.
The way this works is that when you write `a * b`, Lean first determines the
type `G` of `a` and `b`, and then looks for an instance of `Mul G`. For example,
when you write `2 * 3`, Lean looks for an instance of `Mul ℕ`. You can use the
`#synth` command to see the instance that Lean was able to find.
-/

#synth Mul ℕ

/-
The `extends` keyword means that `MyGroup` contains all of the fields of
`One`, `Inv`, and `Mul` in addition to the three group axioms. This is
why the definition of `MyGroup (Equiv α α)` required specifying six things.

Another thing to notice is that the fields like `MyGroup.one_mul` now take
the group structure as a typeclass argument rather than an explicit argument.
Typeclass arguments are written with square brackets. Like implicit arguments,
typeclass arguments are not passed in. But unlike implicit arguments, rather
than Lean inferring their value from the explicit arguments, Lean will instead
look for an instance of that type in the same way that Lean looks for `Mul α`.
-/

#check MyGroup.one_mul

/-
With this typeclass machinery in place, we can now prove basic properties
of groups without having to constantly refer back to the group structure.
-/

variable {G : Type*} [MyGroup G]

theorem MyGroup.mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← inv_mul_cancel a, ← one_mul c, ← inv_mul_cancel a,
    mul_assoc, mul_assoc, h]

theorem MyGroup.mul_one (a : G) : a * 1 = a := by
  sorry

theorem MyGroup.mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem MyGroup.inv_one : (1 : G)⁻¹ = 1 := by
  sorry

theorem MyGroup.mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

/-
Typeclasses also allow results in mathlib to be stated in maximal generality.
For the declarations above, the corresponding results in mathlib are often
stated for much more general algebraic structures.
-/

#check one_mul
#check inv_mul_cancel
#check mul_assoc
#check mul_left_cancel
#check mul_one
#check mul_inv_cancel
#check inv_one
#check mul_inv_rev

/-
This generality can result in some rather unusual algebraic structures.
-/

#check GroupWithZero
#check AddGroupWithOne
#check Distrib

/-
In practice, these exotic structures are rarely encountered in practice.
The algebraic structures are assembled into an algebraic hierarchy and
Lean can automatically infer these low-level typeclasses from more
standard typeclasses like `Group`, `Ring`, and `Field`.

This algebraic hierarchy is primarily built up with the `extends` keyword,
starting with notation typeclasses like `One`, `Inv`, and `Mul` and gradually
adding more axioms. Sometimes, additional arrows need to be provided manually.
-/

#check Group.toCancelMonoid

/-
One thing you will notice if start pulling apart the definition of
`Group` in mathlib is that it extends `NPow` and `ZPow` and has
axioms asserting compatibility with the group operations such as
`g ^ 0 = 1` and `g ^ (n + 1) = g ^ n * g`.
-/

#print Group

/-
These power operations are redundant in the sense that they could be defined
from the other group operations. However, this would run the risk of diamonds.
To explain this, let's look at `AddGroup` which extends `NSMul` and `ZSMul`
with compatibility axioms `0 • g = 0` and `(n + 1) • g = n • g + g`.
-/

#print AddGroup

/-
The integers `ℤ` are an `AddGroup`, so there is an action of `ℤ` on `ℤ`.
But `ℤ` is also a `Ring`, and every ring `R` has an action of `R` on `R`.
The first action arises from repeated addition and the second arises from
multiplication. These are not definitionally equal, so this would lead
to two different instances of `SMul ℤ ℤ`. This is known as a diamond.
The solution is to include the actions of `ℕ` and `ℤ` as data in `AddGroup`
and manually set this to be multiplication in the case of the integers.
-/

#synth AddCommGroup ℤ

/-
Diamonds are only possible for typeclasses that carry data. Fortunately,
many typeclasses are `Prop`-valued, taking in data-carrying typeclasses
as arguments and then imposing additional axioms or compatibility.
-/

#check IsDomain
#check IsTopologicalGroup
#check IsOrderedRing

/-
In addition to the algebraic hierarchy, there is also a topological
hierarchy and an order hierarchy. But rather than adding data-carrying
typeclasses (e.g., `CompleteLinearlyOrderedField`) for all possible
combinations between them, mathlib instead has compatibility predicates.
-/
