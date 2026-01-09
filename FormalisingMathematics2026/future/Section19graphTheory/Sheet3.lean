/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
-- trees and forests

/-

# Trees and forests

A *forest* is a graph with no cycles. A *tree* is a connected forest.

Here's how to do this in Lean. Let `G` be a graph with vertex set `V`.

-/

variable (V : Type) (G : SimpleGraph V)

-- Here's how to say "G is a forest"
example : Prop :=
  G.IsAcyclic

-- It's defined to mean "For all `v : V`, every walk from `v` to `v` is not a cycle. "
example : G.IsAcyclic ↔ ∀ (v : V) (p : G.Walk v v), ¬p.IsCycle := by rfl

-- Here's how to say "G is a tree"
example : Prop :=
  G.IsTree

example : G.IsTree ↔ G.Connected ∧ G.IsAcyclic :=
  G.isTree_iff

-- Here are some harder theorems from the library. Recall that a *path* is a walk
-- with no repeated vertices.
-- A graph is acyclic iff for all `v w : V`, there's at most one path from `v` to `w`.
example : G.IsAcyclic ↔ ∀ (v w : V) (p q : G.Path v w), p = q :=
  SimpleGraph.isAcyclic_iff_path_unique

-- A graph is a tree iff `V` is nonempty and for all `v w : V`,
-- there's exactly one path from `v` to `w`.
example : G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath :=
  SimpleGraph.isTree_iff_existsUnique_path

-- If you want a logic puzzle, rephrase this in terms of `G.path`
-- (i.e. use the theorem above and then unpack and repack the RHS)
example : G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Path v w, True := by sorry

-- Here's a result which isn't yet in mathlib: `G` is a tree iff it's a maximal acyclic graph
-- If you fill this one in, let me know and we can put it in mathlib!
example : G.IsTree ↔ Maximal SimpleGraph.IsAcyclic G := by
  sorry
