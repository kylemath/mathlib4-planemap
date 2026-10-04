/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Jordan

/-!
# Compatibility lemmas for one-leaf extension

The canonical restriction and face-boundary transport proofs are in `Jordan`.
This module preserves the additional grow API without redeclaring those
lemmas. In particular, `even_boundary_grow_before` specializes the general
corner theorem to a nonempty corner.
-/

@[expose] public section

namespace SimpleGraph.PlaneMap

open scoped BigOperators
open PlaneMapConstruction

variable {n : ℕ}

/-- The two darts of an old edge map to the two darts of `growMapEdge`. -/
theorem grow_old_edge_fiber (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) (d : M.Dart)
    (d' : (growGraph M.graph u).Dart)
    (h : RotationSystem.edgeOfDart d' =
      growMapEdge M u c (RotationSystem.edgeOfDart d)) :
    d' = growOld (H := M.graph) u d ∨
      d' = growOld (H := M.graph) u d.symm := by
  have hd := (RotationSystem.edge_of_dart_eq_iff d'
      (growOld (H := M.graph) u d)).1
    (h.trans (grow_old_edge_eq_map M u c d).symm)
  simpa [grow_old_symm] using hd

/-- Compatibility name for face-boundary transport at a nonempty corner. -/
alias boundary_grow_old := boundary_grow_map_before

/-- Specialization of the general one-leaf extension theorem. -/
theorem even_boundary_grow_before (M : PlaneMap n) (u : Fin n)
    (a : M.Dart) (ha : a.fst = u)
    (hM : ∀ φ : M.graph.edgeSet → ZMod 2, IsEven M φ →
      ∃ c : M.Face → ZMod 2, ∀ e, φ e = ∑ f, c f * M.boundary f e)
    (φ : (M.grow u (.before a ha)).graph.edgeSet → ZMod 2)
    (hφ : IsEven (M.grow u (.before a ha)) φ) :
    ∃ c : (M.grow u (.before a ha)).Face → ZMod 2,
      ∀ e, φ e = ∑ f, c f *
        (M.grow u (.before a ha)).boundary f e := by
  exact even_boundary_grow M u (.before a ha) hM φ hφ

end SimpleGraph.PlaneMap
