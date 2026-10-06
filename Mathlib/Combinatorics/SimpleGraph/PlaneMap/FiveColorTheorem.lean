/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalFiveColor
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalDelete
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalDegree

/-!
# The Five Colour Theorem for combinatorial plane maps

Every generated `PlaneMap` is five-colourable. The proof passes to the
algebraic spherical carrier, whose filling property is proved from the
existing PlaneMap theory. Spanning-subgraph closure permits vertex deletion
while retaining an isolated vertex label; strong induction is on the number
of edges. A positive low-degree vertex supplies strict edge-count decrease.
The low-degree theorem handles disconnected graphs and short faces, so no
face-length, triangulation, or separation hypothesis remains.
-/

@[expose] public section
namespace SimpleGraph.SphericalMap
variable {n : ℕ}

/-- Every finite rotation system satisfying the spherical filling property is
five-colourable, with no connectedness or face-length assumptions. -/
theorem five_color_theorem (M : SphericalMap n) : M.graph.Colorable 5 := by
  classical
  generalize hk : Fintype.card M.graph.edgeSet = k
  induction k using Nat.strong_induction_on generalizing M with
  | h k ih =>
    by_cases hd : Nonempty M.Dart
    · obtain ⟨d⟩ := hd
      obtain ⟨x, hxpos, hxdeg⟩ := M.exists_pos_degree_le_five d
      obtain ⟨N, hN, hlt⟩ := M.isolate_closed x hxpos
      have hcN : N.graph.Colorable 5 := ih _ (by omega) N rfl
      have hcH : (M.isolateGraph x).Colorable 5 := hN ▸ hcN
      obtain ⟨c⟩ := hcH
      apply five_color_extension x hxdeg
      exact ⟨Coloring.mk (fun z => c z.val) (fun {u v} huv =>
        c.valid ⟨huv, u.property, v.property⟩)⟩
    · exact ⟨Coloring.mk (fun _ => (0 : Fin 5)) (fun {u v} huv =>
        (hd ⟨⟨(u, v), huv⟩⟩).elim)⟩

end SimpleGraph.SphericalMap

namespace SimpleGraph.PlaneMap
variable {n : ℕ}

/-- The Five Colour Theorem for every generated combinatorial plane map. -/
theorem five_color_theorem (M : PlaneMap n) : M.graph.Colorable 5 :=
  (SphericalMap.ofPlaneMap M).five_color_theorem

/-- Function-valued formulation of the Five Colour Theorem. -/
theorem exists_five_colouring (M : PlaneMap n) :
    ∃ c : Fin n → Fin 5, ∀ u v, M.Adj u v → c u ≠ c v := by
  obtain ⟨c⟩ := five_color_theorem M
  exact ⟨c, fun _ _ h => c.valid h⟩

end SimpleGraph.PlaneMap
