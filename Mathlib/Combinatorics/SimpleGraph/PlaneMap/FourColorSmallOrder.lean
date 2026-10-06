/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FourColorExtension
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalSmallOrder
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalDelete

/-!
# Four colouring with a spherical elimination condition

The elimination condition concerns every edge-containing spanning subgraph.
Spherical separation supplies the degree-four extension, and edge-count
induction supplies termination. The twelve-vertex threshold implies the
condition for spherical maps of order at most eleven.
-/

@[expose] public section
namespace SimpleGraph

/-- Every edge-containing spanning subgraph has a positive-degree vertex of
 degree at most four. This is an elimination condition independent of colouring. -/
def HasFourElimination {n : ℕ} (G : SimpleGraph (Fin n)) : Prop := by
  classical
  exact ∀ H : SimpleGraph (Fin n), H ≤ G → ∀ _d : H.Dart,
    ∃ x : Fin n, 0 < H.degree x ∧ H.degree x ≤ 4

namespace SphericalMap
variable {n : ℕ}

/-- The spherical extension rule turns the spanning-subgraph elimination
condition into four-colourability. -/
theorem four_color_of_elimination (M : SphericalMap n)
    (helim : M.graph.HasFourElimination) : M.graph.Colorable 4 := by
  classical
  generalize hk : Fintype.card M.graph.edgeSet = k
  induction k using Nat.strong_induction_on generalizing M with
  | h k ih =>
    by_cases hd : Nonempty M.Dart
    · obtain ⟨d⟩ := hd
      obtain ⟨x, hxpos, hxdeg⟩ := helim M.graph le_rfl d
      obtain ⟨N, hN, hlt⟩ := M.isolate_closed x hxpos
      have hsub : N.graph ≤ M.graph := by
        rw [hN]
        exact fun _ _ h => h.1
      have helimN : N.graph.HasFourElimination :=
        fun H hH d => helim H (hH.trans hsub) d
      have hcN : N.graph.Colorable 4 := ih _ (by omega) N helimN rfl
      have hcH : (M.isolateGraph x).Colorable 4 := hN ▸ hcN
      obtain ⟨c⟩ := hcH
      apply four_color_extension x hxdeg
      exact ⟨Coloring.mk (fun z => c z.val) (fun {u v} huv =>
        c.valid ⟨huv, u.property, v.property⟩)⟩
    · exact ⟨Coloring.mk (fun _ => (0 : Fin 4)) (fun {u v} huv =>
        (hd ⟨⟨(u, v), huv⟩⟩).elim)⟩

/-- Every spherical map on at most eleven vertices has the elimination
condition, including all its edge-containing spanning subgraphs. -/
theorem hasFourElimination_of_order_le_eleven (M : SphericalMap n) (hn : n ≤ 11) :
    M.graph.HasFourElimination := by
  classical
  intro H hH d
  obtain ⟨N, hN⟩ := M.subgraph_closed H hH
  subst H
  exact N.exists_pos_degree_le_four_of_order_le_eleven hn d

/-- Every spherical map on at most eleven vertices is four-colourable,
without connectedness or face-length assumptions. -/
theorem four_color_of_order_le_eleven (M : SphericalMap n) (hn : n ≤ 11) :
    M.graph.Colorable 4 :=
  M.four_color_of_elimination (M.hasFourElimination_of_order_le_eleven hn)

end SphericalMap

namespace PlaneMap
variable {n : ℕ}

/-- Spherical elimination gives four-colourability for generated plane maps. -/
theorem four_color_of_elimination (M : PlaneMap n)
    (h : M.graph.HasFourElimination) : M.graph.Colorable 4 :=
  (SphericalMap.ofPlaneMap M).four_color_of_elimination h

/-- Generated plane maps on at most eleven vertices are four-colourable. -/
theorem four_color_of_order_le_eleven (M : PlaneMap n) (hn : n ≤ 11) :
    M.graph.Colorable 4 :=
  (SphericalMap.ofPlaneMap M).four_color_of_order_le_eleven hn

end PlaneMap
end SimpleGraph
