/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.DeleteVertex

/-!
# A first application of plane-map five-colour extension

Every generated plane map on six vertices is five-colourable. Deleting any
vertex leaves at most five vertices, which can be coloured injectively; the
proved Heawood/Kempe extension handles degree five. This is a deductive
application, not a finite graph census, and needs no face-length assumptions.
-/

@[expose] public section
namespace SimpleGraph.PlaneMap

/-- Every plane map on six vertices is five-colourable. -/
theorem five_colorable_six_vertices (M : PlaneMap 6) : M.graph.Colorable 5 := by
  classical
  have hdeg : M.graph.degree 0 ≤ 5 := by
    have h := M.graph.degree_lt_card_verts 0
    simp only [Fintype.card_fin] at h
    omega
  apply five_color_extension 0 hdeg
  have hcard : Fintype.card {z : Fin 6 // z ≠ 0} ≤ 5 := by
    have h := Fintype.card_subtype_lt (x := (0 : Fin 6)) (p := fun z => z ≠ 0)
      (fun hh => hh rfl)
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨c, hc⟩ := Kempe.five_colorable_of_card_le_five
    (M.graph.induce {z | z ≠ 0}) hcard
  exact ⟨Coloring.mk c (fun h => hc _ _ h)⟩

end SimpleGraph.PlaneMap
