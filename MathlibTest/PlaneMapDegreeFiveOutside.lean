module

import Mathlib.Combinatorics.SimpleGraph.PlaneMap.DegreeFiveOutside
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Icosahedron

open SimpleGraph

/-- info: 'SimpleGraph.SphericalMap.twice_edges_add_twelve_le_six_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.twice_edges_add_twelve_le_six_support

/-- info: 'SimpleGraph.SphericalMap.six_le_degreeFiveOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.six_le_degreeFiveOutside

/-- info: 'SimpleGraph.SphericalMap.exists_degree_five_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.exists_degree_five_outside

example (a : Fin 12) :
    6 ≤ (Icosahedron.sphericalMap.degreeFiveOutside a).card := by
  apply SphericalMap.six_le_degreeFiveOutside
  · change a ∈ Icosahedron.graph.support
    rw [Icosahedron.support_all]
    trivial
  · intro x _
    rw [Icosahedron.sphericalMap_degree]

example (a : Fin 12) : ∃ x, x ≠ a ∧ ¬ Icosahedron.sphericalMap.graph.Adj a x ∧
    Icosahedron.sphericalMap.graph.degree x = 5 := by
  apply SphericalMap.exists_degree_five_outside
  · change a ∈ Icosahedron.graph.support
    rw [Icosahedron.support_all]
    trivial
  · intro x _
    rw [Icosahedron.sphericalMap_degree]
