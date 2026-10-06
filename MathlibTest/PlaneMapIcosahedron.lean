module

import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Icosahedron

/-! Kernel audits and the sharp twelve-vertex obstruction to degree-four deletion. -/

open SimpleGraph

/-- info: 'SimpleGraph.Icosahedron.sphericalMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icosahedron.sphericalMap

/-- info: 'SimpleGraph.Icosahedron.fills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icosahedron.fills

/-- info: 'SimpleGraph.Icosahedron.edge_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icosahedron.edge_count

/-- info: 'SimpleGraph.Icosahedron.face_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icosahedron.face_count

/-- info: 'SimpleGraph.Icosahedron.degree_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icosahedron.degree_five

/-- info: 'SimpleGraph.Icosahedron.face_length_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icosahedron.face_length_three

/-- info: 'SimpleGraph.Icosahedron.support_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icosahedron.support_count

example : Fintype.card (Fin 12) = 12 := Fintype.card_fin _

example : Icosahedron.sphericalMap.graph.edgeFinset.card = 30 := Icosahedron.sphericalMap_edges

example : Icosahedron.sphericalMap.rotation.faceCount = 20 := Icosahedron.face_count

example (v : Fin 12) : Icosahedron.sphericalMap.graph.degree v = 5 :=
  Icosahedron.sphericalMap_degree v

example (f : Icosahedron.sphericalMap.Face) :
    Icosahedron.sphericalMap.rotation.faceLength f = 3 := Icosahedron.sphericalMap_triangular f

example : Nat.card Icosahedron.sphericalMap.graph.support = 12 := Icosahedron.support_count

-- This fixture genuinely lies beyond the degree-four extension step.
example : ¬ ∃ v, 0 < Icosahedron.sphericalMap.graph.degree v ∧
    Icosahedron.sphericalMap.graph.degree v ≤ 4 := by
  rintro ⟨v, hv⟩
  rw [Icosahedron.sphericalMap_degree] at hv
  omega
