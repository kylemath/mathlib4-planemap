module
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FaceChord
open SimpleGraph
/-- info: 'SimpleGraph.RotationSystem.potential_eq_of_two_consecutive_jumps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.potential_eq_of_two_consecutive_jumps
/-- info: 'SimpleGraph.RotationSystem.face_potential_eq_of_two_consecutive_jumps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.face_potential_eq_of_two_consecutive_jumps
/-- info: 'SimpleGraph.SphericalMap.not_adj_of_triangle_face_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.not_adj_of_triangle_face_corner
/-- info: 'SimpleGraph.SphericalMap.exists_nonadjacent_face_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.exists_nonadjacent_face_vertices
/-- info: 'SimpleGraph.SphericalMap.exists_face_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.exists_face_chord

-- Completion uses minimum positive degree five; the theorem requires only two.
example {n : ℕ} (M : SphericalMap n)
    (hdeg : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x)
    (d : M.Dart) (hlen : 4 ≤ M.rotation.faceLength (M.faceOf d)) :
    ∃ a b : M.Dart, M.faceOf a.symm = M.faceOf d ∧
      M.faceOf b.symm = M.faceOf d ∧ a.fst ≠ b.fst ∧ ¬ M.Adj a.fst b.fst := by
  exact M.exists_face_chord (fun x hx => by have hh := hdeg x hx; omega) d hlen
