module
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalCompletion
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Icosahedron

open SimpleGraph

/-- info: 'SimpleGraph.SphericalMap.natCard_edgeSet_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.natCard_edgeSet_split
/-- info: 'SimpleGraph.SphericalMap.exists_triangulated_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.exists_triangulated_completion
/--
info: 'SimpleGraph.SphericalMap.exists_triangulated_completion_min_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.exists_triangulated_completion_min_five

namespace CompletionRegression

-- Completion lands in the class used by the Gate-D candidate.
example {n : ℕ} (hn : 0 < n) (M : SphericalMap n) (hdeg : ∀ x, 5 ≤ M.graph.degree x) :
    ∃ T : SphericalMap n, M.graph ≤ T.graph ∧ T.graph.Connected ∧ T.Triangulated ∧
      ∀ x, 5 ≤ T.graph.degree x :=
  SphericalMap.exists_triangulated_completion_min_five hn M hdeg

-- The icosahedron satisfies the completion hypotheses on a positive carrier.
example : ∃ T : SphericalMap 12, (Icosahedron.sphericalMap).graph ≤ T.graph ∧
    T.graph.Connected ∧ T.Triangulated := by
  apply SphericalMap.exists_triangulated_completion (by norm_num)
  intro x
  have h : (Icosahedron.sphericalMap).graph.degree x = 5 := by
    convert Icosahedron.degree_five x
    rfl
  omega

end CompletionRegression
