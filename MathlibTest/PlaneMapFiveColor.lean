import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FiveColorExamples
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FiveColorTheorem

/-! Regression checks: the application theorems use only the standard axioms,
with no `sorryAx` or additional mathematical assumption disguised as an axiom. -/

/-- info: 'SimpleGraph.PlaneMap.heawood_hopposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.PlaneMap.heawood_hopposite

/-- info: 'SimpleGraph.PlaneMap.five_color_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.PlaneMap.five_color_extension

/-- info: 'SimpleGraph.PlaneMap.five_colorable_six_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.PlaneMap.five_colorable_six_vertices

/-- info: 'SimpleGraph.RotationSystem.fills_eraseRotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.RotationSystem.fills_eraseRotation

/-- info: 'SimpleGraph.SphericalMap.subgraph_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.subgraph_closed

/-- info: 'SimpleGraph.SphericalMap.isolate_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.isolate_closed

/-- info: 'SimpleGraph.SphericalMap.exists_pos_degree_le_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.exists_pos_degree_le_five

/-- info: 'SimpleGraph.SphericalMap.five_color_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.five_color_theorem

/-- info: 'SimpleGraph.PlaneMap.five_color_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.PlaneMap.five_color_theorem

/-- info: 'SimpleGraph.PlaneMap.exists_five_colouring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.PlaneMap.exists_five_colouring

open SimpleGraph

-- Symbolic families, including paths with bridge edges and short faces.
example (n : ℕ) : (PlaneMap.pathMap n).graph.Colorable 5 :=
  (PlaneMap.pathMap n).five_color_theorem

example (n : ℕ) : (PlaneMap.cycleMap n).graph.Colorable 5 :=
  (PlaneMap.cycleMap n).five_color_theorem

example : PlaneMap.tetrahedron.graph.Colorable 5 :=
  PlaneMap.tetrahedron.five_color_theorem

-- Isolating the centre of the three-vertex path removes all edges. The
-- deletion carrier therefore includes disconnected graphs with isolated labels.
example : ∃ N : SphericalMap 3, N.graph = ⊥ ∧ N.graph.Colorable 5 := by
  classical
  let M := SphericalMap.ofPlaneMap (PlaneMap.pathMap 2)
  have heq : M.isolateGraph 1 = ⊥ := by
    ext u v
    change ((PlaneMap.pathMap 2).graph.Adj u v ∧ u ≠ 1 ∧ v ≠ 1) ↔ False
    rw [PlaneMap.pathMap_graph]
    fin_cases u <;> fin_cases v <;> simp [pathGraph_adj]
  obtain ⟨N, hN⟩ := M.subgraph_closed (M.isolateGraph 1) (fun _ _ h => h.1)
  exact ⟨N, hN.trans heq, N.five_color_theorem⟩

-- The filling condition excludes the six-clique, rather than giving a
-- spurious five-colouring of every finite rotation system.
example (M : SphericalMap 6) : M.graph ≠ ⊤ := by
  intro hgraph
  have hb := M.five_color_theorem.card_le_of_pairwise_adj (fun i : Fin 6 => i)
    (by intro i j hij; simpa [hgraph] using hij)
  norm_num at hb
