import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalFiveColor
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalDelete
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Examples

-- This file deliberately does not import FiveColorTheorem or invoke it.
/-- info: Unknown constant `SimpleGraph.PlaneMap.five_color_theorem` -/
#guard_msgs in
#check_failure SimpleGraph.PlaneMap.five_color_theorem
/-- info: Unknown constant `SimpleGraph.SphericalMap.five_color_theorem` -/
#guard_msgs in
#check_failure SimpleGraph.SphericalMap.five_color_theorem

open SimpleGraph

namespace PlaneMapAudit

-- Distinct alternating neighbours of a six-clique would be joined by two
-- disjoint one-edge walks, contradicting the independently proved separation.
theorem no_spherical_six_clique (M : SphericalMap 6) : M.graph ≠ ⊤ := by
  classical
  intro hgraph
  have hdeg : M.graph.degree 0 = 5 := by
    have hs : M.graph.neighborSet 0 = {i : Fin 6 | 0 ≠ i} := by
      ext i
      change M.graph.Adj 0 i ↔ 0 ≠ i
      rw [hgraph]
      rfl
    rw [← M.graph.ncard_neighborSet, hs]
    have hset : {i : Fin 6 | 0 ≠ i} = ↑({1, 2, 3, 4, 5} : Finset (Fin 6)) := by
      ext i
      fin_cases i <;> decide
    rw [hset, Set.ncard_coe_finset]
    decide
  obtain ⟨e, he⟩ := M.degree_five_neighbour_rotation 0 hdeg
  let v : Fin 5 → Fin 6 := fun i => (e i).val
  have hadj (i : Fin 5) : M.Adj 0 (v i) := (e i).property
  have hinj : Function.Injective v := fun i j h => e.injective (Subtype.ext h)
  have hrot (i : Fin 5) : M.rotation.next ⟨(0, v i), hadj i⟩ =
      ⟨(0, v (i + 1)), hadj (i + 1)⟩ := he i
  apply M.heawood_hopposite id 0 v hadj hrot hinj
  · apply Adj.reachable
    change M.graph.Adj (v 0) (v 2)
    simpa [hgraph] using hinj.ne (by decide : (0 : Fin 5) ≠ 2)
  · apply Adj.reachable
    change M.graph.Adj (v 1) (v 3)
    simpa [hgraph] using hinj.ne (by decide : (1 : Fin 5) ≠ 3)

-- Deleting the centre of a five-vertex path leaves both edge 0--1 and
-- edge 3--4, and the isolated label 2. This exercises nontrivial components.
theorem delete_path_middle : ∃ N : SphericalMap 5,
    (∀ u v : Fin 5, N.Adj u v ↔
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
      (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 3)) ∧
    Fintype.card N.graph.edgeSet <
      Fintype.card (PlaneMap.pathMap 4).graph.edgeSet := by
  classical
  let M := SphericalMap.ofPlaneMap (PlaneMap.pathMap 4)
  have hadj : M.Adj 2 1 := by
    change (PlaneMap.pathMap 4).graph.Adj 2 1
    rw [PlaneMap.pathMap_graph]
    simp [pathGraph_adj]
  have hpos : 0 < M.graph.degree 2 :=
    (M.graph.degree_pos_iff_mem_support 2).mpr hadj.mem_support_left
  obtain ⟨N, hN, hlt⟩ := M.isolate_closed 2 hpos
  refine ⟨N, ?_, hlt⟩
  intro u v
  change N.graph.Adj u v ↔ _
  rw [hN]
  change ((PlaneMap.pathMap 4).graph.Adj u v ∧ u ≠ 2 ∧ v ≠ 2) ↔ _
  rw [PlaneMap.pathMap_graph]
  fin_cases u <;> fin_cases v <;> simp [pathGraph_adj]

end PlaneMapAudit

/-- info: 'PlaneMapAudit.no_spherical_six_clique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PlaneMapAudit.no_spherical_six_clique

/-- info: 'PlaneMapAudit.delete_path_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PlaneMapAudit.delete_path_middle
