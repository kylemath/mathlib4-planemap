import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FourEliminationOrder
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Examples

/-- info: 'SimpleGraph.SphericalMap.four_color_of_elimination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.four_color_of_elimination
/-- info: 'SimpleGraph.SphericalMap.hasFourElimination_of_order_le_eleven' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.hasFourElimination_of_order_le_eleven
/-- info: 'SimpleGraph.SphericalMap.four_color_of_order_le_eleven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.four_color_of_order_le_eleven
/-- info: 'SimpleGraph.PlaneMap.four_color_of_order_le_eleven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.PlaneMap.four_color_of_order_le_eleven

open SimpleGraph
example : PlaneMap.tetrahedron.graph.Colorable 4 :=
  PlaneMap.tetrahedron.four_color_of_order_le_eleven (by decide)

example (n : ℕ) (hn : n + 1 ≤ 11) : (PlaneMap.pathMap n).graph.Colorable 4 :=
  (PlaneMap.pathMap n).four_color_of_order_le_eleven hn

-- The deleted map still has edges on both sides of the removed centre.
example : ∃ N : SphericalMap 5,
    N.graph = (SphericalMap.ofPlaneMap (PlaneMap.pathMap 4)).isolateGraph 2 ∧
    N.graph.Adj 0 1 ∧ N.graph.Adj 3 4 ∧ N.graph.Colorable 4 := by
  classical
  let M := SphericalMap.ofPlaneMap (PlaneMap.pathMap 4)
  obtain ⟨N, hN⟩ := M.subgraph_closed (M.isolateGraph 2) (fun _ _ h => h.1)
  refine ⟨N, hN, ?_, ?_, N.four_color_of_order_le_eleven (by decide)⟩
  · rw [hN]
    change (PlaneMap.pathMap 4).graph.Adj 0 1 ∧ (0 : Fin 5) ≠ 2 ∧ (1 : Fin 5) ≠ 2
    rw [PlaneMap.pathMap_graph]
    simp [pathGraph_adj]
  · rw [hN]
    change (PlaneMap.pathMap 4).graph.Adj 3 4 ∧ (3 : Fin 5) ≠ 2 ∧ (4 : Fin 5) ≠ 2
    rw [PlaneMap.pathMap_graph]
    simp [pathGraph_adj]

-- The same deletion genuinely disconnects the two surviving edges.
example : ¬ ((SphericalMap.ofPlaneMap (PlaneMap.pathMap 4)).isolateGraph 2).Reachable 0 4 := by
  classical
  let H := (SphericalMap.ofPlaneMap (PlaneMap.pathMap 4)).isolateGraph 2
  have hstep {u v : Fin 5} (h : H.Adj u v) (hu : u.val ≤ 1) : v.val ≤ 1 := by
    change (PlaneMap.pathMap 4).graph.Adj u v ∧ u ≠ 2 ∧ v ≠ 2 at h
    rw [PlaneMap.pathMap_graph] at h
    fin_cases u <;> fin_cases v <;> simp_all [pathGraph_adj]
  have hwalk {u v : Fin 5} (p : H.Walk u v) : u.val ≤ 1 → v.val ≤ 1 := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hu => ih (hstep h hu)
  rintro ⟨p⟩
  have hf := hwalk p (by decide)
  norm_num at hf

/-- info: 'SimpleGraph.SphericalMap.four_color_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.four_color_extension

/-- info: 'SimpleGraph.SphericalMap.edge_card_bound_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.edge_card_bound_two

/-- info: 'SimpleGraph.SphericalMap.FourEliminationOrder.length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.FourEliminationOrder.length

/-- info: 'SimpleGraph.SphericalMap.FourEliminationOrder.length_le_edges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.FourEliminationOrder.length_le_edges

/-- info: 'SimpleGraph.SphericalMap.FourEliminationOrder.colorable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.FourEliminationOrder.colorable

/-- info: 'SimpleGraph.SphericalMap.exists_fourEliminationOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.exists_fourEliminationOrder

/-- info: 'SimpleGraph.SphericalMap.exists_fourEliminationOrder_of_order_le_eleven' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.exists_fourEliminationOrder_of_order_le_eleven

open SimpleGraph
example (M : SphericalMap 11) :
    ∃ order : M.FourEliminationOrder, order.length ≤ Fintype.card M.graph.edgeSet ∧
      M.graph.Colorable 4 := by
  obtain ⟨order⟩ := M.exists_fourEliminationOrder_of_order_le_eleven (by decide)
  exact ⟨order, order.length_le_edges, order.colorable⟩

example : (SphericalMap.FourEliminationOrder.done
    (SphericalMap.ofPlaneMap PlaneMap.vertex)
    (by intro u v h; exact h.ne (Subsingleton.elim _ _))).length = 0 := rfl
