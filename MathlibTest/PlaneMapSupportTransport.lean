module

import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SupportTransport
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Examples
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FourColorSmallOrder

open SimpleGraph
open SimpleGraph.SphericalMap

/-- info: 'SimpleGraph.SphericalMap.support_fills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.support_fills
/-- info: 'SimpleGraph.SphericalMap.exists_supportTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.exists_supportTransport
/-- info: 'SimpleGraph.SphericalMap.extendSupportColoring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.extendSupportColoring
/-- info: 'SimpleGraph.SphericalMap.support_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.support_degree
/-- info: 'SimpleGraph.SphericalMap.isolate_support_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.isolate_support_card_lt

-- Removing the centre leaves two edges, two connected components and one isolated label.
example : ∃ N : SphericalMap 5,
    N.graph = (SphericalMap.ofPlaneMap (PlaneMap.pathMap 4)).isolateGraph 2 ∧
    Nat.card N.graph.support = 4 ∧
    ∃ K : SphericalMap 4, K.graph.support = Set.univ ∧ K.graph.Colorable 4 := by
  classical
  let M := SphericalMap.ofPlaneMap (PlaneMap.pathMap 4)
  obtain ⟨N, hN⟩ := M.subgraph_closed (M.isolateGraph 2) (fun _ _ h => h.1)
  have hs : N.graph.support = {0, 1, 3, 4} := by
    rw [hN]
    ext x
    simp only [SimpleGraph.mem_support]
    change (∃ y, (PlaneMap.pathMap 4).graph.Adj x y ∧ x ≠ 2 ∧ y ≠ 2) ↔ _
    rw [PlaneMap.pathMap_graph]
    constructor
    · rintro ⟨y, hxy, hxn, hyn⟩
      have hx2 : x.val ≠ 2 := by
        intro hx
        exact hxn (Fin.ext hx)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
      change x.val = 0 ∨ x.val = 1 ∨ x.val = 3 ∨ x.val = 4
      have hlt := x.isLt
      omega
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx | hx <;> subst x
      · exact ⟨1, by norm_num [pathGraph_adj], by decide, by decide⟩
      · exact ⟨0, by norm_num [pathGraph_adj], by decide, by decide⟩
      · exact ⟨4, by norm_num [pathGraph_adj], by decide, by decide⟩
      · exact ⟨3, by norm_num [pathGraph_adj], by decide, by decide⟩
  have hcard : Nat.card N.graph.support = 4 := by
    rw [hs]
    norm_num
  let i : N.graph.support ≃ Fin 4 := Fintype.equivFinOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  let K := N.supportTransport i
  exact ⟨N, hN, hcard, K, N.supportTransport_support i,
    K.four_color_of_order_le_eleven (by decide)⟩

-- An entirely isolated map contracts to the empty carrier, preserving its empty face.
example : Nat.card (SphericalMap.ofPlaneMap PlaneMap.vertex).graph.support = 0 := by
  change Nat.card (⊥ : SimpleGraph (Fin 1)).support = 0
  simp

example {n s : ℕ} (M : SphericalMap n) (i : M.graph.support ≃ Fin s)
    (hmin : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x) :
    ∀ x, 5 ≤ (M.supportTransport i).graph.degree x := M.support_min_degree i 5 hmin

-- Colour transport requires no connectivity hypothesis and supplies isolated labels explicitly.
noncomputable example {n s : ℕ} (M : SphericalMap n) (i : M.graph.support ≃ Fin s)
    (c : (M.supportTransport i).graph.Coloring (Fin 4)) : M.graph.Coloring (Fin 4) :=
  M.extendSupportColoring i 0 c
