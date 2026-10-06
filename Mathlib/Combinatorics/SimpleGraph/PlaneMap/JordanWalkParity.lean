/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.JordanCycle

/-!
# Mod-two edge counts of walks

The boundary of a walk consists of its endpoints. Consequently every closed
walk is a mod-two sum of face boundaries in a generated plane map. Repeated
edges cancel; no simplicity or connected-cycle-cut assumption is needed.
-/

@[expose] public section

namespace SimpleGraph.PlaneMap

open scoped BigOperators

variable {n : ℕ} {M : PlaneMap n}

/-- Edge multiplicities of a walk, reduced modulo two. -/
noncomputable def walkEdgeCoeff {u v : Fin n} (p : M.graph.Walk u v)
    (e : M.graph.edgeSet) : ZMod 2 := by
  classical
  exact (p.edges.count e.val : ZMod 2)

@[simp] theorem walkEdgeCoeff_nil (u : Fin n) (e : M.graph.edgeSet) :
    walkEdgeCoeff (M := M) (.nil (u := u)) e = 0 := by
  simp [walkEdgeCoeff]

@[simp] theorem walkEdgeCoeff_cons {u v w : Fin n} (h : M.Adj u v)
    (p : M.graph.Walk v w) (e : M.graph.edgeSet) :
    walkEdgeCoeff (.cons h p) e =
      (if RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart) = e then 1 else 0) +
        walkEdgeCoeff p e := by
  classical
  change ((s(u, v) :: p.edges).count e.val : ZMod 2) = _
  by_cases he : RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart) = e
  · have hv : s(u, v) = e.val := congrArg Subtype.val he
    simp [hv, he, walkEdgeCoeff, add_comm]
  · have hv : s(u, v) ≠ e.val := fun hh => he (Subtype.ext hh)
    simp [hv, he, walkEdgeCoeff]

private theorem double_eq_zero (a : ZMod 2) : a + a = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

/-- The incidence boundary of a walk is its pair of endpoints, modulo two. -/
theorem incidentSum_walkEdgeCoeff {u v : Fin n} (p : M.graph.Walk u v)
    (x : Fin n) :
    incidentSum M (walkEdgeCoeff p) x =
      (if x = u then 1 else 0) + (if x = v then 1 else 0) := by
  classical
  induction p with
  | nil => simp [incidentSum, double_eq_zero]
  | @cons u v w h p ih =>
    have hsingle :
        (∑ e : M.graph.edgeSet, if x ∈ e.val then
          (if RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart) = e then
            (1 : ZMod 2) else 0) else 0) =
          (if x = u then 1 else 0) + (if x = v then 1 else 0) := by
      rw [Finset.sum_eq_single (RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart))]
      · simp only [mem_edgeOfDart_iff, ite_true]
        by_cases hu : x = u <;> by_cases hv : x = v <;> simp_all [h.ne, eq_comm]
      · intro e _ he
        simp [Ne.symm he]
      · simp
    have hsplit : incidentSum M (walkEdgeCoeff (.cons h p)) x =
        (∑ e : M.graph.edgeSet, if x ∈ e.val then
          (if RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart) = e then
            (1 : ZMod 2) else 0) else 0) + incidentSum M (walkEdgeCoeff p) x := by
      unfold incidentSum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rw [walkEdgeCoeff_cons]
      split_ifs <;> simp
    rw [hsplit, hsingle, ih]
    have hh := double_eq_zero (if x = v then 1 else 0)
    simpa only [add_assoc, add_zero] using
      congrArg (fun z : ZMod 2 =>
        (if x = u then 1 else 0) + z + (if x = w then 1 else 0)) hh

/-- Every closed walk determines an even edge combination. -/
theorem walkEdgeCoeff_even {u : Fin n} (p : M.graph.Walk u u) :
    IsEven M (walkEdgeCoeff p) := by
  intro x
  rw [incidentSum_walkEdgeCoeff, double_eq_zero]

/-- A closed walk is a mod-two sum of face boundaries. -/
theorem walkEdgeCoeff_is_face_sum {u : Fin n} (p : M.graph.Walk u u) :
    ∃ c : M.Face → ZMod 2, ∀ e, walkEdgeCoeff p e = faceSum M c e :=
  even_is_face_sum M _ (walkEdgeCoeff_even p)

@[simp] theorem walkEdgeCoeff_append {u v w : Fin n}
    (p : M.graph.Walk u v) (q : M.graph.Walk v w) (e : M.graph.edgeSet) :
    walkEdgeCoeff (p.append q) e = walkEdgeCoeff p e + walkEdgeCoeff q e := by
  classical
  simp [walkEdgeCoeff, Walk.edges_append, List.count_append]

/-- An edge incident to an unvisited vertex has zero walk coefficient. -/
theorem walkEdgeCoeff_zero_of_not_mem_support {u v : Fin n}
    (p : M.graph.Walk u v) (x : Fin n) (hx : x ∉ p.support)
    (e : M.graph.edgeSet) (he : x ∈ e.val) : walkEdgeCoeff p e = 0 := by
  classical
  unfold walkEdgeCoeff
  suffices e.val ∉ p.edges by simp [List.count_eq_zero.mpr this]
  intro hm
  exact hx (Walk.mem_support_of_mem_edges hm he)

end SimpleGraph.PlaneMap
