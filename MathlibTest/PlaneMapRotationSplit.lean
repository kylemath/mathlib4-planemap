module
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationSplit

open SimpleGraph SimpleGraph.PlaneMapConstruction

/-- info: 'SimpleGraph.RotationSystem.splitEdgeEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.splitEdgeEquiv
/-- info: 'SimpleGraph.RotationSystem.split_old_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.split_old_edge
/-- info: 'SimpleGraph.RotationSystem.split_edge_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.split_edge_dichotomy
/-- info: 'SimpleGraph.RotationSystem.incident_sum_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.incident_sum_split
/-- info: 'SimpleGraph.RotationSystem.even_restrict_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.even_restrict_split

namespace InsertionCoefficientRegression

def graph : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun x y => x.val / 2 = y.val / 2
instance : DecidableRel graph.Adj := fun x y => inferInstanceAs
  (Decidable (x ≠ y ∧ (x.val / 2 = y.val / 2 ∨ y.val / 2 = x.val / 2)))
def a : graph.Dart := ⟨(0, 1), by decide⟩
def b : graph.Dart := ⟨(2, 3), by decide⟩
theorem different : a.fst ≠ b.fst := by decide
theorem missing : ¬graph.Adj a.fst b.fst := by decide

-- A coefficient supported on the new bridge has nonzero incidence at its endpoints.
noncomputable def onlyNew : (splitGraph graph a.fst b.fst different).edgeSet → ZMod 2 :=
  fun e => if e = RotationSystem.splitNewEdge graph a b different missing then 1 else 0

example : RotationSystem.restrictSplit graph a b different missing onlyNew = 0 := by
  classical
  funext e
  simp [RotationSystem.restrictSplit, onlyNew, RotationSystem.splitMapEdge_ne_new]

example : edgeIncidence (splitGraph graph a.fst b.fst different) onlyNew a.fst = 1 := by
  classical
  rw [RotationSystem.incident_sum_split graph a b different missing]
  simp [RotationSystem.restrictSplit, onlyNew, RotationSystem.splitMapEdge_ne_new,
    edgeIncidence]

example : ¬RotationSystem.FaceEven (G := splitGraph graph a.fst b.fst different) onlyNew := by
  intro h
  have hv := h a.fst
  rw [RotationSystem.incident_sum_split graph a b different missing] at hv
  simp [RotationSystem.restrictSplit, onlyNew, RotationSystem.splitMapEdge_ne_new,
    edgeIncidence] at hv

example : RotationSystem.FaceEven (G := graph)
    (RotationSystem.restrictSplit graph a b different missing 0) := by
  apply RotationSystem.even_restrict_split
  · intro v
    simp [edgeIncidence]
  · rfl

end InsertionCoefficientRegression
