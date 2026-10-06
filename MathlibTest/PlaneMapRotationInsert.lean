module
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationInsert

open SimpleGraph SimpleGraph.PlaneMapConstruction

/-- info: 'SimpleGraph.PlaneMapConstruction.splitFaceFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms splitFaceFunction
/-- info: 'SimpleGraph.PlaneMapConstruction.split_face_value_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_face_value_next
/-- info: 'SimpleGraph.PlaneMapConstruction.split_face_function_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_face_function_old
/-- info: 'SimpleGraph.PlaneMapConstruction.split_face_function_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_face_function_out
/-- info: 'SimpleGraph.PlaneMapConstruction.split_face_function_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_face_function_back
/-- info: 'SimpleGraph.PlaneMapConstruction.after_corners_same_face_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms after_corners_same_face_iff

namespace BridgeRegression

def graph : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun x y => x.val / 2 = y.val / 2
instance : DecidableRel graph.Adj := fun x y => inferInstanceAs
  (Decidable (x ≠ y ∧ (x.val / 2 = y.val / 2 ∨ y.val / 2 = x.val / 2)))

def rotation : RotationSystem graph where
  next := Equiv.refl _
  next_fst _ := rfl
  cyclic d e h := by
    refine ⟨0, ?_⟩
    change d = e
    have uniq : ∀ d e : graph.Dart, d.fst = e.fst → d = e := by decide
    exact uniq d e h

def a : graph.Dart := ⟨(0, 1), by decide⟩
def b : graph.Dart := ⟨(2, 3), by decide⟩
theorem different : a.fst ≠ b.fst := by decide
theorem missing : ¬graph.Adj a.fst b.fst := by decide
noncomputable def joined := split rotation a b different missing

example : joined.FaceRelation (splitOld a.fst b.fst different a)
    (splitOld a.fst b.fst different b) := by
  have h₁ := RotationSystem.FaceRelation.step (R := joined) (splitOld a.fst b.fst different a)
  have h₂ := RotationSystem.FaceRelation.step (R := joined) (splitOld a.fst b.fst different a.symm)
  have h₃ := RotationSystem.FaceRelation.step (R := joined) (splitOut a.fst b.fst different)
  have e₁ : joined.faceNext (splitOld a.fst b.fst different a) =
      splitOld a.fst b.fst different a.symm := by
    rw [joined, split_face_old]
    simp only [show rotation.faceNext a = a.symm from rfl,
      show a.symm ≠ a from by decide, show a.symm ≠ b from by decide,
      ↓reduceIte]
  have e₂ : joined.faceNext (splitOld a.fst b.fst different a.symm) =
      splitOut a.fst b.fst different := by
    rw [joined, split_face_old]
    simp only [show rotation.faceNext a.symm = a from rfl, ↓reduceIte]
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [joined, split_face_out] at h₃
  exact h₁.trans (h₂.trans h₃)

example (f : rotation.Face → ℕ) (hf : f (rotation.faceOf a) = f (rotation.faceOf b)) :
    splitFaceFunction rotation a b different missing f hf
      (joined.faceOf (splitOld a.fst b.fst different a)) = f (rotation.faceOf a) :=
  split_face_function_old rotation a b different missing f hf a

end BridgeRegression
