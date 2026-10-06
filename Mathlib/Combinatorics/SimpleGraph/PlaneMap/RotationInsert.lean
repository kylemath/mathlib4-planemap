/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Construction

/-!
# Face observables under edge insertion

The existing `split` operation inserts immediately before its selected darts.
For insertion immediately after `a` and `b`, its selected darts are `R.next a`
and `R.next b`. This file records that corner convention and transports any old
face observable whose values agree on the two selected faces. No filling or
connectedness premise is used.
-/

@[expose] public section
namespace SimpleGraph.PlaneMapConstruction
universe u w
variable {V : Type u} {G : SimpleGraph V}
variable (R : RotationSystem G) (a b : G.Dart)
variable (hab : a.fst ≠ b.fst) (hmiss : ¬ G.Adj a.fst b.fst)

/-- Values on old faces, extended over the two newly inserted darts. -/
noncomputable def splitFaceValue {W : Type w} (f : R.Face → W)
    (d : (splitGraph G a.fst b.fst hab).Dart) : W :=
  match (splitDartEquiv a.fst b.fst hab hmiss).symm d with
  | .inl e => f (R.faceOf e)
  | .inr false => f (R.faceOf b)
  | .inr true => f (R.faceOf a)

@[simp] theorem split_face_value_old {W : Type w} (f : R.Face → W) (d : G.Dart) :
    splitFaceValue R a b hab hmiss f (splitOld a.fst b.fst hab d) = f (R.faceOf d) := by
  change splitFaceValue R a b hab hmiss f
    (splitDartEquiv a.fst b.fst hab hmiss (.inl d)) = _
  simp only [splitFaceValue, Equiv.symm_apply_apply]

@[simp] theorem split_face_value_out {W : Type w} (f : R.Face → W) :
    splitFaceValue R a b hab hmiss f (splitOut a.fst b.fst hab) = f (R.faceOf b) := by
  change splitFaceValue R a b hab hmiss f
    (splitDartEquiv a.fst b.fst hab hmiss (.inr false)) = _
  simp only [splitFaceValue, Equiv.symm_apply_apply]

@[simp] theorem split_face_value_back {W : Type w} (f : R.Face → W) :
    splitFaceValue R a b hab hmiss f (splitBack a.fst b.fst hab) = f (R.faceOf a) := by
  change splitFaceValue R a b hab hmiss f
    (splitDartEquiv a.fst b.fst hab hmiss (.inr true)) = _
  simp only [splitFaceValue, Equiv.symm_apply_apply]

/-- Agreement at the selected faces makes the extended observable face-invariant. -/
theorem split_face_value_next {W : Type w} (f : R.Face → W)
    (hf : f (R.faceOf a) = f (R.faceOf b))
    (d : (splitGraph G a.fst b.fst hab).Dart) :
    splitFaceValue R a b hab hmiss f ((split R a b hab hmiss).faceNext d) =
      splitFaceValue R a b hab hmiss f d := by
  classical
  obtain ⟨x, rfl⟩ := (splitDartEquiv a.fst b.fst hab hmiss).surjective d
  cases x with
  | inl d =>
    change splitFaceValue R a b hab hmiss f
      ((split R a b hab hmiss).faceNext (splitOld a.fst b.fst hab d)) =
        splitFaceValue R a b hab hmiss f (splitOld a.fst b.fst hab d)
    rw [split_face_old]
    split_ifs with ha hb
    · rw [split_face_value_out, split_face_value_old, ← hf, ← ha, R.face_of_face_next]
    · rw [split_face_value_back, split_face_value_old, hf, ← hb, R.face_of_face_next]
    · rw [split_face_value_old, split_face_value_old, R.face_of_face_next]
  | inr t =>
    cases t
    · change splitFaceValue R a b hab hmiss f
        ((split R a b hab hmiss).faceNext (splitOut a.fst b.fst hab)) =
          splitFaceValue R a b hab hmiss f (splitOut a.fst b.fst hab)
      rw [split_face_out, split_face_value_old, split_face_value_out]
    · change splitFaceValue R a b hab hmiss f
        ((split R a b hab hmiss).faceNext (splitBack a.fst b.fst hab)) =
          splitFaceValue R a b hab hmiss f (splitBack a.fst b.fst hab)
      rw [split_face_back, split_face_value_old, split_face_value_back]

/-- The extended observable is constant throughout each new face orbit. -/
theorem split_face_value_relation {W : Type w} (f : R.Face → W)
    (hf : f (R.faceOf a) = f (R.faceOf b))
    {d e : (splitGraph G a.fst b.fst hab).Dart}
    (h : (split R a b hab hmiss).FaceRelation d e) :
    splitFaceValue R a b hab hmiss f d = splitFaceValue R a b hab hmiss f e := by
  induction h with
  | refl => rfl
  | step d => exact (split_face_value_next R a b hab hmiss f hf d).symm
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

/-- Descend the transported observable to the new face quotient. -/
noncomputable def splitFaceFunction {W : Type w} (f : R.Face → W)
    (hf : f (R.faceOf a) = f (R.faceOf b)) : (split R a b hab hmiss).Face → W :=
  fun F => match F with
  | .inl q => Quotient.lift (splitFaceValue R a b hab hmiss f)
      (fun _ _ h => split_face_value_relation R a b hab hmiss f hf h) q
  | .inr h => (h.property.false (splitOut a.fst b.fst hab)).elim

@[simp] theorem split_face_function_apply {W : Type w} (f : R.Face → W)
    (hf : f (R.faceOf a) = f (R.faceOf b))
    (d : (splitGraph G a.fst b.fst hab).Dart) :
    splitFaceFunction R a b hab hmiss f hf ((split R a b hab hmiss).faceOf d) =
      splitFaceValue R a b hab hmiss f d := rfl

@[simp] theorem split_face_function_old {W : Type w} (f : R.Face → W)
    (hf : f (R.faceOf a) = f (R.faceOf b)) (d : G.Dart) :
    splitFaceFunction R a b hab hmiss f hf
      ((split R a b hab hmiss).faceOf (splitOld a.fst b.fst hab d)) = f (R.faceOf d) := by
  rw [split_face_function_apply, split_face_value_old]

@[simp] theorem split_face_function_out {W : Type w} (f : R.Face → W)
    (hf : f (R.faceOf a) = f (R.faceOf b)) :
    splitFaceFunction R a b hab hmiss f hf
      ((split R a b hab hmiss).faceOf (splitOut a.fst b.fst hab)) = f (R.faceOf b) := by
  rw [split_face_function_apply, split_face_value_out]

@[simp] theorem split_face_function_back {W : Type w} (f : R.Face → W)
    (hf : f (R.faceOf a) = f (R.faceOf b)) :
    splitFaceFunction R a b hab hmiss f hf
      ((split R a b hab hmiss).faceOf (splitBack a.fst b.fst hab)) = f (R.faceOf a) := by
  rw [split_face_function_apply, split_face_value_back]

/-- The corner before `R.next a` is the corner after `a`; its face is that of `a.symm`. -/
@[simp] theorem face_of_next_eq_face_of_symm (d : G.Dart) :
    R.faceOf (R.next d) = R.faceOf d.symm := by
  exact R.face_of_face_next d.symm

/-- The original after-corner premise is exactly the existing split operation's premise. -/
theorem after_corners_same_face_iff :
    R.faceOf (R.next a) = R.faceOf (R.next b) ↔ R.faceOf a.symm = R.faceOf b.symm := by
  rw [face_of_next_eq_face_of_symm, face_of_next_eq_face_of_symm]

end SimpleGraph.PlaneMapConstruction
