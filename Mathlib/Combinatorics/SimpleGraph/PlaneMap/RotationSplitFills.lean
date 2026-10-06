/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationSplit
public import Mathlib.Tactic.Ring

/-!
# Chord insertion preserves filling on a raw rotation carrier

Inserting a missing edge between two corners of one face preserves `Fills`.
If an even combination vanishes on the new edge, restrict it to the old map,
use the old face potential, and give both halves of the split face the old
face's value. Otherwise add the boundary of the new face containing the
outgoing new dart first. This is the raw-carrier form of
`PlaneMap.even_boundary_split`: no generated construction history,
connectedness, or face-length premise is used.
-/

@[expose] public section
namespace SimpleGraph
open scoped BigOperators
open PlaneMapConstruction
namespace RotationSystem
open Classical
variable {n : ℕ} {G : SimpleGraph (Fin n)}

private theorem zmod2_add_self' (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- The two orientations of the inserted chord lie on different new faces. -/
theorem split_out_ne_back_face (R : RotationSystem G) (a b : G.Dart)
    (hface : R.faceOf a = R.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    (split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst) ≠
      (split R a b hfst hadj).faceOf (splitBack (G := G) a.fst b.fst hfst) := by
  intro h
  have hr := ((split R a b hfst hadj).face_of_eq_iff _ _).1 h
  have hl := split_label_relation R a b hfst hadj hface hr
  simp [split_label_out, split_label_back] at hl

/-- Filling for even combinations that vanish on the inserted chord. -/
theorem split_fills_of_zero (R : RotationSystem G) (hR : R.Fills) (a b : G.Dart)
    (hface : R.faceOf a = R.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst)
    (ψ : (splitGraph G a.fst b.fst hfst).edgeSet → ZMod 2)
    (hψ : ∀ x, edgeIncidence (splitGraph G a.fst b.fst hfst) ψ x = 0)
    (h0 : ψ (splitNewEdge G a b hfst hadj) = 0) :
    ∃ c : (split R a b hfst hadj).Face → ZMod 2,
      ∀ d : (splitGraph G a.fst b.fst hfst).Dart,
        ψ (edgeOfDart d) =
          c ((split R a b hfst hadj).faceOf d) + c ((split R a b hfst hadj).faceOf d.symm) := by
  obtain ⟨c0, hc0⟩ := hR (restrictSplit G a b hfst hadj ψ)
    (even_restrict_split G a b hfst hadj ψ hψ h0)
  refine ⟨splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface), ?_⟩
  intro d
  obtain ⟨x, rfl⟩ := (splitDartEquiv a.fst b.fst hfst hadj).surjective d
  cases x with
  | inl d0 =>
    change ψ (edgeOfDart (splitOld a.fst b.fst hfst d0)) =
      splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
          ((split R a b hfst hadj).faceOf (splitOld a.fst b.fst hfst d0)) +
        splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
          ((split R a b hfst hadj).faceOf (splitOld a.fst b.fst hfst d0).symm)
    rw [split_old_symm, split_face_function_old, split_face_function_old,
      split_old_edge G a b hfst hadj d0]
    exact hc0 d0
  | inr t =>
    cases t with
    | false =>
      change ψ (edgeOfDart (splitOut (G := G) a.fst b.fst hfst)) =
        splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
            ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst)) +
          splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
            ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst).symm)
      rw [split_out_edge G a b hfst hadj, h0]
      change (0 : ZMod 2) =
        splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
            ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst)) +
          splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
            ((split R a b hfst hadj).faceOf (splitBack (G := G) a.fst b.fst hfst))
      rw [split_face_function_out, split_face_function_back, hface, zmod2_add_self']
    | true =>
      change ψ (edgeOfDart (splitBack (G := G) a.fst b.fst hfst)) =
        splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
            ((split R a b hfst hadj).faceOf (splitBack (G := G) a.fst b.fst hfst)) +
          splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
            ((split R a b hfst hadj).faceOf (splitBack (G := G) a.fst b.fst hfst).symm)
      rw [split_back_edge G a b hfst hadj, h0]
      change (0 : ZMod 2) =
        splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
            ((split R a b hfst hadj).faceOf (splitBack (G := G) a.fst b.fst hfst)) +
          splitFaceFunction R a b hfst hadj c0 (congrArg c0 hface)
            ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst))
      rw [split_face_function_out, split_face_function_back, hface, zmod2_add_self']

/-- **Chord insertion preserves filling.** Inserting a missing edge between two
corners of one face of a filling rotation system yields a filling rotation system. -/
theorem split_fills (R : RotationSystem G) (hR : R.Fills) (a b : G.Dart)
    (hface : R.faceOf a = R.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    (split R a b hfst hadj).Fills := by
  intro φ hφ
  by_cases h0 : φ (splitNewEdge G a b hfst hadj) = 0
  · exact split_fills_of_zero R hR a b hface hfst hadj φ hφ h0
  have h1 : φ (splitNewEdge G a b hfst hadj) = 1 := by
    generalize φ (splitNewEdge G a b hfst hadj) = x at h0
    fin_cases x
    · exact (h0 rfl).elim
    · rfl
  let ψ : (splitGraph G a.fst b.fst hfst).edgeSet → ZMod 2 := fun e =>
    φ e + faceBoundary (split R a b hfst hadj)
      ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst)) e
  have hψ : ∀ x, edgeIncidence (splitGraph G a.fst b.fst hfst) ψ x = 0 :=
    even_add_face (split R a b hfst hadj) φ hφ
      ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst))
  have hne := split_out_ne_back_face R a b hface hfst hadj
  have hψ0 : ψ (splitNewEdge G a b hfst hadj) = 0 := by
    change φ (splitNewEdge G a b hfst hadj) + faceBoundary (split R a b hfst hadj)
      ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst))
        (splitNewEdge G a b hfst hadj) = 0
    rw [h1, ← split_out_edge G a b hfst hadj, faceBoundary_edgeOfDart]
    have hback : (split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst).symm ≠
        (split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst) := by
      change (split R a b hfst hadj).faceOf (splitBack (G := G) a.fst b.fst hfst) ≠
        (split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst)
      exact fun h => hne h.symm
    rw [ite_eq_left rfl, ite_eq_right hback]
    decide
  obtain ⟨c, hc⟩ := split_fills_of_zero R hR a b hface hfst hadj ψ hψ hψ0
  refine ⟨fun F => c F +
    if F = (split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst) then 1 else 0, ?_⟩
  intro d
  have hφd : φ (edgeOfDart d) = ψ (edgeOfDart d) + faceBoundary (split R a b hfst hadj)
      ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst)) (edgeOfDart d) := by
    change φ (edgeOfDart d) =
      (φ (edgeOfDart d) + faceBoundary (split R a b hfst hadj)
        ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst)) (edgeOfDart d)) +
      faceBoundary (split R a b hfst hadj)
        ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst)) (edgeOfDart d)
    rw [add_assoc, zmod2_add_self', add_zero]
  rw [hφd, hc d, faceBoundary_edgeOfDart]
  by_cases h1 : (split R a b hfst hadj).faceOf d =
      (split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst) <;>
    by_cases h2 : (split R a b hfst hadj).faceOf d.symm =
      (split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst) <;>
    simp [h1, h2] <;> ring

end RotationSystem
end SimpleGraph
