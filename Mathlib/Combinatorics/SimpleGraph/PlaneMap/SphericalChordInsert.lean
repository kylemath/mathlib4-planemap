/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FaceChord
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationSplitFills

/-!
# A nontriangular face of a spherical map admits a filling chord insertion

Combining `SphericalMap.exists_face_chord` with `RotationSystem.split_fills`:
under minimum positive degree two, every face of length at least four has two
corners whose chord can be inserted, and the resulting rotation system still
fills. The corners are passed to `split` in its insert-before convention, via
`R.next`.
-/

@[expose] public section
namespace SimpleGraph.SphericalMap
open PlaneMapConstruction
variable {n : ℕ}

/-- A nontriangular face has a chord whose insertion preserves filling. -/
theorem exists_fills_chord (M : SphericalMap n)
    (hdeg : ∀ x ∈ M.graph.support, 2 ≤ M.graph.degree x)
    (d : M.Dart) (hlen : 4 ≤ M.rotation.faceLength (M.faceOf d)) :
    ∃ (a b : M.Dart) (hab : a.fst ≠ b.fst) (hmiss : ¬ M.Adj a.fst b.fst),
      M.faceOf a = M.faceOf b ∧ (split M.rotation a b hab hmiss).Fills := by
  obtain ⟨a, b, ha, hb, hne, hnadj⟩ := M.exists_face_chord hdeg d hlen
  have hfa : (M.rotation.next a).fst = a.fst := M.rotation.next_fst a
  have hfb : (M.rotation.next b).fst = b.fst := M.rotation.next_fst b
  have hab : (M.rotation.next a).fst ≠ (M.rotation.next b).fst := by
    rw [hfa, hfb]; exact hne
  have hmiss : ¬ M.Adj (M.rotation.next a).fst (M.rotation.next b).fst := by
    rw [hfa, hfb]; exact hnadj
  have hface : M.faceOf (M.rotation.next a) = M.faceOf (M.rotation.next b) :=
    (after_corners_same_face_iff M.rotation a b).2 (ha.trans hb.symm)
  exact ⟨M.rotation.next a, M.rotation.next b, hab, hmiss, hface,
    RotationSystem.split_fills M.rotation M.fills _ _ hface hab hmiss⟩

/-- The chord insertion packaged as a new spherical map on the same labels. -/
theorem exists_spherical_chord (M : SphericalMap n)
    (hdeg : ∀ x ∈ M.graph.support, 2 ≤ M.graph.degree x)
    (d : M.Dart) (hlen : 4 ≤ M.rotation.faceLength (M.faceOf d)) :
    ∃ (N : SphericalMap n) (u v : Fin n) (huv : u ≠ v),
      ¬ M.Adj u v ∧ N.graph = splitGraph M.graph u v huv := by
  obtain ⟨a, b, hab, hmiss, -, hfills⟩ := M.exists_fills_chord hdeg d hlen
  exact ⟨⟨_, split M.rotation a b hab hmiss, hfills⟩, a.fst, b.fst, hab, hmiss, rfl⟩

end SimpleGraph.SphericalMap
