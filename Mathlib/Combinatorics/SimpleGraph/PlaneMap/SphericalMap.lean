/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.JordanCycle

/-!
# An algebraic spherical-map carrier

A finite rotation system is spherical for this development when every even
edge combination is a sum of face boundaries over `ZMod 2`. Generated plane
maps satisfy this property by the proved JordanEven theorem. Connectedness
and construction history are not part of this carrier, so edge deletion can
be handled directly.
-/

@[expose] public section
namespace SimpleGraph

open scoped BigOperators

/-- The mod-two incidence boundary of an edge combination. -/
noncomputable def edgeIncidence {n : ℕ} (G : SimpleGraph (Fin n))
    (φ : G.edgeSet → ZMod 2) (x : Fin n) : ZMod 2 := by
  classical
  exact ∑ e : G.edgeSet, if x ∈ e.val then φ e else 0

/-- Every even edge combination has a face potential. -/
def RotationSystem.Fills {n : ℕ} {G : SimpleGraph (Fin n)} (R : RotationSystem G) : Prop :=
  ∀ φ : G.edgeSet → ZMod 2, (∀ x, edgeIncidence G φ x = 0) →
    ∃ c : R.Face → ZMod 2, ∀ d : G.Dart,
      φ (RotationSystem.edgeOfDart d) = c (R.faceOf d) + c (R.faceOf d.symm)

/-- A finite rotation system whose even edge combinations bound face sums. -/
structure SphericalMap (n : ℕ) where
  graph : SimpleGraph (Fin n)
  rotation : RotationSystem graph
  fills : rotation.Fills

namespace SphericalMap

variable {n : ℕ}

abbrev Adj (M : SphericalMap n) := M.graph.Adj
abbrev Dart (M : SphericalMap n) := M.graph.Dart
abbrev Face (M : SphericalMap n) := M.rotation.Face
abbrev faceOf (M : SphericalMap n) := M.rotation.faceOf
noncomputable instance (M : SphericalMap n) : DecidableRel M.graph.Adj := Classical.decRel _

noncomputable def edgeDart (G : SimpleGraph (Fin n)) (e : G.edgeSet) : G.Dart :=
  Classical.choose (RotationSystem.edge_of_dart_surjective e)

theorem edgeDart_spec (G : SimpleGraph (Fin n)) (e : G.edgeSet) :
    RotationSystem.edgeOfDart (edgeDart G e) = e :=
  Classical.choose_spec (RotationSystem.edge_of_dart_surjective e)

noncomputable def faceSum (M : SphericalMap n) (c : M.Face → ZMod 2)
    (e : M.graph.edgeSet) : ZMod 2 :=
  c (M.faceOf (edgeDart M.graph e)) + c (M.faceOf (edgeDart M.graph e).symm)

noncomputable abbrev incidentSum (M : SphericalMap n) := edgeIncidence M.graph

def IsEven (M : SphericalMap n) (φ : M.graph.edgeSet → ZMod 2) : Prop :=
  ∀ x, incidentSum M φ x = 0

theorem cycle_faceSum_edgeOfDart (M : SphericalMap n)
    (c : M.Face → ZMod 2) (d : M.Dart) :
    faceSum M c (RotationSystem.edgeOfDart d) = c (M.faceOf d) + c (M.faceOf d.symm) := by
  obtain h | h := (RotationSystem.edge_of_dart_eq_iff
    (edgeDart M.graph (RotationSystem.edgeOfDart d)) d).mp (edgeDart_spec _ _)
  · simp [faceSum, h]
  · simp [faceSum, h, add_comm]

theorem even_is_face_sum (M : SphericalMap n) (φ : M.graph.edgeSet → ZMod 2)
    (hφ : IsEven M φ) : ∃ c : M.Face → ZMod 2, ∀ e, φ e = faceSum M c e := by
  obtain ⟨c, hc⟩ := M.fills φ hφ
  refine ⟨c, fun e => ?_⟩
  simpa only [edgeDart_spec, faceSum] using hc (edgeDart M.graph e)

alias mem_edgeOfDart_iff := PlaneMap.mem_edgeOfDart_iff

/-- The previously proved PlaneMap theory supplies the algebraic carrier. -/
def ofPlaneMap (M : PlaneMap n) : SphericalMap n where
  graph := M.graph
  rotation := M.rotation
  fills := by
    intro φ hφ
    obtain ⟨c, hc⟩ := PlaneMap.even_is_face_sum M φ hφ
    exact ⟨c, fun d => (hc _).trans (PlaneMap.cycle_faceSum_edgeOfDart M c d)⟩

end SphericalMap
end SimpleGraph
