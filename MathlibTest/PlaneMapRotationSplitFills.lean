module
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalChordInsert

open SimpleGraph SimpleGraph.PlaneMapConstruction

/-- info: 'SimpleGraph.RotationSystem.split_out_ne_back_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.split_out_ne_back_face
/-- info: 'SimpleGraph.RotationSystem.split_fills_of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.split_fills_of_zero
/-- info: 'SimpleGraph.RotationSystem.split_fills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.split_fills
/-- info: 'SimpleGraph.SphericalMap.exists_fills_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.exists_fills_chord
/-- info: 'SimpleGraph.SphericalMap.exists_spherical_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.exists_spherical_chord

namespace ChordFillsRegression

-- Filling transports along any same-face chord insertion of a filling carrier.
example {n : ℕ} {G : SimpleGraph (Fin n)} (R : RotationSystem G) (hR : R.Fills)
    (a b : G.Dart) (hface : R.faceOf a = R.faceOf b) (hab : a.fst ≠ b.fst)
    (hmiss : ¬ G.Adj a.fst b.fst) :
    (split R a b hab hmiss).Fills :=
  RotationSystem.split_fills R hR a b hface hab hmiss

-- The new chord's two orientations are on different faces after insertion.
example {n : ℕ} {G : SimpleGraph (Fin n)} (R : RotationSystem G)
    (a b : G.Dart) (hface : R.faceOf a = R.faceOf b) (hab : a.fst ≠ b.fst)
    (hmiss : ¬ G.Adj a.fst b.fst) :
    (split R a b hab hmiss).faceOf (splitOut (G := G) a.fst b.fst hab) ≠
      (split R a b hab hmiss).faceOf (splitBack (G := G) a.fst b.fst hab) :=
  RotationSystem.split_out_ne_back_face R a b hface hab hmiss

-- A spherical map with a nontriangular face gains an edge and stays spherical.
example {n : ℕ} (M : SphericalMap n)
    (hdeg : ∀ x ∈ M.graph.support, 2 ≤ M.graph.degree x)
    (d : M.Dart) (hlen : 4 ≤ M.rotation.faceLength (M.faceOf d)) :
    ∃ (N : SphericalMap n) (u v : Fin n) (huv : u ≠ v),
      ¬ M.Adj u v ∧ N.graph = splitGraph M.graph u v huv :=
  M.exists_spherical_chord hdeg d hlen

end ChordFillsRegression
