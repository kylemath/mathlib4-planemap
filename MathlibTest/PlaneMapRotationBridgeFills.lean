module
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationBridgeFills

open SimpleGraph SimpleGraph.PlaneMapConstruction

/-- info: 'SimpleGraph.RotationSystem.sum_incidence_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.sum_incidence_component
/-- info: 'SimpleGraph.RotationSystem.bridge_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.bridge_coeff_zero
/-- info: 'SimpleGraph.RotationSystem.reachable_iff_of_faceRelation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.reachable_iff_of_faceRelation
/-- info: 'SimpleGraph.RotationSystem.split_fills_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.split_fills_bridge
/-- info: 'SimpleGraph.SphericalMap.exists_spherical_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SphericalMap.exists_spherical_bridge

namespace BridgeFillsRegression

-- Filling transports along any bridge between two components of a filling carrier.
example {n : ℕ} {G : SimpleGraph (Fin n)} (R : RotationSystem G) (hR : R.Fills)
    (a b : G.Dart) (hab : a.fst ≠ b.fst) (hmiss : ¬ G.Adj a.fst b.fst)
    (hsep : ¬ G.Reachable a.fst b.fst) :
    (split R a b hab hmiss).Fills :=
  RotationSystem.split_fills_bridge R hR a b hab hmiss hsep

-- An even combination on the bridged graph has zero coefficient on the bridge.
example {n : ℕ} {G : SimpleGraph (Fin n)} (a b : G.Dart) (hab : a.fst ≠ b.fst)
    (hmiss : ¬ G.Adj a.fst b.fst) (hsep : ¬ G.Reachable a.fst b.fst)
    (φ : (splitGraph G a.fst b.fst hab).edgeSet → ZMod 2)
    (hφ : ∀ x, edgeIncidence (splitGraph G a.fst b.fst hab) φ x = 0) :
    φ (RotationSystem.splitNewEdge G a b hab hmiss) = 0 :=
  RotationSystem.bridge_coeff_zero a b hab hmiss hsep φ hφ

-- Joining two components of a spherical map gives a spherical map.
example {n : ℕ} (M : SphericalMap n) (a b : M.Dart) (hsep : ¬ M.graph.Reachable a.fst b.fst) :
    ∃ (N : SphericalMap n) (huv : a.fst ≠ b.fst),
      ¬ M.Adj a.fst b.fst ∧ N.graph = splitGraph M.graph a.fst b.fst huv :=
  M.exists_spherical_bridge a b hsep

end BridgeFillsRegression
