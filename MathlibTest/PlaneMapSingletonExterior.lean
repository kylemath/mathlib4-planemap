module
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SingletonExterior
open SimpleGraph
/-- info: 'SimpleGraph.Kempe.singleton_chain_two_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kempe.singleton_chain_two_exterior

private def pathGraph : SimpleGraph (Fin 4) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := ⟨by intro u v; tauto⟩
  loopless := ⟨by intro u; omega⟩
private instance : DecidableRel pathGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (u.val + 1 = v.val ∨ v.val + 1 = u.val))
private def colour : Fin 4 → Fin 2 := ![0, 1, 0, 1]
private def boundary : Finset (Fin 4) := {0, 3}

/-- The two-exterior-vertex bound is attained by a length-three chain. -/
example : ∃ x y : Fin 4, x ∉ boundary ∧ y ∉ boundary ∧ x ≠ y ∧
    colour x = 1 ∧ colour y = 0 ∧
    (Kempe.bichromaticSubgraph pathGraph colour 0 1).Reachable 0 x ∧
    (Kempe.bichromaticSubgraph pathGraph colour 0 1).Reachable 0 y := by
  apply Kempe.singleton_chain_two_exterior pathGraph colour boundary 0 1
    (by decide) 0 3 rfl rfl (by decide)
  · unfold Kempe.IsProperColouring
    decide
  · decide
  · decide
  · exact (show (Kempe.bichromaticSubgraph pathGraph colour 0 1).Adj 0 1 from
      by decide).reachable.trans ((show
      (Kempe.bichromaticSubgraph pathGraph colour 0 1).Adj 1 2 from by decide).reachable.trans
      (show (Kempe.bichromaticSubgraph pathGraph colour 0 1).Adj 2 3 from by decide).reachable)
