module

import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeBoundary
import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeRepartition

open SimpleGraph
/-- info: 'SimpleGraph.Kempe.swap_removes_singleton_boundary_colour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kempe.swap_removes_singleton_boundary_colour
/-- info: 'SimpleGraph.Kempe.boundary_card_le_three_of_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kempe.boundary_card_le_three_of_missing
/-- info: 'SimpleGraph.Kempe.singleton_chain_boundary_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kempe.singleton_chain_boundary_target
/-- info: 'SimpleGraph.Kempe.singleton_chain_proper_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kempe.singleton_chain_proper_target

private def exampleGraph : SimpleGraph (Fin 5) where
  Adj u v := (u = 0 ∧ v = 4) ∨ (u = 4 ∧ v = 0)
  symm := ⟨by intro u v; tauto⟩
  loopless := ⟨by intro u; omega⟩

private instance : DecidableRel exampleGraph.Adj := fun u v =>
  inferInstanceAs (Decidable ((u = 0 ∧ v = 4) ∨ (u = 4 ∧ v = 0)))
private def exampleColour : Fin 5 → Fin 4 := ![0, 1, 2, 3, 1]
private def exampleBoundary : Finset (Fin 5) := {0, 1, 2, 3}

example : FiniteReachability.component
    (Kempe.bichromaticSubgraph exampleGraph exampleColour 0 1) 0 = {0, 4} := by decide

example : FiniteReachability.componentSwap exampleGraph exampleColour 0 1 0 =
    (![1, 1, 2, 3, 0] : Fin 5 → Fin 4) := by decide

example : Kempe.IsProperColouring exampleGraph
    (FiniteReachability.componentSwap exampleGraph exampleColour 0 1 0) ∧
    (exampleBoundary.image
      (FiniteReachability.componentSwap exampleGraph exampleColour 0 1 0)).card ≤ 3 := by
  apply Kempe.singleton_chain_proper_target exampleGraph exampleColour
    (by unfold Kempe.IsProperColouring; decide) exampleBoundary 0 1 (by decide) 0 rfl
  · decide
  · intro v hv hr
    have hm := (FiniteReachability.mem_component_iff
      (Kempe.bichromaticSubgraph exampleGraph exampleColour 0 1) 0 v).mpr hr
    have hh : ∀ v ∈ exampleBoundary, v ∈ FiniteReachability.component
        (Kempe.bichromaticSubgraph exampleGraph exampleColour 0 1) 0 → v = 0 := by decide
    exact hh v hv hm

/-- info: 'SimpleGraph.Kempe.boundaryMassRank_lt_of_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kempe.boundaryMassRank_lt_of_target
/-- info: 'SimpleGraph.Kempe.singleton_chain_rank_decreases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kempe.singleton_chain_rank_decreases
/-- info: 'SimpleGraph.Kempe.singleton_locked_of_no_rank_decrease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kempe.singleton_locked_of_no_rank_decrease

example : Kempe.boundaryMassRank exampleGraph
    (FiniteReachability.componentSwap exampleGraph exampleColour 0 1 0) exampleBoundary 6 <
    Kempe.boundaryMassRank exampleGraph exampleColour exampleBoundary 6 := by
  apply Kempe.singleton_chain_rank_decreases exampleGraph exampleColour exampleBoundary
    6 (by decide) (by decide) 0 1 (by decide) 0 rfl
  · decide
  · intro v hv hr
    have hm := (FiniteReachability.mem_component_iff
      (Kempe.bichromaticSubgraph exampleGraph exampleColour 0 1) 0 v).mpr hr
    have hh : ∀ v ∈ exampleBoundary, v ∈ FiniteReachability.component
        (Kempe.bichromaticSubgraph exampleGraph exampleColour 0 1) 0 → v = 0 := by decide
    exact hh v hv hm
