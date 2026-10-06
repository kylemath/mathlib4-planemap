module

import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FiveColorDemo
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Icosahedron

/-! Guard tests for the Five Colour demonstration: standard axioms only. -/

open SimpleGraph

/-- info: 'SimpleGraph.PlaneMap.five_color_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PlaneMap.five_color_theorem

/-- info: 'SimpleGraph.Icosahedron.icosahedron_colorable_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icosahedron.icosahedron_colorable_five

/-- Sanity check only, independent of the theorem: an explicit table, checked by `decide`. -/
public def explicitColouring : Fin 12 → Fin 5 := ![0, 1, 0, 1, 0, 2, 3, 1, 2, 3, 2, 3]

public theorem explicitColouring_valid :
    ∀ u v, Icosahedron.graph.Adj u v → explicitColouring u ≠ explicitColouring v := by
  decide

/-- info: 'explicitColouring_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms explicitColouring_valid

/-- info: [0, 1, 0, 1, 0, 2, 3, 1, 2, 3, 2, 3] -/
#guard_msgs in
#eval (List.finRange 12).map explicitColouring

/-- info: 'SimpleGraph.Icosahedron.icosahedron_five_colouring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Icosahedron.icosahedron_five_colouring

/-- info: @PlaneMap.five_color_theorem : ∀ {n : ℕ} (M : PlaneMap n), M.graph.Colorable 5 -/
#guard_msgs in
#check @PlaneMap.five_color_theorem
