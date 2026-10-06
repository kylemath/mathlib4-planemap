module

import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalRankedContact

open SimpleGraph

/--
info: 'SimpleGraph.SphericalMap.ranked_good_target_path' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.ranked_good_target_path

/--
info: 'SimpleGraph.SphericalMap.ranked_good_target_path_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.ranked_good_target_path_of_le

/--
info: 'SimpleGraph.SphericalMap.colorable_of_ranked_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.colorable_of_ranked_good

/--
info: 'SimpleGraph.SphericalMap.empty_ranked_region_of_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.empty_ranked_region_of_descent

/--
info: 'SimpleGraph.SphericalMap.ranked_descent_of_empty_region' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.ranked_descent_of_empty_region

/--
info: 'SimpleGraph.SphericalMap.four_color_of_empty_ranked_region' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.four_color_of_empty_ranked_region

/--
info: 'SimpleGraph.SphericalMap.four_color_of_ranked_macro_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.four_color_of_ranked_macro_descent

/--
info: 'SimpleGraph.SphericalMap.ranked_good_mass_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.ranked_good_mass_iff

/--
info: 'SimpleGraph.SphericalMap.ranked_mass_descent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.ranked_mass_descent_iff

/--
info: 'SimpleGraph.SphericalMap.empty_ranked_mass_region_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.empty_ranked_mass_region_iff

/--
info: 'SimpleGraph.SphericalMap.four_color_of_mass_rank_specialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.four_color_of_mass_rank_specialization

-- The rank is an input fixed before the graph/root/colouring quantifiers.
example (rank : SphericalMap.DeletionRankFamily)
    (h : SphericalMap.RankedMacroDescentHypothesis rank)
    {n : ℕ} (M : SphericalMap n) : M.graph.Colorable 4 :=
  SphericalMap.four_color_of_ranked_macro_descent h M

-- Existing mass hypotheses pass to the generic interface by definitional equality.
example (h : SphericalMap.MassMacroDescentHypothesis) :
    SphericalMap.RankedMacroDescentHypothesis SphericalMap.massRankFamily := h

/--
info: 'SimpleGraph.SphericalMap.bounded_lex_scalar_lt_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.bounded_lex_scalar_lt_iff

/--
info: 'SimpleGraph.SphericalMap.bounded_binary_scalar_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.bounded_binary_scalar_le

-- The secondary coordinate may increase when the binary primary coordinate falls.
example (B : ℕ) : (B + 1) * 0 + B < (B + 1) * 1 + 0 := by
  apply (SphericalMap.bounded_lex_scalar_lt_iff (by omega) (by omega)).2
  exact Or.inl (by omega)

-- At a fixed primary coordinate, the scalar compares secondary coordinates exactly.
example {p s s' B : ℕ} (hs : s ≤ B) (hs' : s' ≤ B) :
    (B + 1) * p + s' < (B + 1) * p + s ↔ s' < s := by
  rw [SphericalMap.bounded_lex_scalar_lt_iff hs hs']
  simp
