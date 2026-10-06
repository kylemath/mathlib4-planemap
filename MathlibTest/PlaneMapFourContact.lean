module

import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalFourContact

open SimpleGraph

/--
info: 'SimpleGraph.SphericalMap.four_color_of_triangulated_five_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SphericalMap.four_color_of_triangulated_five_extension

-- The degree-five premise stays explicit even on a disconnected original map.
example (h : SphericalMap.TriangulatedFiveExtension) {n : ℕ} (M : SphericalMap n) :
    M.graph.Colorable 4 := M.four_color_of_triangulated_five_extension h
