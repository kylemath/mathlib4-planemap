/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FiveColorTheorem
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Icosahedron

/-!
# A demonstration of the Five Colour Theorem for plane maps

## The theorem

Every graph presented as a plane map can have its vertices coloured with five
colours so that adjacent vertices receive different colours. In this library the
statement is

```
theorem SimpleGraph.PlaneMap.five_color_theorem {n : ℕ} (M : PlaneMap n) :
    M.graph.Colorable 5
```

with a function-valued form `SimpleGraph.PlaneMap.exists_five_colouring`
(`∃ c : Fin n → Fin 5, ∀ u v, M.Adj u v → c u ≠ c v`), and a more general form
`SimpleGraph.SphericalMap.five_color_theorem` for `SphericalMap`s.

## What "planar" means here

Planarity is not a geometric hypothesis (no points, curves or topology). A planar
graph is presented by a *combinatorial map* on `Fin n`: a finite simple graph `G`
together with a rotation system `next : Equiv.Perm G.Dart`, the cyclic order of
the outgoing darts at every vertex, as in the clockwise order of edges around a
vertex of a drawing on the sphere. The rotation determines the *faces* as the
orbits of `faceNext` on darts.

* A `PlaneMap n` is such a rotation system that is *generated*: start from one
  vertex and repeatedly (a) attach a new vertex to a corner of an existing
  vertex or (b) insert a missing edge between two vertices on the same face.
  These are exactly the operations that build a connected plane graph one step
  at a time, so every `PlaneMap` is the combinatorial shadow of a connected
  graph drawn in the plane.
* A `SphericalMap n` is a rotation system satisfying the algebraic condition
  `RotationSystem.Fills`: every even edge set (every vertex incidence even mod
  two) is a mod-two sum of face boundaries. This is the cycle-space form of the
  Jordan curve theorem for the sphere (every cycle separates), and it is
  stable under edge deletion, which the induction needs. No connectedness is
  assumed. `SphericalMap.ofPlaneMap` shows every `PlaneMap` is one, using the
  proved `JordanEven` theorem.

Relation to planarity: a graph drawn in the plane or on the sphere has such a
map (read off the clockwise orders), so the theorem applies to every graph that
comes with one. What is proved is the colouring statement for graphs *given*
a `PlaneMap` or `SphericalMap`. What is not proved is that an abstractly planar
graph (defined by Kuratowski minors, or by a topological embedding) admits such a
map; that representation theorem is not part of this development.

## The worked example

The icosahedron is supplied in `Mathlib.Combinatorics.SimpleGraph.PlaneMap.Icosahedron`
as an explicit `SphericalMap 12`: twelve vertices, thirty edges, twenty triangular
faces, with the rotation and the `Fills` certificate checked by the kernel. Below
we apply the Five Colour Theorem to it to get a 5-colouring, then compare with
the colouring extracted from the theorem. (An independent table checked by `decide`
lives in the test file, as a sanity check only.)
-/

@[expose] public section

namespace SimpleGraph.Icosahedron

/-- The Five Colour Theorem applied to the icosahedron. -/
theorem icosahedron_colorable_five : sphericalMap.graph.Colorable 5 :=
  sphericalMap.five_color_theorem

/-- A five-colouring of the icosahedron, obtained from the Five Colour Theorem
(`sphericalMap.five_color_theorem`) alone. -/
theorem icosahedron_five_colouring :
    ∃ c : Fin 12 → Fin 5, ∀ u v, sphericalMap.graph.Adj u v → c u ≠ c v := by
  obtain ⟨c⟩ := icosahedron_colorable_five
  exact ⟨c, fun _ _ h => c.valid h⟩

end SimpleGraph.Icosahedron
