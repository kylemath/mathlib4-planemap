# PlaneMap Five Colour Theorem — completed

Date: 3 October 2026
Authoritative checkout: `/Users/fulkanjou/mathlib4-planemap`
Toolchain: `leanprover/lean4:v4.35.0-rc3`

The general theorem is proved and compiled:

```lean
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FiveColorTheorem

example {n : ℕ} (M : SimpleGraph.PlaneMap n) : M.graph.Colorable 5 :=
  M.five_color_theorem
```

`PlaneMap.exists_five_colouring` also returns an existentially quantified
function `Fin n → Fin 5` with the proper-colouring property. There is no
face-length, triangulation, separation, or connected-deletion premise.
The scope is generated combinatorial PlaneMaps; this does not establish a
representation theorem for arbitrary geometrically planar graphs.

## Proof route

`JordanWalkParity` and `FiveColorSeparation` prove `heawood_hopposite` from
closed-walk parity. The current-Mathlib Kempe ports supply the local extension.
The original GraphColour Lean 4.15 package remains unchanged.

`SphericalMap` is a finite rotation system with the mod-two filling property.
`ofPlaneMap` proves that property from the existing `JordanEven` theorem.
`ErasePermutation` and `RotationDelete` bypass deleted darts in vertex
rotations. `SphericalDelete` proves that edge deletion preserves filling,
then proves spanning-subgraph closure and vertex isolation with strict
edge-count decrease. This carrier permits disconnected graphs and isolated
vertices. No generated-component reconstruction theorem is assumed.

`SphericalDegree` uses rank-nullity, the filling property, and face counting
to produce a positive-degree vertex of degree at most five whenever an edge
exists. It handles short faces and disconnected graphs without extra premises.
`SphericalFiveColor` supplies the local Kempe extension for this carrier.
`FiveColorTheorem` inducts on edge count and transfers the result to PlaneMap.

## Verification

- `lake build Mathlib.Combinatorics.SimpleGraph.PlaneMap.FiveColorTheorem
  MathlibTest.PlaneMapFiveColor` exits 0.
- The original `JordanTwoSides` foundation target also builds.
- Guarded axiom audits cover the separation, local extension, deletion,
  low-degree, and final theorems. Dependencies are only `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx` or additional axioms.
- Proof sources contain no `sorry`, `admit`, axiom declarations, or
  `native_decide`.
- Regression applications include symbolic paths and cycles, the tetrahedron,
  deletion of the centre of a three-vertex path, and exclusion of the six-clique
  from the spherical carrier.

The mathematical Five Colour goal is complete. Mathlib contribution cleanup
remains a separate task: existing foundation/Kempe style warnings and API
organization need review before an upstream submission. No PR was opened.
There is no Four Colour Theorem claim and no general `cycle_two_sides` claim
for possibly disconnected `CycleCut`.

## Subsequent source audit

An isolated rebuild of all 26 custom production modules and both regression
modules passes. The audit found and repaired an unused stale `JordanGrow`
module; it was not a dependency of the final theorem. Independent tests now
exclude the six-clique using separation without importing the final theorem,
and check deletion leaving two components with edges. See `PlaneMapAudit.md`
for the findings, scope boundary, and reproduction method.
