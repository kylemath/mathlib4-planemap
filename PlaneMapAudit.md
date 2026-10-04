# PlaneMap Five Colour audit

Date: 3 October 2026
Checkout: `/Users/fulkanjou/mathlib4-planemap`
Toolchain: `leanprover/lean4:v4.35.0-rc3`

## Verdict

No invalid hypothesis, circular proof dependency, placeholder, or stale custom
artifact was found in the final theorem's proof. All 26 custom production
modules and both regression modules re-elaborate successfully into an isolated
Lean library. The final theorem and audited infrastructure depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

This is a code and source-rebuild audit, not a separate formal verification of
Lean or a fresh build of all upstream Mathlib dependencies.

## Findings

### 1. Mathematical scope remains narrower than arbitrary planar graphs

`PlaneMap` packages a connected simple graph on `Fin n`, a cyclic rotation,
and a proof of generation from one vertex by leaf attachment and same-face
edge insertion. Its final theorem has no additional face-length or separation
premise. `Colorable 5` is Mathlib's ordinary proper vertex-colouring predicate.

There is still no theorem converting every arbitrary geometrically planar
finite graph to this representation (up to relabelling and components), nor
a proved equivalence between the new `SphericalMap` condition and an existing
independent definition of geometric planarity. Therefore the result should
continue to be described as the Five Colour Theorem for generated combinatorial
PlaneMaps. This boundary does not invalidate that statement.

`SphericalMap.fills` is a substantial planarity-related field, not a generic
property of all rotation systems. Crucially, `ofPlaneMap` proves it from
`JordanEven`; it is not an extra assumption in `PlaneMap.five_color_theorem`.

### 2. An unused legacy source failed compilation — repaired

A rebuild of every custom file found duplicate declarations and obsolete
`restrictGrow` calls in `JordanGrow.lean`. Its duplicated lemmas already live
in `Jordan.lean`. No production module imported the old file, so previous
selected-target builds missed it. The final theorem and its complete dependency
chain rebuilt successfully before the audit reached this unrelated file.

`JordanGrow` now imports the canonical proofs and preserves its extra API:
`grow_old_edge_fiber`, `boundary_grow_old`, and `even_boundary_grow_before`.
It compiles. The pre-repair source is preserved as `JordanGrow.before.lean.txt`
in the workspace audit directory.

### 3. Existing sanity tests were weak — independent checks added

The earlier six-clique exclusion followed from `five_color_theorem` itself.
It was a valid consequence, but not independent evidence about separation.
The earlier disconnected-deletion example produced an entirely edgeless graph.

`MathlibTest/PlaneMapIndependentChecks.lean` now proves:

- Six-clique exclusion directly from Heawood separation: two alternating pairs
  of neighbours would have disjoint one-edge connecting walks.
- Isolating the middle of a five-vertex path leaves exactly edges `0–1` and
  `3–4`, plus isolated vertex `2`, and strictly decreases the edge count.

Guarded negative checks verify that neither final colouring theorem is in this
module's imported environment. Both new results also have guarded axiom audits.
The production proof imports no test module.

### 4. Packaging remains unfinished

The custom proof sources are still untracked in the Mathlib checkout. They are
present locally and in the checked workspace snapshot, but not yet included in
a Git commit. The existing foundation/Kempe style warnings also remain. These
are contribution and reproducibility loose ends, not mathematical assumptions.

## Rebuild method and evidence

`audit/rebuild.py` discovers every custom PlaneMap/colouring source and orders
it by imports. It creates a new temporary Lean library, symlinks unchanged
upstream artifacts, and excludes every previous custom module artifact. It
then re-elaborates each custom source with the new library first in `LEAN_PATH`.
Lean resolves the Mathlib package in this overlay, so custom imports cannot
fall back to their previous cached objects.

All 28 modules return exit code 0. `rebuild-results.json` records source hashes
and the overlay path, and per-module logs are retained beside this report.
This check includes `JordanGrow`, `JordanTwoSides`, the final theorem, the
original axiom audit, and the new independent checks.

Source inspection also confirmed:

- No `sorry`, `admit`, `native_decide`, custom axiom declarations, or unsafe
  proof implementations in the custom production files.
- No production imports of `MathlibTest` and no cyclic custom import graph.
- `ofPlaneMap` uses the existing even-face-sum proof, not colourability.
- Deletion preserves the exact spanning subgraph, retaining isolated labels;
  edge count, not vertex count, supplies the induction's strict decrease.
- The low-degree proof does not assume all faces have length at least three:
  that condition is derived inside the high-degree contradiction.
- The final output uses Mathlib's genuine proper-colouring predicate.
