# Four Colour gates A/B: checked scope

Date: 4 October 2026. Lean: `leanprover/lean4:v4.35.0-rc3`.

## Results

The `FourColorExtension`, `SphericalSmallOrder`, `FourColorSmallOrder`, and `FourEliminationOrder` modules compile. The additional `Icosahedron`, `FiniteFourExtension`, `DegreeFiveOutside`, and `SupportTransport` modules also compile. They prove spherical degree-four extension, `e + 2 ≤ s + f`, the twelve-nonisolated-vertex lower bound under minimum positive degree five, four-colourability under spherical elimination, and four-colourability through eleven vertices. Finite elimination certificates are sound and have length at most the initial edge count. The small-order existence theorem requires no connectedness, triangulation, or face-length premise.

`Coloring/FiniteReachability` supplies executable component extraction and Kempe component swapping. Extraction agrees with reachability, and swapping preserves properness. Its full-scan accounting charges `n³` adjacency slots, independently of any claim about runtime of an arbitrary adjacency decider or a complete solver.

`Icosahedron.sphericalMap` is a genuine spherical carrier with twelve vertices, thirty edges, twenty triangular faces, degree five everywhere, and support size twelve. Its filling proof is a finite linear certificate checked by the kernel. `six_le_degreeFiveOutside` proves at least six degree-five vertices outside every nonisolated anchor's closed neighbourhood under minimum positive degree five. That availability result supplies no Kempe escape or good-root selection theorem.

`finiteFourColorExtend` computes a proper four-colouring from executable adjacency, the spherical rotation data, a degree-at-most-four vertex, and its proper deletion colouring. It computes its own cyclic neighbour enumeration. The guarded tests exercise automatic singleton extension, a positive four-neighbour rotation search, and a nontrivial component swap. A full spherical degree-four swap execution fixture remains outstanding.

`SupportTransport` supplies the exact spherical carrier on the nonisolated support: adjacency and degree correspondence, a conjugated cyclic rotation, filling preservation, extension of a support colouring over isolated labels, and strict support-cardinality decrease after isolating a nonisolated root. Its label equivalence and colouring extension are classical; this is a carrier theorem rather than an executable relabeller. The tests cover disconnected deletion, empty support and minimum-degree transport. Edge insertion and triangulation completion are proved below; the support construction remains classical.

`FaceCorner` proves, for arbitrary finite rotation systems, that minimum positive degree two excludes immediate facial reversal and forces every dart-containing face to have length at least three. It does not prove chord availability or triangulation completion.

`KempeMass`, `KempeRepartition`, and `KempeBoundary` formalise WP7 Lemmas 7.1, 7.2, and 7.4. They prove actual boundary-weighted component mass locality, fixed mixed-graph re-partition, the quadratic mass bound, target attainment by a free singleton chain, and its strict rank decrease. No spherical hypothesis is used. The mass definition is noncomputable and supplies no executable solver, uniform escape, or polynomial warning bound.

`FaceChord` proves `exists_face_chord`. In a spherical map with minimum positive degree two, every face of length at least four has two corners at distinct, nonadjacent vertices; repeated facial vertices are allowed. `InsertPermutation`, `RotationInsert`, `RotationSplit` and `RotationBoundary` supply raw-carrier tools:
- successor-swap orbit algebra;
- transport of face observables through `split`;
- edge bookkeeping for the inserted edge;
- face-boundary parity.

`RotationSplitFills` proves `RotationSystem.split_fills`: **inserting a missing edge between two corners of one face of a filling rotation system preserves filling.** It also proves `split_out_ne_back_face`: the two new darts lie on different faces. This is the raw-carrier form of `PlaneMap.even_boundary_split`. It uses no generated history, connectedness or face-length premise. `SphericalChordInsert` combines the two: under minimum positive degree two, a face of length at least four admits a chord insertion that yields another `SphericalMap` on the same labels.

`RotationBridgeFills` proves `RotationSystem.split_fills_bridge`: **inserting an edge between corners in two different connected components preserves filling.**
- An even combination vanishes on the bridge (`bridge_coeff_zero`): summing the even condition over one component counts old edges twice and the bridge once.
- Face orbits stay in one component (`reachable_iff_of_faceRelation`). So the old potential can be shifted by a constant on one component before lifting.
- `SphericalMap.exists_spherical_bridge` packages this.

`SphericalCompletion` proves **triangulation completion** as `SphericalMap.exists_triangulated_completion`. On a nonempty carrier, a spherical map whose vertices all have degree at least two embeds, on the same labels, in a connected spherical map whose faces are all triangles. Each step bridges two components or inserts a chord into a face of length at least four, and the number of missing vertex pairs strictly decreases. `exists_triangulated_completion_min_five` adds that minimum degree five is preserved, which lands the result in the Gate-D triangulation class. The carrier is assumed nonempty, following the math team's correction.

Composing completion with support transport, deletion and recolouring into the general four-colour argument remains open. So does Gate D.

`BreadcrumbWarning` formalises Lemma W (`not_good_of_reachable`, `card_le_deadEnd`) on an abstract finite ranked move system:
- A policy that changes its warning set only by warning a non-target state, all of whose rank-decreasing macro successors are already warned, never warns a good state.
- So the number of warnings in a run is at most the size of the dead-end region.
- `good_of_forall_descent` shows the region is empty when every non-target state has a rank-decreasing macro.

No colouring content is used. This bounds warnings by the region; it does not bound the region.

`SharedHub` formalises Lemma S as `singleton_colour_neighbour_unique`. If all faces are triangles, then for a hub h of degree at least five that is neither the deleted root r nor adjacent to it, and any colouring proper on the edges avoiding r, at most one neighbour of h has a colour used by no other neighbour.
- The link-cycle step is the existing `neighbor_rotation_adj`.
- The counting step is `two_mul_card_le_degree`: a neighbour set with no rotation-consecutive pair has at most half the neighbours.

So two-vertex Kempe toggles at a common hub cannot coexist. The lemma says nothing about toggles at different hubs, or about larger components.

`SphericalFourContact` composes support relabelling, isolation, degree-four extension and triangulation completion by induction on nonisolated support cardinality. `SphericalMassContact` defines actual proper deletion colourings, the existing mass rank, whole-component swaps including interior swaps, and endpoint-decreasing macros of at most two swaps. `four_color_of_empty_mass_region` and `four_color_of_mass_macro_descent` prove the conditional contact implication for every spherical map. Their universal degree-five hypotheses remain explicit and unproved. The empty-region and universal immediate-descent formulations are equivalent. Colourings cross completion by restriction; Kempe components do not. The experimental colour-orbit bridge, polynomial selection and complete algorithm remain open.

## Validation

`MathlibTest/PlaneMapFourColor.lean` guards theorem axiom reports and tests K4, symbolic small paths, a centre deletion retaining two disconnected edge-containing components, and certificate soundness and length. `MathlibTest/PlaneMapFiniteReachability.lean` guards actual evaluations and axiom reports, and proves concrete component/swap results with kernel `decide`. The selected component swaps while the other edge remains unchanged. All guarded theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The latest unified source audit on 4 October 2026 passed all **83** custom modules and tests. All 79 earlier audited source hashes are unchanged. The four new vacancy-slide and portfolio sources add thirteen exact guarded axiom reports within the standard three axioms. Current hashes are in `PlaneMapFourColorAudit.sha256`; GraphColour records the manifest, compiler output and hashes in `backgroundMaterial/planemap-structural/independent-inquiry/`. Earlier audits remain historical evidence. The rebuild can be repeated with:

```sh
lake env python3 scripts/rebuild-planemap-source.py
shasum -a256 -c PlaneMapFourColorAudit.sha256
```

No `sorry`, `admit`, new axiom declaration, `unsafe`, or `native_decide` occurs in these custom proof sources. The independent earlier checks still verify separation-based K6 exclusion and disconnected deletion without importing the final Five Colour theorem.

## Limits

This does **not** prove the general Four Colour Theorem. Minimum-positive-degree-five cores remain the obstruction. It does not prove that abstract 4-degenerate graphs are four-colourable, that every ordinary planar graph has the current spherical representation, that the classical elimination witness construction is executable, or that a complete solver runs in polynomial time. The icosahedron sharpness example is now checked; it does not resolve the degree-five core.

The active route and first quantified degree-five research candidate are consolidated in GraphColour's `SolvingFrameworkPlan/StructuralFourColourPlan.md` and `StructuralFourColourCandidate.md`. The Kittell replay is computational research evidence, separate from these checked Lean theorems.

`SphericalRankedContact` generalizes conditional contact to a fixed natural-number rank family, retaining actual at-most-two component swaps. A ranked-good state has a target path of at most its initial rank many macros. Bounded lexicographic scalarization and a binary primary coordinate give the conditional bound `2B+1`. No universal descent or move-search complexity is proved. `SingletonExterior.singleton_chain_two_exterior` proves that a locked singleton chain with no boundary exit forces two distinct exterior vertices; it needs neither finiteness nor a spherical hypothesis. A four-vertex path demonstrates sharpness.

`VacancySlide` proves generic vacancy properness, reverse singleton legality and restoration away from the original hole. `RankPortfolio` proves contact conditional on a graph-chosen root and rank index before every deletion colouring, plus the active-minimum lower-envelope criterion. None of these is a termination theorem for moving vacancies or a proof of the universal degree-five hypothesis.
