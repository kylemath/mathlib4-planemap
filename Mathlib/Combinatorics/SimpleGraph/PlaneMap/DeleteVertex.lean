module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FiveColor

/-!
# Vertex deletion: the graph and colouring interface

Deletion can disconnect a plane map. Each connected component has fewer
vertices, and Mathlib's component colouring API assembles their colourings.
This file does not assert that those components have generated plane-map
structures; the global induction instead uses the proved spherical carrier in
`SphericalDelete` and `FiveColorTheorem`.
-/

@[expose] public section

namespace SimpleGraph.PlaneMap

variable {n : ℕ}

/-- The induced graph obtained by removing a vertex. -/
def deleteVertexGraph (M : PlaneMap n) (x : Fin n) :
    SimpleGraph {z : Fin n // z ≠ x} := M.graph.induce {z | z ≠ x}

/-- Every connected component of a vertex-deleted graph is strictly smaller. -/
theorem delete_components_smaller (M : PlaneMap n) (x : Fin n)
    (C : (deleteVertexGraph M x).ConnectedComponent) : Nat.card C.supp < n := by
  classical
  let : Fintype C.supp := Fintype.ofFinite _
  let f : C.supp → Fin n := fun z => z.val.val
  have hf : Function.Injective f := fun a b h => Subtype.ext (Subtype.ext h)
  have hx : x ∉ Set.range f := by
    rintro ⟨z, hz⟩
    exact z.val.property hz
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Fintype.card_lt_of_injective_of_notMem f hf hx

/-- Component colourings assemble without assuming the deleted graph is connected. -/
theorem colour_delete_of_components (M : PlaneMap n) (x : Fin n) {k : ℕ}
    (h : ∀ C : (deleteVertexGraph M x).ConnectedComponent,
      C.toSimpleGraph.Colorable k) : (deleteVertexGraph M x).Colorable k :=
  colorable_iff_forall_connectedComponent.mpr h

/-- The induction step consumes colourings of all deleted components. -/
theorem five_color_of_delete_components (M : PlaneMap n) (x : Fin n)
    (hdeg : M.graph.degree x ≤ 5)
    (h : ∀ C : (deleteVertexGraph M x).ConnectedComponent,
      C.toSimpleGraph.Colorable 5) : M.graph.Colorable 5 :=
  five_color_extension x hdeg (colour_delete_of_components M x h)

end SimpleGraph.PlaneMap
