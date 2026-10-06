/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalFourContact
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.BreadcrumbWarning
public import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeBoundary

/-!
# Contact with the explicit two-swap mass hypothesis

States are proper colourings of the deleted graph, with fixed colour names.
A macro is zero, one or two actual whole-component swaps; interior components
are allowed. Its endpoint, rather than its intermediate state, must decrease
mass rank. Colour-renaming orbits are an experimental optimization, not an
assumption here. The universal root hypothesis remains unproved.
-/

@[expose] public section
namespace SimpleGraph.SphericalMap
open Classical
noncomputable section
variable {n : ℕ} (M : SphericalMap n) (r : Fin n)

abbrev DeletedVertex := {z : Fin n // z ≠ r}
abbrev DeletedGraph := M.graph.induce {z | z ≠ r}

def DeletionColouring := {c : DeletedVertex r → Fin 4 //
  Kempe.IsProperColouring (DeletedGraph M r) c}

def deletionBoundary : Finset (DeletedVertex r) :=
  Finset.univ.filter (fun z => M.Adj r z.val)

def boundaryTarget (c : DeletionColouring M r) : Prop :=
  ((deletionBoundary M r).image c.val).card ≤ 3

def deletionMassRank (c : DeletionColouring M r) : ℕ :=
  Kempe.boundaryMassRank (DeletedGraph M r) c.val (deletionBoundary M r) n

/-- One entire active bichromatic component, with no boundary-intersection restriction. -/
def ComponentStep (c d : DeletionColouring M r) : Prop :=
  ∃ (a b : Fin 4) (u : DeletedVertex r), a ≠ b ∧ c.val u = a ∧
    d.val = FiniteReachability.componentSwap (DeletedGraph M r) c.val a b u

/-- At most two swaps; the intermediate rank is unrestricted. -/
def TwoSwapMacro (c d : DeletionColouring M r) : Prop :=
  c = d ∨ ComponentStep M r c d ∨
    ∃ e, ComponentStep M r c e ∧ ComponentStep M r e d

/-- A state has a finite, endpoint-rank-decreasing macro path to a boundary target. -/
def MassGood (c : DeletionColouring M r) : Prop :=
  Breadcrumb.Good (deletionMassRank M r) (boundaryTarget M r) (TwoSwapMacro M r) c

/-- A proper deletion colouring with a three-colour boundary fills the root. -/
theorem colorable_of_boundary_target (c : DeletionColouring M r)
    (hc : boundaryTarget M r c) : M.graph.Colorable 4 := by
  have hlt : ((deletionBoundary M r).image c.val).card <
      (Finset.univ : Finset (Fin 4)).card := by
    have hh : ((deletionBoundary M r).image c.val).card ≤ 3 := hc
    simpa using (show ((deletionBoundary M r).image c.val).card < 4 by omega)
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  apply M.four_color_extend_missing r c.val c.property a
  intro z hz heq
  exact ha (Finset.mem_image.mpr ⟨z, by simp [deletionBoundary, hz], heq⟩)

/-- The model's good states provide an actual root extension. -/
theorem colorable_of_mass_good (c : DeletionColouring M r) (hc : MassGood M r c) :
    M.graph.Colorable 4 := by
  induction hc with
  | target ht => exact M.colorable_of_boundary_target r _ ht
  | descend _ _ _ ih => exact ih

/-- The exact empty-dead-end-region hypothesis. The root precedes all deletion
colourings. Neither this predicate nor its polynomial selection is proved. -/
def EmptyMassRegionHypothesis : Prop :=
  ∀ (n : ℕ) (T : SphericalMap n), 0 < n → T.graph.Connected → T.Triangulated →
    (∀ x, 5 ≤ T.graph.degree x) →
    ∃ r, T.graph.degree r = 5 ∧ ∀ c : DeletionColouring T r, MassGood T r c

/-- The universal two-swap decrease hypothesis from mass-macro descent. -/
def MassMacroDescentHypothesis : Prop :=
  ∀ (n : ℕ) (T : SphericalMap n), 0 < n → T.graph.Connected → T.Triangulated →
    (∀ x, 5 ≤ T.graph.degree x) →
    ∃ r, T.graph.degree r = 5 ∧ ∀ c : DeletionColouring T r,
      ¬ boundaryTarget T r c → ∃ d, TwoSwapMacro T r c d ∧
        deletionMassRank T r d < deletionMassRank T r c

/-- Universal descent implies an empty region by well-founded induction on rank. -/
theorem empty_mass_region_of_descent (h : MassMacroDescentHypothesis) :
    EmptyMassRegionHypothesis := by
  intro n T hn hconn htri hdeg
  obtain ⟨r, hr, hstep⟩ := h n T hn hconn htri hdeg
  exact ⟨r, hr, Breadcrumb.good_of_forall_descent hstep⟩

/-- An empty region also implies immediate descent at every non-target state.
Thus the two formulations have the same quantifiers, unlike bare Kempe reachability. -/
theorem mass_descent_of_empty_region (h : EmptyMassRegionHypothesis) :
    MassMacroDescentHypothesis := by
  intro n T hn hconn htri hdeg
  obtain ⟨r, hr, hgood⟩ := h n T hn hconn htri hdeg
  refine ⟨r, hr, ?_⟩
  intro c hct
  cases hgood c with
  | target ht => exact (hct ht).elim
  | @descend x z hm hr hz => exact ⟨z, hm, hr⟩

/-- **Contact theorem.** An empty mass region at some degree-five root of every
minimum-degree-five triangulation implies four-colourability of every spherical map. -/
theorem four_color_of_empty_mass_region (h : EmptyMassRegionHypothesis)
    (M : SphericalMap n) : M.graph.Colorable 4 := by
  apply M.four_color_of_triangulated_five_extension
  intro n T hn hconn htri hdeg
  obtain ⟨r, hr, hgood⟩ := h n T hn hconn htri hdeg
  refine ⟨r, hr, ?_⟩
  rintro ⟨c⟩
  let s : DeletionColouring T r := ⟨c, fun u v huv => c.valid huv⟩
  exact T.colorable_of_mass_good r s (hgood s)

/-- The original two-swap mass-macro claim also suffices; its premise remains explicit. -/
theorem four_color_of_mass_macro_descent (h : MassMacroDescentHypothesis)
    (M : SphericalMap n) : M.graph.Colorable 4 :=
  M.four_color_of_empty_mass_region (empty_mass_region_of_descent h)

end
end SimpleGraph.SphericalMap
