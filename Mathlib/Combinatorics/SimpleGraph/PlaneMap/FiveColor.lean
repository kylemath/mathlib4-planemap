/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FiveColorSeparation
public import Mathlib.Combinatorics.SimpleGraph.Coloring.FiveColorExtension

/-!
# Five-colour extension on a plane map

The Heawood separation theorem supplies the missing hypothesis of the
Kempe extension lemma, in one current-Mathlib compilation. The resulting
local extension theorem does not assume triangulation or separation.
Global induction still requires closure under vertex deletion.
-/

@[expose] public section

namespace SimpleGraph.PlaneMap

variable {n : ℕ} {M : PlaneMap n}

private theorem kempe_reachable_away (x : Fin n) (c : Fin n → Fin 5) (a b : Fin 5)
    {u v : {z : Fin n // z ≠ x}}
    (hu : c u.val = a ∨ c u.val = b) (hv : c v.val = a ∨ c v.val = b)
    (h : (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
      (fun z => c z.val) a b).Reachable u v) :
    (M.graph.induce {z | z ≠ x ∧ (c z = a ∨ c z = b)}).Reachable
      ⟨u.val, u.property, hu⟩ ⟨v.val, v.property, hv⟩ := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons u v w h p ih =>
    obtain ⟨q⟩ := ih h.2.2 hv
    refine ⟨.cons (v := ⟨v.val, v.property, h.2.2⟩) ?_ q⟩
    exact h.1

/-- The difficult degree-five case: distinct neighbour colours can be reduced
by a Kempe swap, using separation proved from the plane map. -/
theorem five_color_degree_five_distinct (x : Fin n) (c : Fin n → Fin 5)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (hdeg : M.graph.degree x = 5)
    (hinj : Set.InjOn c (M.graph.neighborSet x)) : M.graph.Colorable 5 := by
  classical
  obtain ⟨e, he⟩ := degree_five_neighbour_rotation x hdeg
  let v : Fin 5 → Fin n := fun i => (e i).val
  have hadj (i : Fin 5) : M.Adj x (v i) := (e i).property
  have hrot (i : Fin 5) : M.rotation.next ⟨(x, v i), hadj i⟩ =
      ⟨(x, v (i + 1)), hadj (i + 1)⟩ := he i
  have hcolors : Function.Injective (fun i => c (v i)) := by
    intro i j hij
    exact e.injective (Subtype.ext (hinj (e i).property (e j).property hij))
  have hne (i j : Fin 5) (hij : i ≠ j) : c (v i) ≠ c (v j) := hcolors.ne hij
  have hopposite :
      (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
        (fun z => c z.val) (c (v 0)) (c (v 2))).Reachable
          ⟨v 0, (hadj 0).ne.symm⟩ ⟨v 2, (hadj 2).ne.symm⟩ →
      ¬ (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
        (fun z => c z.val) (c (v 1)) (c (v 3))).Reachable
          ⟨v 1, (hadj 1).ne.symm⟩ ⟨v 3, (hadj 3).ne.symm⟩ := by
    intro h02 h13
    exact heawood_hopposite c x v hadj hrot hcolors
      (kempe_reachable_away (M := M) x c (c (v 0)) (c (v 2)) (Or.inl rfl) (Or.inr rfl) h02)
      (kempe_reachable_away (M := M) x c (c (v 1)) (c (v 3)) (Or.inl rfl) (Or.inr rfl) h13)
  obtain ⟨full, hfull⟩ := Kempe.five_color_degree_five M.graph x
    (v 0) (v 1) (v 2) (v 3) (v 4) c hproper hdeg
    (hadj 0) (hadj 1) (hadj 2) (hadj 3) (hadj 4)
    (hadj 0).ne.symm (hadj 1).ne.symm (hadj 2).ne.symm
    (hadj 3).ne.symm (hadj 4).ne.symm
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 0 4 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide))
    (hne 1 4 (by decide)) (hne 2 3 (by decide)) (hne 2 4 (by decide))
    (hne 3 4 (by decide)) hopposite
  exact ⟨Coloring.mk full (fun h => hfull _ _ h)⟩

/-- A five-colouring of the deleted graph gives a five-colouring of the whole
plane map whenever the deleted vertex has degree at most five. The resulting
colouring may recolour a Kempe component. -/
theorem five_color_extension (x : Fin n) (hdeg : M.graph.degree x ≤ 5)
    (hcolour : (M.graph.induce {z | z ≠ x}).Colorable 5) :
    M.graph.Colorable 5 := by
  classical
  obtain ⟨colour⟩ := hcolour
  let c : Fin n → Fin 5 := fun z => if hz : z = x then 0 else colour ⟨z, hz⟩
  have hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val) := by
    intro u v huv
    have hu : u.val ≠ x := u.property
    have hv : v.val ≠ x := v.property
    simpa [c, hu, hv] using colour.valid huv
  by_cases hsmall : ((M.graph.neighborFinset x).image c).card ≤ 4
  · obtain ⟨full, hfull, _⟩ := Kempe.five_color_degree_at_most_four
      M.graph x c hproper (Or.inr hsmall)
    exact ⟨Coloring.mk full (fun h => hfull _ _ h)⟩
  · have himage : ((M.graph.neighborFinset x).image c).card ≤ M.graph.degree x :=
      Finset.card_image_le
    have hfive : M.graph.degree x = 5 := by omega
    have hcard : ((M.graph.neighborFinset x).image c).card =
        (M.graph.neighborFinset x).card := by
      rw [card_neighborFinset_eq_degree]
      omega
    have hinj := Finset.injOn_of_card_image_eq hcard
    apply five_color_degree_five_distinct x c hproper hfive
    simpa only [coe_neighborFinset] using hinj

end SimpleGraph.PlaneMap
