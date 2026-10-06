/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalFiveColor

/-!
# Deductive four-colour extension at vertices of degree at most four

The deleted map may be recoloured along one bichromatic component. Alternating
components cannot both connect opposite neighbours, by spherical separation.
-/

@[expose] public section

namespace SimpleGraph.SphericalMap

variable {n : ℕ} {M : SphericalMap n}

/-- Degree four supplies a cyclic enumeration of all four neighbours, without
assuming that the map is a triangulation. -/
theorem degree_four_neighbour_rotation (x : Fin n) (hdeg : M.graph.degree x = 4) :
    ∃ e : Fin 4 ≃ M.graph.neighborSet x, ∀ i : Fin 4,
      M.rotation.next (M.graph.dartOfNeighborSet x (e i)) =
        M.graph.dartOfNeighborSet x (e (i + 1)) := by
  classical
  have hn : Nonempty (M.graph.neighborSet x) := by
    apply Fintype.card_pos_iff.1
    rw [card_neighborSet_eq_degree, hdeg]
    decide
  obtain ⟨w⟩ := hn
  let σ := M.rotation.neighborRotation x
  let P := Function.minimalPeriod (⇑σ) w
  have hP : P = 4 := (M.rotation.neighbor_period_eq_degree x w).trans hdeg
  let e : Fin 4 ≃ M.graph.neighborSet x :=
    (finCongr hP.symm).trans (M.rotation.neighborOrbitEquiv x w)
  have he (i : Fin 4) : e i = (⇑σ)^[i.val] w := rfl
  have hnext (i : Fin 4) : σ (e i) = e (i + 1) := by
    rw [he, he]
    have hm : (i.val + 1) % 4 = (i.val + 1) % P := by rw [hP]
    simp only [Fin.val_add, Fin.val_one]
    rw [hm]
    exact (Function.iterate_mod_minimalPeriod_eq.trans
      (Function.iterate_succ_apply' _ _ _)).symm
  refine ⟨e, fun i => ?_⟩
  rw [← M.rotation.neighbor_rotation_dart, hnext]

/-- Heawood separation for two pairs of differently coloured neighbours.
The reachability relations are in the actual bichromatic induced subgraphs of
`M.graph` with the centre deleted. Properness is not needed for separation. -/
theorem four_colour_hopposite {α : Type*} (c : Fin n → α) (x : Fin n)
    (v : Fin 4 → Fin n) (hadj : ∀ i, M.Adj x (v i))
    (hrot : ∀ i : Fin 4,
      M.rotation.next ⟨(x, v i), hadj i⟩ = ⟨(x, v (i + 1)), hadj (i + 1)⟩)
    (hcolors : Function.Injective (fun i => c (v i))) :
    let B := fun i j : Fin 4 =>
      M.graph.induce {z | z ≠ x ∧ (c z = c (v i) ∨ c z = c (v j))}
    (B 0 2).Reachable ⟨v 0, (hadj 0).ne.symm, Or.inl rfl⟩
      ⟨v 2, (hadj 2).ne.symm, Or.inr rfl⟩ →
    ¬ (B 1 3).Reachable ⟨v 1, (hadj 1).ne.symm, Or.inl rfl⟩
      ⟨v 3, (hadj 3).ne.symm, Or.inr rfl⟩ := by
  dsimp only
  rintro ⟨p⟩ ⟨q⟩
  let p' := p.map (Embedding.induce _).toHom
  let q' := q.map (Embedding.induce _).toHom
  have hp' : ∀ z ∈ p'.support, z ≠ x ∧ (c z = c (v 0) ∨ c z = c (v 2)) := by
    intro z hz
    simp only [p', Walk.support_map, List.mem_map] at hz
    obtain ⟨a, _, ha⟩ := hz
    change a.val = z at ha
    exact ha ▸ a.property
  have hq' : ∀ z ∈ q'.support, z ≠ x ∧ (c z = c (v 1) ∨ c z = c (v 3)) := by
    intro z hz
    simp only [q', Walk.support_map, List.mem_map] at hz
    obtain ⟨a, _, ha⟩ := hz
    change a.val = z at ha
    exact ha ▸ a.property
  have hv02 : v 0 ≠ v 2 := by
    intro hh
    have := hcolors (congrArg c hh)
    norm_num at this
  obtain ⟨z, hpz, hqz⟩ := alternating_walks_intersect
    (hadj 0) (hadj 1) (hadj 2) (hadj 3) hv02
    (by simpa using hrot 1) (by simpa using hrot 2)
    p' (fun hh => (hp' x hh).1 rfl) q' (fun hh => (hq' x hh).1 rfl)
  rcases (hp' z hpz).2 with h0 | h2 <;>
    rcases (hq' z hqz).2 with h1 | h3
  · have := hcolors (h0.symm.trans h1); norm_num at this
  · have := hcolors (h0.symm.trans h3); norm_num at this
  · have := hcolors (h2.symm.trans h1); norm_num at this
  · have := hcolors (h2.symm.trans h3); norm_num at this

private theorem kempe_reachable_away (x : Fin n) (c : Fin n → Fin 4) (a b : Fin 4)
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


/-- A missing neighbour colour can be assigned to the deleted vertex. -/
def fourColorExtendMissing (x : Fin n) (c : {z : Fin n // z ≠ x} → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x}) c)
    (a : Fin 4) (hmissing : ∀ z, M.Adj x z.val → c z ≠ a) :
    M.graph.Coloring (Fin 4) := by
  let full : Fin n → Fin 4 := fun z => if hz : z = x then a else c ⟨z, hz⟩
  refine Coloring.mk full ?_
  intro u v huv
  by_cases hu : u = x
  · subst u
    have hv := huv.ne.symm
    simpa [full, hv] using (hmissing ⟨v, hv⟩ huv).symm
  · by_cases hv : v = x
    · subst v
      simpa [full, hu] using hmissing ⟨u, hu⟩ huv.symm
    · simpa [full, hu, hv] using hproper ⟨u, hu⟩ ⟨v, hv⟩ huv

/-- The explicit missing-colour construction gives four-colourability. -/
theorem four_color_extend_missing (x : Fin n) (c : {z : Fin n // z ≠ x} → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x}) c)
    (a : Fin 4) (hmissing : ∀ z, M.Adj x z.val → c z ≠ a) :
    M.graph.Colorable 4 :=
  ⟨fourColorExtendMissing x c hproper a hmissing⟩

/-- An explicitly supplied finite bichromatic component gives an executable
Kempe recolouring and vertex extension. The component search is separate. -/
def fourColorSwapSet (x : Fin n) (c : Fin n → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (e : Fin 4 ≃ M.graph.neighborSet x)
    (hinj : Function.Injective (fun i => c (e i).val))
    (i j : Fin 4) (hij : i ≠ j)
    (S : Finset {z : Fin n // z ≠ x})
    (hS_ab : ∀ z ∈ S, c z.val = c (e i).val ∨ c z.val = c (e j).val)
    (hS_closed : ∀ u v : {z : Fin n // z ≠ x}, M.Adj u.val v.val →
      u ∈ S → (c v.val = c (e i).val ∨ c v.val = c (e j).val) → v ∈ S)
    (hiS : (⟨(e i).val, (e i).property.ne.symm⟩ : {z : Fin n // z ≠ x}) ∈ S)
    (hjS : (⟨(e j).val, (e j).property.ne.symm⟩ : {z : Fin n // z ≠ x}) ∉ S) :
    M.graph.Coloring (Fin 4) := by
  let H := M.graph.induce {z | z ≠ x}
  let cH : {z : Fin n // z ≠ x} → Fin 4 := fun z => c z.val
  let ui : {z : Fin n // z ≠ x} := ⟨(e i).val, (e i).property.ne.symm⟩
  let uj : {z : Fin n // z ≠ x} := ⟨(e j).val, (e j).property.ne.symm⟩
  let swapped := Kempe.kempeSwap cH (↑S) (c (e i).val) (c (e j).val)
  have hcols := hinj.ne hij
  have hproper' : Kempe.IsProperColouring H swapped :=
    Kempe.kempeSwap_preserves_proper H cH _ _ hcols (S : Set {z : Fin n // z ≠ x})
      hS_ab hS_closed hproper
  apply fourColorExtendMissing x swapped hproper' (c (e i).val)
  intro z hz
  obtain ⟨k, hk⟩ := e.surjective ⟨z.val, hz⟩
  have hzval : (e k).val = z.val := congrArg Subtype.val hk
  by_cases hki : k = i
  · subst k
    have hzu : z = ui := Subtype.ext hzval.symm
    rw [hzu]
    have hflip : swapped ui = c (e j).val :=
      Kempe.kempeSwap_flips_a cH (↑S) _ _ ui hiS rfl
    rw [hflip]
    exact hcols.symm
  · by_cases hkj : k = j
    · subst k
      have hzu : z = uj := Subtype.ext hzval.symm
      rw [hzu]
      have hout : uj ∉ (↑S : Set {z : Fin n // z ≠ x}) := hjS
      have hstay : swapped uj = cH uj := Kempe.kempeSwap_outside cH (↑S) _ _ uj hout
      rw [hstay]
      exact hcols.symm
    · have hci : cH z ≠ c (e i).val := by
        change c z.val ≠ c (e i).val
        rw [← hzval]
        exact hinj.ne hki
      have hcj : cH z ≠ c (e j).val := by
        change c z.val ≠ c (e j).val
        rw [← hzval]
        exact hinj.ne hkj
      have hstay : swapped z = cH z :=
        Kempe.kempeSwap_preserves_other cH (↑S) _ _ z hci hcj
      rw [hstay]
      exact hci

/-- A separated pair of uniquely coloured neighbours frees one colour by one
Kempe swap. The enumeration includes every neighbour. -/
theorem four_color_swap_pair (x : Fin n) (c : Fin n → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (e : Fin 4 ≃ M.graph.neighborSet x)
    (hinj : Function.Injective (fun i => c (e i).val))
    (i j : Fin 4) (hij : i ≠ j)
    (hsep : ¬ (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
      (fun z => c z.val) (c (e i).val) (c (e j).val)).Reachable
        ⟨(e i).val, (e i).property.ne.symm⟩
        ⟨(e j).val, (e j).property.ne.symm⟩) :
    M.graph.Colorable 4 := by
  classical
  let H := M.graph.induce {z | z ≠ x}
  let cH : {z : Fin n // z ≠ x} → Fin 4 := fun z => c z.val
  let ui : {z : Fin n // z ≠ x} := ⟨(e i).val, (e i).property.ne.symm⟩
  let uj : {z : Fin n // z ≠ x} := ⟨(e j).val, (e j).property.ne.symm⟩
  let S := Kempe.kempeChain H cH (c (e i).val) (c (e j).val) ui
  let swapped := Kempe.kempeSwap cH S (c (e i).val) (c (e j).val)
  have hcols := hinj.ne hij
  have hproper' : Kempe.IsProperColouring H swapped :=
    Kempe.kempeSwap_chain_proper H cH _ _ hcols ui rfl hproper
  apply four_color_extend_missing x swapped hproper' (c (e i).val)
  intro z hz
  obtain ⟨k, hk⟩ := e.surjective ⟨z.val, hz⟩
  have hzval : (e k).val = z.val := congrArg Subtype.val hk
  by_cases hki : k = i
  · subst k
    have hzu : z = ui := Subtype.ext hzval.symm
    rw [hzu]
    have hflip : swapped ui = c (e j).val :=
      Kempe.kempeSwap_flips_a cH S _ _ ui
        (Kempe.mem_kempeChain_self H cH _ _ ui) rfl
    rw [hflip]
    exact hcols.symm
  · by_cases hkj : k = j
    · subst k
      have hzu : z = uj := Subtype.ext hzval.symm
      rw [hzu]
      have hout : uj ∉ S := hsep
      have hstay : swapped uj = cH uj := Kempe.kempeSwap_outside cH S _ _ uj hout
      rw [hstay]
      exact hcols.symm
    · have hci : cH z ≠ c (e i).val := by
        change c z.val ≠ c (e i).val
        rw [← hzval]
        exact hinj.ne hki
      have hcj : cH z ≠ c (e j).val := by
        change c z.val ≠ c (e j).val
        rw [← hzval]
        exact hinj.ne hkj
      have hstay : swapped z = cH z :=
        Kempe.kempeSwap_preserves_other cH S _ _ z hci hcj
      rw [hstay]
      exact hci

/-- Distinct colours at a degree-four vertex can be reduced by a single Kempe
swap. Spherical separation supplies the required disconnected pair. -/
theorem four_color_degree_four_distinct (x : Fin n) (c : Fin n → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (hdeg : M.graph.degree x = 4)
    (hinj : Set.InjOn c (M.graph.neighborSet x)) : M.graph.Colorable 4 := by
  classical
  obtain ⟨e, he⟩ := degree_four_neighbour_rotation x hdeg
  let v : Fin 4 → Fin n := fun i => (e i).val
  have hadj (i : Fin 4) : M.Adj x (v i) := (e i).property
  have hrot (i : Fin 4) : M.rotation.next ⟨(x, v i), hadj i⟩ =
      ⟨(x, v (i + 1)), hadj (i + 1)⟩ := he i
  have hcolors : Function.Injective (fun i => c (v i)) := by
    intro i j hij
    exact e.injective (Subtype.ext (hinj (e i).property (e j).property hij))
  by_cases h02 : (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
      (fun z => c z.val) (c (v 0)) (c (v 2))).Reachable
        ⟨v 0, (hadj 0).ne.symm⟩ ⟨v 2, (hadj 2).ne.symm⟩
  · have h13 : ¬ (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
        (fun z => c z.val) (c (v 1)) (c (v 3))).Reachable
          ⟨v 1, (hadj 1).ne.symm⟩ ⟨v 3, (hadj 3).ne.symm⟩ := by
      intro h
      exact four_colour_hopposite c x v hadj hrot hcolors
        (kempe_reachable_away (M := M) x c (c (v 0)) (c (v 2)) (Or.inl rfl) (Or.inr rfl) h02)
        (kempe_reachable_away (M := M) x c (c (v 1)) (c (v 3)) (Or.inl rfl) (Or.inr rfl) h)
    exact four_color_swap_pair x c hproper e hcolors 1 3 (by decide) h13
  · exact four_color_swap_pair x c hproper e hcolors 0 2 (by decide) h02

/-- Every four-colouring after deleting a degree-at-most-four vertex can be
extended, allowing a Kempe recolouring of the deleted graph. -/
theorem four_color_extension (x : Fin n) (hdeg : M.graph.degree x ≤ 4)
    (hcolour : (M.graph.induce {z | z ≠ x}).Colorable 4) :
    M.graph.Colorable 4 := by
  classical
  obtain ⟨colour⟩ := hcolour
  let c : Fin n → Fin 4 := fun z => if hz : z = x then 0 else colour ⟨z, hz⟩
  have hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val) := by
    intro u v huv
    have hu : u.val ≠ x := u.property
    have hv : v.val ≠ x := v.property
    simpa [c, hu, hv] using colour.valid huv
  by_cases hsmall : ((M.graph.neighborFinset x).image c).card ≤ 3
  · have hlt : ((M.graph.neighborFinset x).image c).card <
        (Finset.univ : Finset (Fin 4)).card := by simpa using (show _ < 4 by omega)
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    apply four_color_extend_missing x (fun z => c z.val) hproper a
    intro z hz heq
    exact ha (Finset.mem_image.mpr ⟨z.val, (by simpa [mem_neighborFinset] using hz), heq⟩)
  · have himage : ((M.graph.neighborFinset x).image c).card ≤ M.graph.degree x :=
      Finset.card_image_le
    have hfour : M.graph.degree x = 4 := by omega
    have hcard : ((M.graph.neighborFinset x).image c).card =
        (M.graph.neighborFinset x).card := by
      rw [card_neighborFinset_eq_degree]
      omega
    have hinj := Finset.injOn_of_card_image_eq hcard
    apply four_color_degree_four_distinct x c hproper hfour
    simpa only [coe_neighborFinset] using hinj

end SimpleGraph.SphericalMap
