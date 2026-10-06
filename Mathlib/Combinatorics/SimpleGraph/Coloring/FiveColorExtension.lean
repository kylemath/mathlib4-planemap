/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Kempe

/-!
# The graph-theoretic degree-five extension

Port of GraphColour's FiveColorDeg5 to current Mathlib. Separation is an
explicit hypothesis here; PlaneMap discharges it in its application module.
-/

@[expose] public section
namespace SimpleGraph.Kempe

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

private lemma five_named_neighbours
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x v0 v1 v2 v3 v4 : V)
    (hdeg : G.degree x = 5)
    (hadj0 : G.Adj x v0) (hadj1 : G.Adj x v1)
    (hadj2 : G.Adj x v2) (hadj3 : G.Adj x v3) (hadj4 : G.Adj x v4)
    (hc01 : v0 ≠ v1) (hc02 : v0 ≠ v2) (hc03 : v0 ≠ v3) (hc04 : v0 ≠ v4)
    (hc12 : v1 ≠ v2) (hc13 : v1 ≠ v3) (hc14 : v1 ≠ v4)
    (hc23 : v2 ≠ v3) (hc24 : v2 ≠ v4) (hc34 : v3 ≠ v4) :
    G.neighborFinset x = {v0, v1, v2, v3, v4} := by
  let s : Finset V := {v0, v1, v2, v3, v4}
  have hs : s.card = 5 := by
    simp [s, hc01, hc02, hc03, hc04, hc12, hc13, hc14, hc23, hc24, hc34]
  have hsub : s ⊆ G.neighborFinset x := by
    intro v hv
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · simpa [mem_neighborFinset] using hadj0
    · simpa [mem_neighborFinset] using hadj1
    · simpa [mem_neighborFinset] using hadj2
    · simpa [mem_neighborFinset] using hadj3
    · simpa [mem_neighborFinset] using hadj4
  have hcard : (G.neighborFinset x).card ≤ s.card := by
    rw [card_neighborFinset_eq_degree, hdeg, hs]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- If the `(c v0,c v2)`-chain in `G - x` separates `v0` from `v2`, swapping
the component of `v0` preserves properness, frees `c v0` on `N(x)`, and
extends to a proper five-colouring of `G`. -/
theorem five_color_degree_five_swap
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x v0 v1 v2 v3 v4 : V) (c : V → Fin 5)
    (hproper : IsProperColouring (G.induce {v | v ≠ x})
      (fun y : {v : V // v ≠ x} => c y.val))
    (hdeg : G.degree x = 5)
    (hadj0 : G.Adj x v0) (hadj1 : G.Adj x v1)
    (hadj2 : G.Adj x v2) (hadj3 : G.Adj x v3) (hadj4 : G.Adj x v4)
    (hv0x : v0 ≠ x) (hv1x : v1 ≠ x) (hv2x : v2 ≠ x)
    (hv3x : v3 ≠ x) (hv4x : v4 ≠ x)
    (hc01 : c v0 ≠ c v1) (hc02 : c v0 ≠ c v2)
    (hc03 : c v0 ≠ c v3) (hc04 : c v0 ≠ c v4)
    (hc12 : c v1 ≠ c v2) (hc13 : c v1 ≠ c v3)
    (hc14 : c v1 ≠ c v4) (hc23 : c v2 ≠ c v3)
    (hc24 : c v2 ≠ c v4) (hc34 : c v3 ≠ c v4)
    (hsep : ¬ (bichromaticSubgraph (G.induce {v | v ≠ x})
      (fun y : {v : V // v ≠ x} => c y.val) (c v0) (c v2)).Reachable
        ⟨v0, hv0x⟩ ⟨v2, hv2x⟩) :
    let H := G.induce {v | v ≠ x}
    let cH : {v : V // v ≠ x} → Fin 5 := fun y => c y.val
    let u0 : {v : V // v ≠ x} := ⟨v0, hv0x⟩
    let swapped := kempeSwap cH (kempeChain H cH (c v0) (c v2) u0)
      (c v0) (c v2)
    IsProperColouring H swapped ∧
      swapped u0 = c v2 ∧
      (∀ w : {v : V // v ≠ x}, G.Adj x w.val → swapped w ≠ c v0) ∧
      ∃ full : V → Fin 5, IsProperColouring G full := by
  dsimp only
  let H := G.induce {v | v ≠ x}
  let cH : {v : V // v ≠ x} → Fin 5 := fun y => c y.val
  let u0 : {v : V // v ≠ x} := ⟨v0, hv0x⟩
  let u2 : {v : V // v ≠ x} := ⟨v2, hv2x⟩
  let swapped := kempeSwap cH (kempeChain H cH (c v0) (c v2) u0)
    (c v0) (c v2)
  have hv01 : v0 ≠ v1 := fun h => hc01 (congrArg c h)
  have hv02 : v0 ≠ v2 := fun h => hc02 (congrArg c h)
  have hv03 : v0 ≠ v3 := fun h => hc03 (congrArg c h)
  have hv04 : v0 ≠ v4 := fun h => hc04 (congrArg c h)
  have hv12 : v1 ≠ v2 := fun h => hc12 (congrArg c h)
  have hv13 : v1 ≠ v3 := fun h => hc13 (congrArg c h)
  have hv14 : v1 ≠ v4 := fun h => hc14 (congrArg c h)
  have hv23 : v2 ≠ v3 := fun h => hc23 (congrArg c h)
  have hv24 : v2 ≠ v4 := fun h => hc24 (congrArg c h)
  have hv34 : v3 ≠ v4 := fun h => hc34 (congrArg c h)
  have hneighbors : G.neighborFinset x = {v0, v1, v2, v3, v4} :=
    five_named_neighbours G x v0 v1 v2 v3 v4 hdeg
      hadj0 hadj1 hadj2 hadj3 hadj4
      hv01 hv02 hv03 hv04 hv12 hv13 hv14 hv23 hv24 hv34
  have hproper' : IsProperColouring H swapped := by
    exact kempeSwap_chain_proper H cH (c v0) (c v2) hc02 u0 rfl hproper
  have hflip : swapped u0 = c v2 := by
    exact kempeSwap_flips_a cH (kempeChain H cH (c v0) (c v2) u0)
      (c v0) (c v2) u0 (mem_kempeChain_self H cH (c v0) (c v2) u0) rfl
  have hmissing :
      ∀ w : {v : V // v ≠ x}, G.Adj x w.val → swapped w ≠ c v0 := by
    intro w hw
    have hwmem : w.val ∈ ({v0, v1, v2, v3, v4} : Finset V) := by
      rw [← hneighbors, mem_neighborFinset]
      exact hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwmem
    rcases hwmem with hw0 | hw1 | hw2 | hw3 | hw4
    · have hwu : w = u0 := by
        apply Subtype.ext
        exact hw0
      rw [hwu, hflip]
      exact hc02.symm
    · have hstay := kempeSwap_preserves_other cH
        (kempeChain H cH (c v0) (c v2) u0) (c v0) (c v2) w
        (by simpa [cH, hw1] using hc01.symm)
        (by simpa [cH, hw1] using hc12)
      have hstay' : swapped w = cH w := by simpa [swapped] using hstay
      rw [hstay']
      simpa [cH, hw1] using hc01.symm
    · have hout : u2 ∉ kempeChain H cH (c v0) (c v2) u0 := by
        exact hsep
      have hstay := kempeSwap_outside cH
        (kempeChain H cH (c v0) (c v2) u0) (c v0) (c v2) u2 hout
      have hwu : w = u2 := by
        apply Subtype.ext
        exact hw2
      have hstay' : swapped u2 = cH u2 := by simpa [swapped] using hstay
      rw [hwu, hstay']
      exact hc02.symm
    · have hstay := kempeSwap_preserves_other cH
        (kempeChain H cH (c v0) (c v2) u0) (c v0) (c v2) w
        (by simpa [cH, hw3] using hc03.symm)
        (by simpa [cH, hw3] using hc23.symm)
      have hstay' : swapped w = cH w := by simpa [swapped] using hstay
      rw [hstay']
      simpa [cH, hw3] using hc03.symm
    · have hstay := kempeSwap_preserves_other cH
        (kempeChain H cH (c v0) (c v2) u0) (c v0) (c v2) w
        (by simpa [cH, hw4] using hc04.symm)
        (by simpa [cH, hw4] using hc24.symm)
      have hstay' : swapped w = cH w := by simpa [swapped] using hstay
      rw [hstay']
      simpa [cH, hw4] using hc04.symm
  let lifted : V → Fin 5 := fun y =>
    if hy : y = x then 0 else swapped ⟨y, hy⟩
  have hlifted_missing :
      ∀ y ∈ G.neighborFinset x, lifted y ≠ c v0 := by
    intro y hy
    have hadj : G.Adj x y := by simpa [mem_neighborFinset] using hy
    have hyx : y ≠ x := fun h => G.ne_of_adj hadj h.symm
    simpa [lifted, hyx] using hmissing ⟨y, hyx⟩ hadj
  have himage :
      ((G.neighborFinset x).image lifted).card ≤ 4 := by
    have hsub :
        (G.neighborFinset x).image lifted ⊆
          (Finset.univ : Finset (Fin 5)).erase (c v0) := by
      intro col hcol
      rcases Finset.mem_image.mp hcol with ⟨y, hy, rfl⟩
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact hlifted_missing y hy
    calc
      ((G.neighborFinset x).image lifted).card
          ≤ ((Finset.univ : Finset (Fin 5)).erase (c v0)).card :=
        Finset.card_le_card hsub
      _ = 4 := by simp
  have hbound : G.degree x ≤ 4 ∨
      ((G.neighborFinset x).image fun y =>
        if h : y = x then (0 : Fin 5) else swapped ⟨y, h⟩).card ≤ 4 := by
    right
    simpa [lifted] using himage
  obtain ⟨full, hfull, _⟩ :=
    five_color_degree_at_most_four_subtype G x swapped hproper' hbound
  exact ⟨hproper', hflip, hmissing, full, hfull⟩

/-- The same degree-five step for the opposite pair `(v1,v3)`. -/
theorem five_color_degree_five_separated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x v0 v1 v2 v3 v4 : V) (c : V → Fin 5)
    (hproper : IsProperColouring (G.induce {v | v ≠ x})
      (fun y : {v : V // v ≠ x} => c y.val))
    (hdeg : G.degree x = 5)
    (hadj0 : G.Adj x v0) (hadj1 : G.Adj x v1)
    (hadj2 : G.Adj x v2) (hadj3 : G.Adj x v3) (hadj4 : G.Adj x v4)
    (hv0x : v0 ≠ x) (hv1x : v1 ≠ x) (hv2x : v2 ≠ x)
    (hv3x : v3 ≠ x) (hv4x : v4 ≠ x)
    (hc01 : c v0 ≠ c v1) (hc02 : c v0 ≠ c v2)
    (hc03 : c v0 ≠ c v3) (hc04 : c v0 ≠ c v4)
    (hc12 : c v1 ≠ c v2) (hc13 : c v1 ≠ c v3)
    (hc14 : c v1 ≠ c v4) (hc23 : c v2 ≠ c v3)
    (hc24 : c v2 ≠ c v4) (hc34 : c v3 ≠ c v4)
    (hsep : ¬ (bichromaticSubgraph (G.induce {v | v ≠ x})
      (fun y : {v : V // v ≠ x} => c y.val) (c v1) (c v3)).Reachable
        ⟨v1, hv1x⟩ ⟨v3, hv3x⟩) :
    let H := G.induce {v | v ≠ x}
    let cH : {v : V // v ≠ x} → Fin 5 := fun y => c y.val
    let u1 : {v : V // v ≠ x} := ⟨v1, hv1x⟩
    let swapped := kempeSwap cH (kempeChain H cH (c v1) (c v3) u1)
      (c v1) (c v3)
    IsProperColouring H swapped ∧
      swapped u1 = c v3 ∧
      (∀ w : {v : V // v ≠ x}, G.Adj x w.val → swapped w ≠ c v1) ∧
      ∃ full : V → Fin 5, IsProperColouring G full := by
  simpa using five_color_degree_five_swap G x v1 v0 v3 v2 v4 c hproper hdeg
    hadj1 hadj0 hadj3 hadj2 hadj4
    hv1x hv0x hv3x hv2x hv4x
    hc01.symm hc13 hc12 hc14 hc03 hc02 hc04 hc23.symm hc34 hc24 hsep

/-- Under the topological opposite-pair implication, the degree-five case
extends to a proper five-colouring by one Kempe swap. -/
theorem five_color_degree_five
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x v0 v1 v2 v3 v4 : V) (c : V → Fin 5)
    (hproper : IsProperColouring (G.induce {v | v ≠ x})
      (fun y : {v : V // v ≠ x} => c y.val))
    (hdeg : G.degree x = 5)
    (hadj0 : G.Adj x v0) (hadj1 : G.Adj x v1)
    (hadj2 : G.Adj x v2) (hadj3 : G.Adj x v3) (hadj4 : G.Adj x v4)
    (hv0x : v0 ≠ x) (hv1x : v1 ≠ x) (hv2x : v2 ≠ x)
    (hv3x : v3 ≠ x) (hv4x : v4 ≠ x)
    (hc01 : c v0 ≠ c v1) (hc02 : c v0 ≠ c v2)
    (hc03 : c v0 ≠ c v3) (hc04 : c v0 ≠ c v4)
    (hc12 : c v1 ≠ c v2) (hc13 : c v1 ≠ c v3)
    (hc14 : c v1 ≠ c v4) (hc23 : c v2 ≠ c v3)
    (hc24 : c v2 ≠ c v4) (hc34 : c v3 ≠ c v4)
    (hopposite :
      (bichromaticSubgraph (G.induce {v | v ≠ x})
        (fun y : {v : V // v ≠ x} => c y.val) (c v0) (c v2)).Reachable
          ⟨v0, hv0x⟩ ⟨v2, hv2x⟩ →
      ¬ (bichromaticSubgraph (G.induce {v | v ≠ x})
        (fun y : {v : V // v ≠ x} => c y.val) (c v1) (c v3)).Reachable
          ⟨v1, hv1x⟩ ⟨v3, hv3x⟩) :
    ∃ full : V → Fin 5, IsProperColouring G full := by
  by_cases h02 : (bichromaticSubgraph (G.induce {v | v ≠ x})
      (fun y : {v : V // v ≠ x} => c y.val) (c v0) (c v2)).Reachable
        ⟨v0, hv0x⟩ ⟨v2, hv2x⟩
  · exact (five_color_degree_five_separated G x v0 v1 v2 v3 v4 c
      hproper hdeg hadj0 hadj1 hadj2 hadj3 hadj4
      hv0x hv1x hv2x hv3x hv4x
      hc01 hc02 hc03 hc04 hc12 hc13 hc14 hc23 hc24 hc34
      (hopposite h02)).2.2.2
  · exact (five_color_degree_five_swap G x v0 v1 v2 v3 v4 c
      hproper hdeg hadj0 hadj1 hadj2 hadj3 hadj4
      hv0x hv1x hv2x hv3x hv4x
      hc01 hc02 hc03 hc04 hc12 hc13 hc14 hc23 hc24 hc34 h02).2.2.2

end

end SimpleGraph.Kempe
