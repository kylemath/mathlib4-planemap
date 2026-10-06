/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Kempe
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Boundary-weighted Kempe component mass

The mass counts each active bichromatic component meeting a prescribed boundary
once, with weight the square of its number of vertices outside that boundary.
No planarity, properness, or component-closure assumption is needed for locality.
-/

@[expose] public section
namespace SimpleGraph.Kempe

variable {V : Type*} {k : ℕ}

/-- Swapping two colours on any set preserves membership in their union. -/
lemma kempeSwap_mem_pair_iff (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b : Fin k) (v : V) :
    (kempeSwap c S a b v = a ∨ kempeSwap c S a b v = b) ↔
      (c v = a ∨ c v = b) := by
  by_cases hv : v ∈ S <;> by_cases ha : c v = a <;> by_cases hb : c v = b <;>
    simp [kempeSwap, hv, ha, hb]

/-- Colours disjoint from the swapped pair have exactly the same fibres. -/
lemma kempeSwap_mass_eq_other_iff (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b e : Fin k) (ha : e ≠ a) (hb : e ≠ b) (v : V) :
    kempeSwap c S a b v = e ↔ c v = e := by
  by_cases hv : v ∈ S <;> by_cases hca : c v = a <;> by_cases hcb : c v = b <;>
    simp [kempeSwap, hv, hca, hcb, Ne.symm ha, Ne.symm hb]
  split <;> simp_all
  exact Ne.symm ha

/-- The entire bichromatic graph of the swapped pair is unchanged. -/
theorem bichromaticSubgraph_swap_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (S : Set V) [DecidablePred (· ∈ S)] (a b : Fin k) :
    bichromaticSubgraph G (kempeSwap c S a b) a b = bichromaticSubgraph G c a b := by
  ext u v
  simp only [bichromaticSubgraph, bichromaticAdj, kempeSwap_mem_pair_iff]

/-- The bichromatic graph of any disjoint pair is unchanged. -/
theorem bichromaticSubgraph_swap_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (S : Set V) [DecidablePred (· ∈ S)] (a b d e : Fin k)
    (hda : d ≠ a) (hdb : d ≠ b) (hea : e ≠ a) (heb : e ≠ b) :
    bichromaticSubgraph G (kempeSwap c S a b) d e = bichromaticSubgraph G c d e := by
  ext u v
  simp only [bichromaticSubgraph, bichromaticAdj,
    kempeSwap_mass_eq_other_iff c S a b d hda hdb,
    kempeSwap_mass_eq_other_iff c S a b e hea heb]

variable [Fintype V] [DecidableEq V]

/-- Vertices in the reachable component of `v` in the bichromatic graph.
Inactive isolated vertices are excluded by `boundaryPairComponents` below. -/
noncomputable def pairComponent (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => (bichromaticSubgraph G c a b).Reachable v w

/-- Distinct active bichromatic components that intersect the boundary.
Taking an image removes repeated representatives of the same component. -/
noncomputable def boundaryPairComponents (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (a b : Fin k) : Finset (Finset V) := by
  classical
  exact (B.filter fun v => c v = a ∨ c v = b).image (pairComponent G c a b)

/-- Sum of squared exterior component sizes, counting each boundary component once. -/
noncomputable def pairMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (a b : Fin k) : ℕ :=
  ∑ K ∈ boundaryPairComponents G c B a b, (K \ B).card ^ 2

/-- Boundary mass of the swapped pair is unchanged, even for an arbitrary swap set. -/
theorem pairMass_swap_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (S : Set V) [DecidablePred (· ∈ S)]
    (a b : Fin k) :
    pairMass G (kempeSwap c S a b) B a b = pairMass G c B a b := by
  classical
  have hc : pairComponent G (kempeSwap c S a b) a b = pairComponent G c a b := by
    funext v
    unfold pairComponent
    rw [bichromaticSubgraph_swap_pair]
  simp only [pairMass, boundaryPairComponents, kempeSwap_mem_pair_iff, hc]

/-- Boundary mass of a disjoint pair is unchanged. -/
theorem pairMass_swap_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (S : Set V) [DecidablePred (· ∈ S)]
    (a b d e : Fin k) (hda : d ≠ a) (hdb : d ≠ b) (hea : e ≠ a) (heb : e ≠ b) :
    pairMass G (kempeSwap c S a b) B d e = pairMass G c B d e := by
  classical
  have hc : pairComponent G (kempeSwap c S a b) d e = pairComponent G c d e := by
    funext v
    unfold pairComponent
    rw [bichromaticSubgraph_swap_disjoint G c S a b d e hda hdb hea heb]
  simp only [pairMass, boundaryPairComponents,
    kempeSwap_mass_eq_other_iff c S a b d hda hdb,
    kempeSwap_mass_eq_other_iff c S a b e hea heb, hc]

/-- The six pair masses associated with four named colours.
For four distinct colours these are precisely the six unordered colour pairs. -/
noncomputable def fourColorMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (a b d e : Fin k) : ℕ :=
  pairMass G c B a b + pairMass G c B d e +
    pairMass G c B a d + pairMass G c B a e +
    pairMass G c B b d + pairMass G c B b e

/-- WP7 Lemma 7.1: only the four mixed terms contribute to the integer change.
Casting before subtraction avoids truncated natural subtraction. -/
theorem fourColorMass_swap_change (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (S : Set V) [DecidablePred (· ∈ S)]
    (a b d e : Fin k) (hda : d ≠ a) (hdb : d ≠ b) (hea : e ≠ a) (heb : e ≠ b) :
    (fourColorMass G (kempeSwap c S a b) B a b d e : ℤ) -
      (fourColorMass G c B a b d e : ℤ) =
    ((pairMass G (kempeSwap c S a b) B a d : ℤ) - (pairMass G c B a d : ℤ)) +
    ((pairMass G (kempeSwap c S a b) B a e : ℤ) - (pairMass G c B a e : ℤ)) +
    ((pairMass G (kempeSwap c S a b) B b d : ℤ) - (pairMass G c B b d : ℤ)) +
    ((pairMass G (kempeSwap c S a b) B b e : ℤ) - (pairMass G c B b e : ℤ)) := by
  simp only [fourColorMass, Nat.cast_add, pairMass_swap_pair,
    pairMass_swap_disjoint G c B S a b d e hda hdb hea heb]
  ring

/-- All six masses for the four-colour palette. -/
noncomputable def sixPairMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 4) (B : Finset V) : ℕ := fourColorMass G c B 0 1 2 3

/-- Four-colour instance of WP7 locality, for exchanging colours zero and one. -/
theorem sixPairMass_swap_zero_one_change (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 4) (B : Finset V) (S : Set V) [DecidablePred (· ∈ S)] :
    (sixPairMass G (kempeSwap c S 0 1) B : ℤ) - (sixPairMass G c B : ℤ) =
    ((pairMass G (kempeSwap c S 0 1) B 0 2 : ℤ) - (pairMass G c B 0 2 : ℤ)) +
    ((pairMass G (kempeSwap c S 0 1) B 0 3 : ℤ) - (pairMass G c B 0 3 : ℤ)) +
    ((pairMass G (kempeSwap c S 0 1) B 1 2 : ℤ) - (pairMass G c B 1 2 : ℤ)) +
    ((pairMass G (kempeSwap c S 0 1) B 1 3 : ℤ) - (pairMass G c B 1 3 : ℤ)) :=
  fourColorMass_swap_change G c B S 0 1 2 3 (by decide) (by decide) (by decide)
    (by decide)


/-- Pair mass depends on an unordered pair of colours. -/
theorem pairMass_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (a b : Fin k) :
    pairMass G c B a b = pairMass G c B b a := by
  classical
  have hg : bichromaticSubgraph G c a b = bichromaticSubgraph G c b a := by
    ext u v
    simp only [bichromaticSubgraph, bichromaticAdj, or_comm]
  have hc : pairComponent G c a b = pairComponent G c b a := by
    funext v
    unfold pairComponent
    rw [hg]
  simp only [pairMass, boundaryPairComponents, or_comm, hc]

/-- Any four distinct members of `Fin 4` enumerate the same six pair masses. -/
theorem fourColorMass_eq_sixPairMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 4) (B : Finset V) (a b d e : Fin 4)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) :
    fourColorMass G c B a b d e = sixPairMass G c B := by
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
    simp_all only [Fin.reduceFinMk, ne_eq, not_true_eq_false, Fin.zero_eta]
  all_goals
    simp only [fourColorMass, sixPairMass,
      pairMass_comm G c B 1 0, pairMass_comm G c B 2 0,
      pairMass_comm G c B 3 0, pairMass_comm G c B 2 1,
      pairMass_comm G c B 3 1, pairMass_comm G c B 3 2] <;> ring

/-- WP7 locality for any exchanged pair in the four-colour palette. -/
theorem sixPairMass_swap_change (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 4) (B : Finset V) (S : Set V) [DecidablePred (· ∈ S)]
    (a b d e : Fin 4) (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) :
    (sixPairMass G (kempeSwap c S a b) B : ℤ) - (sixPairMass G c B : ℤ) =
    ((pairMass G (kempeSwap c S a b) B a d : ℤ) - (pairMass G c B a d : ℤ)) +
    ((pairMass G (kempeSwap c S a b) B a e : ℤ) - (pairMass G c B a e : ℤ)) +
    ((pairMass G (kempeSwap c S a b) B b d : ℤ) - (pairMass G c B b d : ℤ)) +
    ((pairMass G (kempeSwap c S a b) B b e : ℤ) - (pairMass G c B b e : ℤ)) := by
  rw [← fourColorMass_eq_sixPairMass G (kempeSwap c S a b) B a b d e
    hab had hae hbd hbe hde,
    ← fourColorMass_eq_sixPairMass G c B a b d e hab had hae hbd hbe hde]
  exact fourColorMass_swap_change G c B S a b d e had.symm hbd.symm hae.symm hbe.symm

omit [DecidableEq V] in
/-- Components whose representatives reach the same vertex coincide. -/
lemma pairComponent_eq_of_common_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) {u v w : V}
    (hu : w ∈ pairComponent G c a b u) (hv : w ∈ pairComponent G c a b v) :
    pairComponent G c a b u = pairComponent G c a b v := by
  classical
  simp only [pairComponent, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  ext z
  simp only [pairComponent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hz => hv.trans (hu.symm.trans hz), fun hz => hu.trans (hv.symm.trans hz)⟩

/-- Distinct boundary components have disjoint exterior sets. -/
lemma boundaryPairComponents_pairwiseDisjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (a b : Fin k) :
    (boundaryPairComponents G c B a b : Set (Finset V)).PairwiseDisjoint
      (fun K => K \ B) := by
  classical
  intro K hK L hL hne
  change Disjoint (K \ B) (L \ B)
  rw [Finset.disjoint_left]
  intro w hwK hwL
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hL
  exact hne (pairComponent_eq_of_common_mem G c a b
    (Finset.mem_sdiff.mp hwK).1 (Finset.mem_sdiff.mp hwL).1)

/-- The sum of exterior sizes of distinct components is at most the carrier size. -/
lemma sum_exterior_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (a b : Fin k) :
    ∑ K ∈ boundaryPairComponents G c B a b, (K \ B).card ≤ Fintype.card V := by
  classical
  rw [← Finset.card_biUnion (boundaryPairComponents_pairwiseDisjoint G c B a b)]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- Boundary-weighted pair mass is bounded by the square of the carrier size. -/
theorem pairMass_le_card_sq (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (a b : Fin k) :
    pairMass G c B a b ≤ Fintype.card V ^ 2 := by
  classical
  exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun K _ => Nat.zero_le (K \ B).card)).trans
    (Nat.pow_le_pow_left (sum_exterior_card_le G c B a b) 2)

/-- Six component masses have the uniform quadratic bound used by the rank. -/
theorem fourColorMass_le_six_card_sq (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (B : Finset V) (a b d e : Fin k) :
    fourColorMass G c B a b d e ≤ 6 * Fintype.card V ^ 2 := by
  have h₁ := pairMass_le_card_sq G c B a b
  have h₂ := pairMass_le_card_sq G c B d e
  have h₃ := pairMass_le_card_sq G c B a d
  have h₄ := pairMass_le_card_sq G c B a e
  have h₅ := pairMass_le_card_sq G c B b d
  have h₆ := pairMass_le_card_sq G c B b e
  unfold fourColorMass
  omega

/-- Four-colour specialization of the six-pair quadratic bound. -/
theorem sixPairMass_le_six_card_sq (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 4) (B : Finset V) :
    sixPairMass G c B ≤ 6 * Fintype.card V ^ 2 :=
  fourColorMass_le_six_card_sq G c B 0 1 2 3

end SimpleGraph.Kempe
