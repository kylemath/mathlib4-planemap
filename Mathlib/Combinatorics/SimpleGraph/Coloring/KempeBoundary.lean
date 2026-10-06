module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.FiniteReachability
public import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeMass

/-! # Removing a singleton boundary colour by a Kempe swap

No planarity hypothesis is needed. The boundary is an arbitrary finite set.
-/
@[expose] public section
namespace SimpleGraph.Kempe
variable {V : Type*} {k : ℕ}

/-- A swap set meeting the boundary only at a uniquely coloured vertex removes
that vertex's old colour from the entire boundary. -/
theorem swap_removes_singleton_boundary_colour [DecidableEq V]
    (c : V → Fin k) (B : Finset V) (S : Set V) [DecidablePred (· ∈ S)]
    (a b : Fin k) (hab : a ≠ b) (u : V) (hu : c u = a) (huS : u ∈ S)
    (hunique : ∀ v ∈ B, c v = a → v = u)
    (hboundary : ∀ v ∈ B, v ∈ S → v = u) :
    ∀ v ∈ B, kempeSwap c S a b v ≠ a := by
  intro v hv
  by_cases hvs : v ∈ S
  · have hve := hboundary v hv hvs
    subst v
    simpa [kempeSwap, huS, hu] using hab.symm
  · intro he
    have hca : c v = a := (kempeSwap_outside c S a b v hvs).symm.trans he
    have hve := hunique v hv hca
    subst v
    exact hvs huS

/-- Missing one of four colours leaves at most three boundary colours. -/
theorem boundary_card_le_three_of_missing [DecidableEq V]
    (c : V → Fin 4) (B : Finset V) (a : Fin 4)
    (ha : ∀ v ∈ B, c v ≠ a) : (B.image c).card ≤ 3 := by
  have hsub : B.image c ⊆ (Finset.univ : Finset (Fin 4)).erase a := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    simp [ha v hv]
  have hh := Finset.card_le_card hsub
  simpa using hh

/-- A disconnected singleton chain reaches a three-colour boundary. -/
theorem singleton_chain_boundary_target [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Fin 4)
    (B : Finset V) (a b : Fin 4) (hab : a ≠ b) (u : V) (hu : c u = a)
    (hunique : ∀ v ∈ B, c v = a → v = u)
    (hboundary : ∀ v ∈ B,
      (bichromaticSubgraph G c a b).Reachable u v → v = u) :
    (B.image (FiniteReachability.componentSwap G c a b u)).card ≤ 3 := by
  classical
  rw [FiniteReachability.componentSwap_eq]
  apply boundary_card_le_three_of_missing
    (kempeSwap c (kempeChain G c a b u) a b) B a
  exact swap_removes_singleton_boundary_colour c B (kempeChain G c a b u)
    a b hab u hu (Reachable.refl u) hunique hboundary

/-- The singleton-chain move is a legal proper colouring and reaches a target. -/
theorem singleton_chain_proper_target [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Fin 4)
    (hc : IsProperColouring G c) (B : Finset V)
    (a b : Fin 4) (hab : a ≠ b) (u : V) (hu : c u = a)
    (hunique : ∀ v ∈ B, c v = a → v = u)
    (hboundary : ∀ v ∈ B,
      (bichromaticSubgraph G c a b).Reachable u v → v = u) :
    IsProperColouring G (FiniteReachability.componentSwap G c a b u) ∧
    (B.image (FiniteReachability.componentSwap G c a b u)).card ≤ 3 := by
  exact ⟨FiniteReachability.componentSwap_proper G c a b hab u hu hc,
    singleton_chain_boundary_target G c B a b hab u hu hunique hboundary⟩

/-- The surplus is truncated natural subtraction, hence zero at a target. -/
def boundarySurplus [DecidableEq V] (c : V → Fin 4) (B : Finset V) : ℕ :=
  (B.image c).card - 3

/-- The mass rank, with an explicit bound n on the deletion carrier size. -/
noncomputable def boundaryMassRank [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Fin 4)
    (B : Finset V) (n : ℕ) : ℕ :=
  (6 * n ^ 2 + 1) * boundarySurplus c B + sixPairMass G c B

/-- Reaching a target from a four-colour boundary strictly lowers the actual
component-mass rank. The carrier bound allows n to be the order before deletion. -/
theorem boundaryMassRank_lt_of_target [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c c' : V → Fin 4)
    (B : Finset V) (n : ℕ) (hn : Fintype.card V ≤ n)
    (hfull : (B.image c).card = 4) (htarget : (B.image c').card ≤ 3) :
    boundaryMassRank G c' B n < boundaryMassRank G c B n := by
  have hq := sixPairMass_le_six_card_sq G c' B
  have hpow := Nat.pow_le_pow_left hn 2
  have hq' : sixPairMass G c' B ≤ 6 * n ^ 2 :=
    hq.trans (Nat.mul_le_mul_left 6 hpow)
  have hp : boundarySurplus c B = 1 := by simp [boundarySurplus, hfull]
  have hp' : boundarySurplus c' B = 0 := by
    exact Nat.sub_eq_zero_of_le htarget
  simp only [boundaryMassRank, hp, hp', mul_zero, zero_add, mul_one]
  omega

/-- A free singleton component strictly lowers the rank in one legal swap. -/
theorem singleton_chain_rank_decreases [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Fin 4)
    (B : Finset V) (n : ℕ) (hn : Fintype.card V ≤ n)
    (hfull : (B.image c).card = 4)
    (a b : Fin 4) (hab : a ≠ b) (u : V) (hu : c u = a)
    (hunique : ∀ v ∈ B, c v = a → v = u)
    (hboundary : ∀ v ∈ B,
      (bichromaticSubgraph G c a b).Reachable u v → v = u) :
    boundaryMassRank G (FiniteReachability.componentSwap G c a b u) B n <
      boundaryMassRank G c B n :=
  boundaryMassRank_lt_of_target G c _ B n hn hfull
    (singleton_chain_boundary_target G c B a b hab u hu hunique hboundary)

/-- A one-swap-stuck state links every singleton to another boundary vertex in
all its colour pairs. This is Lemma 7.4, without a planarity hypothesis. -/
theorem singleton_locked_of_no_rank_decrease [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Fin 4)
    (B : Finset V) (n : ℕ) (hn : Fintype.card V ≤ n)
    (hfull : (B.image c).card = 4) (u : V)
    (hunique : ∀ v ∈ B, c v = c u → v = u)
    (hblocked : ∀ b : Fin 4, c u ≠ b →
      boundaryMassRank G c B n ≤
        boundaryMassRank G (FiniteReachability.componentSwap G c (c u) b u) B n) :
    ∀ b : Fin 4, c u ≠ b → ∃ v ∈ B, v ≠ u ∧
      (bichromaticSubgraph G c (c u) b).Reachable u v := by
  classical
  intro b hb
  by_contra hnone
  have hboundary : ∀ v ∈ B,
      (bichromaticSubgraph G c (c u) b).Reachable u v → v = u := by
    intro v hv hr
    by_contra hne
    exact hnone ⟨v, hv, hne, hr⟩
  exact (not_lt_of_ge (hblocked b hb))
    (singleton_chain_rank_decreases G c B n hn hfull (c u) b hb u rfl
      hunique hboundary)

end SimpleGraph.Kempe
