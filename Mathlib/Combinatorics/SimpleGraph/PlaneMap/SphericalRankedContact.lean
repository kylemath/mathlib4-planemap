/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalMassContact

/-!
# Contact with an arbitrary natural-number rank

The rank family is fixed before the triangulation, root and deletion colouring
quantifiers. The macro relation remains the actual at-most-two component swaps.
The descent hypothesis is explicit and unproved. The path bound counts macros;
it is not a complexity bound for searching for them.
-/

@[expose] public section
namespace SimpleGraph.SphericalMap
open Classical
noncomputable section

/-- A rank family independent of the choice of deletion colouring. -/
abbrev DeletionRankFamily :=
  ∀ (n : ℕ) (M : SphericalMap n) (r : Fin n), DeletionColouring M r → ℕ

variable {n : ℕ} (M : SphericalMap n) (r : Fin n)

/-- A target reached by endpoint-rank-decreasing, at-most-two-swap macros. -/
def RankedGood (rank : DeletionColouring M r → ℕ) (c : DeletionColouring M r) : Prop :=
  Breadcrumb.Good rank (boundaryTarget M r) (TwoSwapMacro M r) c

/-- An actual finite macro path, carrying its number of macros. -/
inductive RankedMacroPath (rank : DeletionColouring M r → ℕ) :
    DeletionColouring M r → DeletionColouring M r → ℕ → Prop
  | nil (c) : RankedMacroPath rank c c 0
  | cons {c d e k} : TwoSwapMacro M r c d → rank d < rank c →
      RankedMacroPath rank d e k → RankedMacroPath rank c e (k + 1)

/-- A good state has a target path with at most its initial rank many macros. -/
theorem ranked_good_target_path {rank : DeletionColouring M r → ℕ}
    {c : DeletionColouring M r} (hc : RankedGood M r rank c) :
    ∃ d k, boundaryTarget M r d ∧ RankedMacroPath M r rank c d k ∧ k ≤ rank c := by
  induction hc with
  | @target c ht => exact ⟨c, 0, ht, RankedMacroPath.nil c, Nat.zero_le _⟩
  | @descend c z hm hr hz ih =>
    obtain ⟨d, k, ht, hp, hk⟩ := ih
    exact ⟨d, k + 1, ht, RankedMacroPath.cons hm hr hp, by omega⟩

/-- A rank bound gives a bound on path length, without making move search executable. -/
theorem ranked_good_target_path_of_le {rank : DeletionColouring M r → ℕ}
    {c : DeletionColouring M r} {B : ℕ} (hc : RankedGood M r rank c) (hB : rank c ≤ B) :
    ∃ d k, boundaryTarget M r d ∧ RankedMacroPath M r rank c d k ∧ k ≤ B := by
  obtain ⟨d, k, ht, hp, hk⟩ := ranked_good_target_path M r hc
  exact ⟨d, k, ht, hp, hk.trans hB⟩

/-- Any ranked good deletion colouring extends across the deleted root. -/
theorem colorable_of_ranked_good {rank : DeletionColouring M r → ℕ}
    (c : DeletionColouring M r) (hc : RankedGood M r rank c) : M.graph.Colorable 4 := by
  obtain ⟨d, _, ht, _, _⟩ := ranked_good_target_path M r hc
  exact M.colorable_of_boundary_target r d ht

/-- Some degree-five root works for every deletion colouring, for the fixed rank family. -/
def EmptyRankedRegionHypothesis (rank : DeletionRankFamily) : Prop :=
  ∀ (n : ℕ) (T : SphericalMap n), 0 < n → T.graph.Connected → T.Triangulated →
    (∀ x, 5 ≤ T.graph.degree x) →
    ∃ r, T.graph.degree r = 5 ∧ ∀ c : DeletionColouring T r,
      RankedGood T r (rank n T r) c

/-- Universal endpoint descent at a root chosen before the colouring. -/
def RankedMacroDescentHypothesis (rank : DeletionRankFamily) : Prop :=
  ∀ (n : ℕ) (T : SphericalMap n), 0 < n → T.graph.Connected → T.Triangulated →
    (∀ x, 5 ≤ T.graph.degree x) →
    ∃ r, T.graph.degree r = 5 ∧ ∀ c : DeletionColouring T r,
      ¬ boundaryTarget T r c → ∃ d, TwoSwapMacro T r c d ∧
        rank n T r d < rank n T r c

/-- Well-founded descent produces ranked good states. -/
theorem empty_ranked_region_of_descent {rank : DeletionRankFamily}
    (h : RankedMacroDescentHypothesis rank) : EmptyRankedRegionHypothesis rank := by
  intro n T hn hconn htri hdeg
  obtain ⟨r, hr, hstep⟩ := h n T hn hconn htri hdeg
  exact ⟨r, hr, Breadcrumb.good_of_forall_descent hstep⟩

/-- The ranked-good and immediate-descent formulations have identical quantifiers. -/
theorem ranked_descent_of_empty_region {rank : DeletionRankFamily}
    (h : EmptyRankedRegionHypothesis rank) : RankedMacroDescentHypothesis rank := by
  intro n T hn hconn htri hdeg
  obtain ⟨r, hr, hgood⟩ := h n T hn hconn htri hdeg
  refine ⟨r, hr, ?_⟩
  intro c hct
  cases hgood c with
  | target ht => exact (hct ht).elim
  | @descend x z hm hr hz => exact ⟨z, hm, hr⟩

/-- Generic conditional contact: any such rank family suffices for four colours. -/
theorem four_color_of_empty_ranked_region {rank : DeletionRankFamily}
    (h : EmptyRankedRegionHypothesis rank) (M : SphericalMap n) : M.graph.Colorable 4 := by
  apply M.four_color_of_triangulated_five_extension
  intro n T hn hconn htri hdeg
  obtain ⟨r, hr, hgood⟩ := h n T hn hconn htri hdeg
  refine ⟨r, hr, ?_⟩
  rintro ⟨c⟩
  let s : DeletionColouring T r := ⟨c, fun u v huv => c.valid huv⟩
  exact T.colorable_of_ranked_good r s (hgood s)

/-- The rank need not be the component-mass rank. The premise remains unproved. -/
theorem four_color_of_ranked_macro_descent {rank : DeletionRankFamily}
    (h : RankedMacroDescentHypothesis rank) (M : SphericalMap n) : M.graph.Colorable 4 :=
  M.four_color_of_empty_ranked_region (empty_ranked_region_of_descent h)

/-- A bounded secondary coordinate scalarizes strict lexicographic descent.
Both bounds are necessary; the multiplier is fixed before comparing states. -/
theorem bounded_lex_scalar_lt_iff {p p' s s' B : ℕ} (hs : s ≤ B) (hs' : s' ≤ B) :
    (B + 1) * p' + s' < (B + 1) * p + s ↔
      p' < p ∨ (p' = p ∧ s' < s) := by
  constructor
  · intro h
    by_cases hp : p' < p
    · exact Or.inl hp
    · have hpp : p ≤ p' := Nat.le_of_not_gt hp
      have heq : p' = p := by
        by_contra hne
        have hlt : p < p' := by omega
        have hm := Nat.mul_le_mul_left (B + 1) (show p + 1 ≤ p' by omega)
        rw [Nat.mul_add, Nat.mul_one] at hm
        omega
      exact Or.inr ⟨heq, by simpa [heq] using h⟩
  · rintro (hp | ⟨rfl, hss⟩)
    · have hm := Nat.mul_le_mul_left (B + 1) (show p' + 1 ≤ p by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    · exact Nat.add_lt_add_left hss _

/-- A binary primary coordinate yields a scalar at most twice the secondary bound plus one. -/
theorem bounded_binary_scalar_le {p s B : ℕ} (hp : p ≤ 1) (hs : s ≤ B) :
    (B + 1) * p + s ≤ 2 * B + 1 := by
  have hm := Nat.mul_le_mul_left (B + 1) hp
  simp only [Nat.mul_one] at hm
  omega

/-- The existing mass rank is one rank family. -/
def massRankFamily : DeletionRankFamily := fun _ M r => deletionMassRank M r

@[simp] theorem ranked_good_mass_iff (c : DeletionColouring M r) :
    RankedGood M r (massRankFamily n M r) c ↔ MassGood M r c := Iff.rfl

@[simp] theorem ranked_mass_descent_iff :
    RankedMacroDescentHypothesis massRankFamily ↔ MassMacroDescentHypothesis := Iff.rfl

@[simp] theorem empty_ranked_mass_region_iff :
    EmptyRankedRegionHypothesis massRankFamily ↔ EmptyMassRegionHypothesis := Iff.rfl

/-- Recover the mass contact theorem directly through the generic interface. -/
theorem four_color_of_mass_rank_specialization (h : MassMacroDescentHypothesis)
    (M : SphericalMap n) : M.graph.Colorable 4 :=
  four_color_of_ranked_macro_descent (rank := massRankFamily) h M

end
end SimpleGraph.SphericalMap
