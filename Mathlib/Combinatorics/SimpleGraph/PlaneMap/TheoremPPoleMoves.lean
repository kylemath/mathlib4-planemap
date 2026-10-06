/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TheoremPPoleBasic

/-!
# Theorem P: rules T1 and F, junction bookkeeping
-/

@[expose] public section
namespace SimpleGraph.TheoremPPole
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

variable {n : ℕ}

/-! ### Junction preservation under swaps avoiding the colour of `b` -/

lemma swap_b {c : Vertex n → Colour} {x y : Colour} {S : Set (Vertex n)}
    (hx : x ≠ c b) (hy : y ≠ c b) :
    VacancyShortFill.swap c x y S b = c b :=
  VacancyShortFill.swap_other hx.symm hy.symm

lemma swap_jn {c : Vertex n → Colour} {x y : Colour} {S : Set (Vertex n)}
    (hx : x ≠ c b) (hy : y ≠ c b) (w : Vertex n) :
    VacancyShortFill.swap c x y S w = c b ↔ c w = c b := by
  by_cases hw : w ∈ S
  · rw [VacancyShortFill.swap_in hw, Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_of_ne_of_ne hx.symm hy.symm]
  · rw [VacancyShortFill.swap_out hw]

lemma jn_swap {c : Vertex n → Colour} {x y : Colour} {S : Set (Vertex n)}
    (hx : x ≠ c b) (hy : y ≠ c b) (i : ZMod n) :
    Jn (VacancyShortFill.swap c x y S) i ↔ Jn c i := by
  unfold Jn
  rw [swap_b hx hy, swap_jn hx hy]

/-- The set of junction indices. -/
def jset [NeZero n] (c : Vertex n → Colour) : Finset (ZMod n) :=
  Finset.univ.filter (fun i => Jn c i)

lemma mem_jset [NeZero n] {c : Vertex n → Colour} {i : ZMod n} : i ∈ jset c ↔ Jn c i := by
  simp [jset]

lemma card_drop [NeZero n] {c c' : Vertex n → Colour} {i : ZMod n}
    (h : ∀ j, Jn c' j ↔ Jn c j ∧ j ≠ i) (hi : Jn c i) :
    (jset c').card + 1 = (jset c).card := by
  have : jset c' = (jset c).erase i := by
    ext j; simp [mem_jset, h j, Finset.mem_erase, and_comm]
  rw [this, Finset.card_erase_add_one (mem_jset.mpr hi)]

/-! ### Exposure counting -/

open Classical in
lemma three_le_of_exposed [NeZero n] {c : Vertex n → Colour}
    (h : ∀ x, x ≠ c b → ∃ i j, i ≠ j ∧ Exposed c x i ∧ Exposed c x j) :
    3 ≤ (jset c).card := by
  set J := jset c with hJ
  set Exp : Finset (ZMod n) := J.image (· + 1) ∪ J.image (· - 1) with hExp
  have hExpc : Exp.card ≤ 2 * J.card := by
    calc Exp.card ≤ (J.image (· + 1)).card + (J.image (· - 1)).card := Finset.card_union_le _ _
      _ ≤ J.card + J.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * J.card := by ring
  set X : Finset Colour := Finset.univ.erase (c b) with hX
  have hXc : X.card = 3 := by
    rw [hX, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  let E : Colour → Finset (ZMod n) := fun x => Finset.univ.filter (Exposed c x)
  have hdisj : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint (E x) (E y) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    intro i hx hy
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hxy (hx.1.symm.trans hy.1)
  have hsub : X.biUnion E ⊆ Exp := by
    intro i hi
    simp only [Finset.mem_biUnion, E, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨x, _, _, hj⟩ := hi
    rw [hExp, Finset.mem_union]
    rcases hj with hj | hj
    · left
      exact Finset.mem_image.mpr ⟨i-1, mem_jset.mpr hj, by simp⟩
    · right
      exact Finset.mem_image.mpr ⟨i+1, mem_jset.mpr hj, by simp⟩
  have hbig : ∀ x ∈ X, 2 ≤ (E x).card := by
    intro x hx
    obtain ⟨i, j, hij, hi, hj⟩ := h x (Finset.ne_of_mem_erase hx)
    have : ({i, j} : Finset (ZMod n)) ⊆ E x := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> simp [E, *]
    calc 2 = ({i, j} : Finset (ZMod n)).card := (Finset.card_pair hij).symm
      _ ≤ _ := Finset.card_le_card this
  have hsum : X.card * 2 ≤ (X.biUnion E).card := by
    rw [Finset.card_biUnion hdisj]
    calc X.card * 2 = ∑ _x ∈ X, 2 := by simp
      _ ≤ _ := Finset.sum_le_sum hbig
  have := (hsum.trans (Finset.card_le_card hsub)).trans hExpc
  omega

/-! ### Rule T1: zeroing interior vertices -/

lemma step_facts (hn : 5 ≤ n) {c c' : Vertex n → Colour} (hc : PR n c) {x : Colour}
    (hx : x ≠ c b) {i0 : ZMod n} (hI : c (u i0) = x) (hself : c' (u i0) = c b)
    (hother : ∀ v, v ≠ u i0 → c' v = c v) :
    c' b = c b ∧
    (∀ i, c' (u i) = x → (Jn c' (i-1) ↔ Jn c (i-1)) ∧ (Jn c' (i+1) ↔ Jn c (i+1))) := by
  have hb : c' b = c b := hother b (by simp)
  refine ⟨hb, fun i hi => ?_⟩
  have hii : i ≠ i0 := by
    rintro rfl; rw [hself] at hi; exact hx hi.symm
  have hcu : c (u i) = x := by rw [← hi, hother _ (by simpa using hii)]
  constructor
  · by_cases h : i - 1 = i0
    · exfalso; apply cuu' hn hc i; rw [h, hI, hcu]
    · simp only [Jn, hb, hother _ (show u (i-1) ≠ u i0 by simpa using h)]
  · by_cases h : i + 1 = i0
    · exfalso; apply cuu hn hc i; rw [h, hI, hcu]
    · simp only [Jn, hb, hother _ (show u (i+1) ≠ u i0 by simpa using h)]

theorem t1 (hn : 5 ≤ n) [NeZero n] {x : Colour} :
    ∀ (N : ℕ) (c : Vertex n → Colour), PR n c → c b ≠ x →
    (∀ i j, Exposed c x i → Exposed c x j → i = j) →
    (Finset.univ.filter (fun i : ZMod n => Interior c x i)).card ≤ N →
    ∃ k, k ≤ N ∧ ∃ d, VacancyShortFill.PurePath (graph n) a k c d ∧ Good d := by
  intro N
  induction N with
  | zero =>
    intro c hc hx hE hcard
    refine ⟨0, le_rfl, c, .nil c, x, ?_⟩
    intro i j hi hj
    have hz : (Finset.univ.filter (fun i : ZMod n => Interior c x i)) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have key : ∀ t, c (u t) = x → Exposed c x t := by
      intro t ht
      refine ⟨ht, ?_⟩
      by_contra hh
      push Not at hh
      have : t ∈ (Finset.univ.filter (fun i : ZMod n => Interior c x i)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hh.1, hh.2⟩
      rw [hz] at this; exact absurd this (Finset.notMem_empty _)
    exact hE i j (key i hi) (key j hj)
  | succ N ih =>
    intro c hc hx hE hcard
    by_cases hI : ∃ i, Interior c x i
    · obtain ⟨i0, hi0, hl, hr⟩ := hI
      have hxb : x ≠ c b := fun h => hx h.symm
      obtain ⟨hstep, hself, hother⟩ := single_step hc (w := u i0) (by simp)
        (x := x) (y := c b) hxb hi0 (by
          intro v hv hva
          rcases (adj_u hn i0 v).mp hv with rfl | rfl | rfl | rfl | rfl
          · exact (hva rfl).elim
          · exact fun h => hr h
          · exact (cvb hn hc i0)
          · exact (cvb hn hc (i0-1))
          · exact fun h => hl h)
      set c' := VacancyShortFill.swap c x (c b) {u i0} with hc'
      have hpr : PR n c' := VacancyShortFill.kempe_proper _ hc hstep
      obtain ⟨hb', hexp⟩ := step_facts hn hc hxb hi0 hself hother
      have hE' : ∀ i j, Exposed c' x i → Exposed c' x j → i = j := by
        intro i j hi hj
        apply hE
        · obtain ⟨h1, h2⟩ := hexp i hi.1
          exact ⟨by rw [← hi.1, hother _ (by
            intro e; have := hi.1; rw [show u i = u i0 from e, hself] at this
            exact hx this)], by rw [← h1, ← h2]; exact hi.2⟩
        · obtain ⟨h1, h2⟩ := hexp j hj.1
          exact ⟨by rw [← hj.1, hother _ (by
            intro e; have := hj.1; rw [show u j = u i0 from e, hself] at this
            exact hx this)], by rw [← h1, ← h2]; exact hj.2⟩
      have hlt : (Finset.univ.filter (fun i : ZMod n => Interior c' x i)).card <
          (Finset.univ.filter (fun i : ZMod n => Interior c x i)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0, hl, hr⟩, ?_⟩
          intro hm
          have := (Finset.mem_filter.mp hm).2.1
          rw [hself] at this; exact hx this
        · intro i hi
          obtain ⟨_, h0, h1, h2⟩ := Finset.mem_filter.mp hi
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          obtain ⟨e1, e2⟩ := hexp i h0
          refine ⟨?_, fun h => h1 (e1.mpr h), fun h => h2 (e2.mpr h)⟩
          rw [← h0, hother _ (by
            intro e; rw [show u i = u i0 from e, hself] at h0; exact hx h0)]
      obtain ⟨k, hk, d, hd, hg⟩ := ih c' hpr (by rw [hb']; exact hx) hE' (by omega)
      exact ⟨k+1, by omega, d, .cons hstep hd, hg⟩
    · push Not at hI
      refine ⟨0, Nat.zero_le _, c, .nil c, x, ?_⟩
      intro i j hi hj
      have key : ∀ t, c (u t) = x → Exposed c x t := by
        intro t ht
        refine ⟨ht, ?_⟩
        by_contra hh
        push Not at hh
        exact hI t ⟨ht, hh.1, hh.2⟩
      exact hE i j (key i hi) (key j hj)

end SimpleGraph.TheoremPPole
