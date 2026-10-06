/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TheoremPPoleRules

/-!
# Theorem P: cut lemma (two junctions separate the belt)

Offsets `δ i l = (l - i).val` and the arc after junction `u_i` up to junction `u_j`.
-/

@[expose] public section
namespace SimpleGraph.TheoremPPole
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

variable {n : ℕ}

/-! ### Offsets -/

/-- Offset of `l` from `i`. -/
def delta (i l : ZMod n) : ℕ := (l - i).val

section offsets
variable [NeZero n]

lemma val_one' (hn : 2 ≤ n) : (1 : ZMod n).val = 1 := by
  rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_eq_of_lt (by omega)

lemma delta_lt (i l : ZMod n) : delta i l < n := ZMod.val_lt _

lemma delta_succ (hn : 2 ≤ n) {i l : ZMod n} (h : delta i l + 1 < n) :
    delta i (l+1) = delta i l + 1 := by
  unfold delta at *
  have : l + 1 - i = (l - i) + 1 := by ring
  rw [this, ZMod.val_add, val_one' hn]
  exact Nat.mod_eq_of_lt h

lemma delta_pred (hn : 2 ≤ n) {i l : ZMod n} (h : 0 < delta i l) :
    delta i (l-1) = delta i l - 1 := by
  unfold delta at *
  have e : l - i = (l - 1 - i) + 1 := by ring
  have hlt := ZMod.val_lt (l - 1 - i)
  rw [e, ZMod.val_add, val_one' hn] at h ⊢
  by_cases hc : (l - 1 - i).val + 1 < n
  · rw [Nat.mod_eq_of_lt hc]; omega
  · have : (l - 1 - i).val + 1 = n := by omega
    rw [this, Nat.mod_self] at h
    omega

lemma delta_zero {i l : ZMod n} : delta i l = 0 ↔ l = i := by
  unfold delta
  rw [ZMod.val_eq_zero, sub_eq_zero]

lemma delta_inj {i l l' : ZMod n} (h : delta i l = delta i l') : l = l' := by
  unfold delta at h
  have := ZMod.val_injective n h
  exact sub_left_injective this

end offsets

/-- The arc strictly after `u_i` and before `u_j`, with offsets `< d`. -/
def InArc (i : ZMod n) (d : ℕ) : Vertex n → Prop
  | .a => False
  | .b => False
  | .u l => 1 ≤ delta i l ∧ delta i l < d
  | .v l => delta i l < d

/-- Closedness of the arc under active edges of a `{x,y}` pair graph, when the
two glue edges are inactive. -/
theorem arc_closed (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c)
    {i j : ZMod n} (hi : Jn c i) (hj : Jn c j) {x y : Colour}
    (hx : x ≠ c b) (hy : y ≠ c b)
    (gi : ¬ ((c (v (i-1)) = x ∨ c (v (i-1)) = y) ∧ (c (v i) = x ∨ c (v i) = y)))
    (gj : ¬ ((c (v (j-1)) = x ∨ c (v (j-1)) = y) ∧ (c (v j) = x ∨ c (v j) = y)))
    {w w' : Vertex n}
    (e : (VacancyShortFill.pairGraph (graph n) a c x y).Adj w w')
    (hw : InArc i (delta i j) w) : InArc i (delta i j) w' := by
  obtain ⟨hadj, ⟨hwa, hwc⟩, ⟨hwa', hwc'⟩⟩ := e
  have hn2 : 2 ≤ n := by omega
  have hdn := delta_lt i j
  -- junction vertices are inactive
  have hjb : ∀ t : ZMod n, Jn c t → ¬ (c (u t) = x ∨ c (u t) = y) := by
    intro t ht h
    unfold Jn at ht
    rcases h with h | h
    · exact hx (h.symm.trans ht)
    · exact hy (h.symm.trans ht)
  have hbb : ¬ (c b = x ∨ c b = y) := by
    rintro (h | h)
    · exact hx h.symm
    · exact hy h.symm
  cases w with
  | a => exact absurd rfl hwa
  | b => exact (hbb hwc).elim
  | u l =>
    obtain ⟨hl1, hl2⟩ := hw
    rcases (adj_u hn l w').mp hadj with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hwa'
    · -- u (l+1)
      change 1 ≤ delta i (l+1) ∧ delta i (l+1) < delta i j
      rw [delta_succ hn2 (by omega)]
      refine ⟨by omega, ?_⟩
      by_contra hh
      have : delta i (l+1) = delta i j := by rw [delta_succ hn2 (by omega)]; omega
      have := delta_inj this
      subst this
      exact hjb _ hj hwc'
    · exact hl2
    · change delta i (l-1) < delta i j
      rw [delta_pred hn2 (by omega)]; omega
    · change 1 ≤ delta i (l-1) ∧ delta i (l-1) < delta i j
      rw [delta_pred hn2 (by omega)]
      refine ⟨?_, by omega⟩
      by_contra hh
      have h0 : delta i (l-1) = 0 := by rw [delta_pred hn2 (by omega)]; omega
      have := delta_zero.mp h0
      subst this
      exact hjb _ hi hwc'
  | v l =>
    have hl2 : delta i l < delta i j := hw
    rcases (adj_v hn l w').mp hadj with rfl | rfl | rfl | rfl | rfl
    · exact (hbb hwc').elim
    · change delta i (l-1) < delta i j
      by_cases h0 : delta i l = 0
      · exfalso
        have := delta_zero.mp h0
        subst this
        exact gi ⟨hwc', hwc⟩
      · rw [delta_pred hn2 (by omega)]; omega
    · change 1 ≤ delta i l ∧ delta i l < delta i j
      refine ⟨?_, hl2⟩
      by_contra hh
      have h0 : delta i l = 0 := by omega
      have := delta_zero.mp h0
      subst this
      exact hjb _ hi hwc'
    · change 1 ≤ delta i (l+1) ∧ delta i (l+1) < delta i j
      rw [delta_succ hn2 (by omega)]
      refine ⟨by omega, ?_⟩
      by_contra hh
      have : delta i (l+1) = delta i j := by rw [delta_succ hn2 (by omega)]; omega
      have := delta_inj this
      subst this
      exact hjb _ hj hwc'
    · change delta i (l+1) < delta i j
      rw [delta_succ hn2 (by omega)]
      by_contra hh
      have : delta i (l+1) = delta i j := by rw [delta_succ hn2 (by omega)]; omega
      have := delta_inj this
      subst this
      simp only [add_sub_cancel_right] at gj
      exact gj ⟨hwc, hwc'⟩

/-- No pair-graph walk leaves the arc. -/
theorem arc_reach (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c)
    {i j : ZMod n} (hi : Jn c i) (hj : Jn c j) {x y : Colour}
    (hx : x ≠ c b) (hy : y ≠ c b)
    (gi : ¬ ((c (v (i-1)) = x ∨ c (v (i-1)) = y) ∧ (c (v i) = x ∨ c (v i) = y)))
    (gj : ¬ ((c (v (j-1)) = x ∨ c (v (j-1)) = y) ∧ (c (v j) = x ∨ c (v j) = y)))
    {w w' : Vertex n} (hw : InArc i (delta i j) w)
    (r : (VacancyShortFill.pairGraph (graph n) a c x y).Reachable w w') :
    InArc i (delta i j) w' :=
  VacancyShortFill.reachable_invariant
    (fun _ _ e h => arc_closed hn hc hi hj hx hy gi gj e h) hw r

end SimpleGraph.TheoremPPole
