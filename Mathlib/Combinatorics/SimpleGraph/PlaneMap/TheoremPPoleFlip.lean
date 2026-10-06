/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TheoremPPoleChain

/-!
# Theorem P: rule S (the flip) and consecutive junctions
-/

@[expose] public section
namespace SimpleGraph.TheoremPPole
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

variable {n : ℕ}

/-- `RN` gives the two-move kill. -/
theorem rn_step (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c) {t : ZMod n}
    (h : RN c t) :
    ∃ c'', VacancyShortFill.PurePath (graph n) a 2 c c'' ∧
      (jset c'').card + 1 = (jset c).card := by
  rcases h with ⟨⟨hj, e2, e1⟩, hnd⟩ | ⟨⟨hj, e1, e2⟩, hnd⟩
  · exact k_step_R1 hn hc hj e2 e1 hnd
  · exact k_step_R2 hn hc hj e1 e2 hnd

/-! ### pure colour lemmas for the flip -/

lemma flip_J1 (β P Q m z x y : Colour) (hP : P ≠ β) (hQ : Q ≠ β) (hPQ : P ≠ Q)
    (hm : m ≠ β) (hmP : m ≠ P) (hmQ : m ≠ Q) (hz : z ≠ β) (hzm : z ≠ m)
    (hxy : x ≠ y) (hxb : x ≠ β) (hxz : x ≠ z) (hyb : y ≠ β) (hyz : y ≠ z) :
    (Equiv.swap x y m = P ∧ m ≠ Equiv.swap x y Q) ∨
    (m = Equiv.swap x y Q ∧ Equiv.swap x y m ≠ P) := by
  revert β P Q m z x y; decide +kernel

lemma flip_J2 (β P Q m z x y : Colour) (hP : P ≠ β) (hQ : Q ≠ β) (hPQ : P ≠ Q)
    (hm : m ≠ β) (hmP : m ≠ P) (hmQ : m ≠ Q) (hz : z ≠ β) (hzm : z ≠ m)
    (hxy : x ≠ y) (hxb : x ≠ β) (hxz : x ≠ z) (hyb : y ≠ β) (hyz : y ≠ z) :
    (m = Equiv.swap x y P ∧ Equiv.swap x y m ≠ Q) ∨
    (Equiv.swap x y m = Q ∧ m ≠ Equiv.swap x y P) := by
  revert β P Q m z x y; decide +kernel

lemma seed_col (β m z x y : Colour) (hmb : m ≠ β) (hzm : z ≠ m) (hzb : z ≠ β)
    (hxy : x ≠ y) (hxb : x ≠ β) (hxz : x ≠ z) (hyb : y ≠ β) (hyz : y ≠ z) :
    m = x ∨ m = y := by
  revert β m z x y; decide +kernel

lemma glue_col (β P Q m z x y : Colour) (hP : P ≠ β) (hQ : Q ≠ β) (hPQ : P ≠ Q)
    (hm : m ≠ β) (hmP : m ≠ P) (hmQ : m ≠ Q) (hz : z ≠ β) (hzm : z ≠ m)
    (hxy : x ≠ y) (hxb : x ≠ β) (hxz : x ≠ z) (hyb : y ≠ β) (hyz : y ≠ z) :
    ¬ ((P = x ∨ P = y) ∧ (Q = x ∨ Q = y)) := by
  revert β P Q m z x y; decide +kernel

lemma exists_z (β m1 m2 : Colour) : ∃ z, z ≠ β ∧ z ≠ m1 ∧ z ≠ m2 := by
  revert β m1 m2; decide

lemma exists_xy (β z : Colour) (h : z ≠ β) :
    ∃ x y, x ≠ y ∧ x ≠ β ∧ x ≠ z ∧ y ≠ β ∧ y ≠ z := by
  revert β z; decide

/-! ### Consecutive junctions -/

theorem exists_consecutive [NeZero n] (hn : 2 ≤ n) {c : Vertex n → Colour}
    (h2 : 2 ≤ (jset c).card) :
    ∃ i j, Jn c i ∧ Jn c j ∧ j ≠ i ∧
      ∀ k : ℕ, 1 ≤ k → k < delta i j → ¬ Jn c (i + (k : ZMod n)) := by
  classical
  obtain ⟨i, hi⟩ : (jset c).Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨j0, hj0, hj0i⟩ := Finset.exists_mem_ne (by omega : 1 < (jset c).card) i
  have hex : ∃ d : ℕ, 1 ≤ d ∧ d < n ∧ Jn c (i + (d : ZMod n)) := by
    refine ⟨delta i j0, ?_, delta_lt i j0, ?_⟩
    · by_contra hh
      exact hj0i (delta_zero.mp (by omega))
    · rw [← eq_add_delta]; exact mem_jset.mp hj0
  let d := Nat.find hex
  obtain ⟨hd1, hdn, hdj⟩ := Nat.find_spec hex
  refine ⟨i, i + (d : ZMod n), mem_jset.mp hi, hdj, ?_, ?_⟩
  · intro h
    have := delta_add hn i d hdn
    rw [h, delta_self] at this; omega
  · intro k hk hkd hJ
    rw [delta_add hn i d hdn] at hkd
    exact Nat.find_min hex hkd ⟨hk, by omega, hJ⟩

/-! ### Rule S -/

section flip
variable [NeZero n]

/-- X junctions have equal ring neighbours. -/
lemma xj_eq (hn : 5 ≤ n) {c : Vertex n → Colour} (hc : PR n c) {t : ZMod n}
    (h : XJ c t) : c (u (t+1)) = c (u (t-1)) := by
  obtain ⟨hj, x1, x2⟩ := h
  have hPQ := cvv' hn hc t
  have hA1 : c (u (t-1)) ≠ c (v (t-1)) := by simpa using cuv0 hn hc (t-1)
  have hA2 : c (u (t+1)) ≠ c (v t) := (cvu1 hn hc t).symm
  have hβP := cvb hn hc (t-1)
  have hβQ := cvb hn hc t
  have hA1b : c (u (t-1)) ≠ c b := fun h => cuu' hn hc t (h.trans hj.symm)
  have hA2b : c (u (t+1)) ≠ c b := fun h => cuu hn hc t (hj.trans h.symm)
  have := (c (u (t+1))).isLt; have := (c (u (t-1))).isLt; have := (c (v t)).isLt
  have := (c (v (t-1))).isLt; have := (c b).isLt
  simp only [Fin.ext_iff, ne_eq] at *
  omega

lemma arc_facts (hn : 5 ≤ n) {c : Vertex n → Colour} (hc : PR n c) {i j : ZMod n}
    (hi : Jn c i) (hj : Jn c j) (hij : j ≠ i) :
    InArc i (delta i j) (v i) ∧ InArc i (delta i j) (u (i+1)) ∧
    ¬ InArc i (delta i j) (v (i-1)) ∧ ¬ InArc i (delta i j) (u (i-1)) ∧
    InArc i (delta i j) (v (j-1)) ∧ InArc i (delta i j) (u (j-1)) ∧
    ¬ InArc i (delta i j) (v j) ∧ ¬ InArc i (delta i j) (u (j+1)) := by
  have hd2 := two_le_delta hn hc hi hj hij
  have hdn := delta_lt i j
  have hn2 : 2 ≤ n := by omega
  have hp := delta_prev hn2 i
  have hjp : delta i (j-1) = delta i j - 1 := delta_pred hn2 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change delta i i < delta i j; rw [delta_self]; omega
  · change 1 ≤ delta i (i+1) ∧ delta i (i+1) < delta i j
    rw [delta_next hn2]; omega
  · change ¬ (delta i (i-1) < delta i j); omega
  · change ¬ (1 ≤ delta i (i-1) ∧ delta i (i-1) < delta i j); omega
  · change delta i (j-1) < delta i j; omega
  · change 1 ≤ delta i (j-1) ∧ delta i (j-1) < delta i j; omega
  · change ¬ (delta i j < delta i j); omega
  · change ¬ (1 ≤ delta i (j+1) ∧ delta i (j+1) < delta i j)
    rintro ⟨h1, h2⟩
    have := delta_pred hn2 (i := i) (l := j+1) (by omega)
    rw [add_sub_cancel_right] at this
    omega

/-- **Rule S** (the flip) followed by a kill: three moves lower the junction count. -/
theorem s_step (hn : 5 ≤ n) {c : Vertex n → Colour} (hc : PR n c)
    (h3 : 3 ≤ (jset c).card) {i j : ZMod n} (hi : Jn c i) (hj : Jn c j) (hij : j ≠ i)
    (hfree : ∀ k : ℕ, 1 ≤ k → k < delta i j → ¬ Jn c (i + (k : ZMod n)))
    (hXi : XJ c i) (hXj : XJ c j) :
    ∃ c'', VacancyShortFill.PurePath (graph n) a 3 c c'' ∧
      (jset c'').card + 1 = (jset c).card := by
  obtain ⟨ai1, ai2, ai3, ai4, aj1, aj2, aj3, aj4⟩ := arc_facts hn hc hi hj hij
  have e1 := xj_eq hn hc hXi
  have e2 := xj_eq hn hc hXj
  obtain ⟨z, hzb, hz1, hz2⟩ := exists_z (c b) (c (u (i-1))) (c (u (j+1)))
  obtain ⟨x, y, hxy, hxb, hxz, hyb, hyz⟩ := exists_xy (c b) z hzb
  -- colour facts
  have hPi : c (v (i-1)) ≠ c b := cvb hn hc (i-1)
  have hQi : c (v i) ≠ c b := cvb hn hc i
  have hPQi : c (v (i-1)) ≠ c (v i) := cvv' hn hc i
  have hm1b : c (u (i-1)) ≠ c b := fun h => cuu' hn hc i (h.trans hi.symm)
  have hm1P : c (u (i-1)) ≠ c (v (i-1)) := by simpa using cuv0 hn hc (i-1)
  have hm1Q : c (u (i-1)) ≠ c (v i) := hXi.2.1
  have hPj : c (v (j-1)) ≠ c b := cvb hn hc (j-1)
  have hQj : c (v j) ≠ c b := cvb hn hc j
  have hPQj : c (v (j-1)) ≠ c (v j) := cvv' hn hc j
  have hm2b : c (u (j+1)) ≠ c b := fun h => cuu hn hc j (hj.trans h.symm)
  have hm2Q : c (u (j+1)) ≠ c (v j) := (cvu1 hn hc j).symm
  have hm2P : c (u (j+1)) ≠ c (v (j-1)) := hXj.2.2
  have hseed : c (u (i+1)) = x ∨ c (u (i+1)) = y := by
    rw [e1]; exact seed_col _ _ _ _ _ hm1b hz1 hzb hxy hxb hxz hyb hyz
  have gi := glue_col (c b) (c (v (i-1))) (c (v i)) (c (u (i-1))) z x y hPi hQi hPQi hm1b
    (fun h => hm1P h) (fun h => hm1Q h) hzb hz1 hxy hxb hxz hyb hyz
  have gj := glue_col (c b) (c (v (j-1))) (c (v j)) (c (u (j+1))) z x y hPj hQj hPQj hm2b
    (fun h => hm2P h) (fun h => hm2Q h) hzb hz2 hxy hxb hxz hyb hyz
  have hchain := arc_chain hn hc hi hj hij hxy hxb hyb hfree hseed
  have hseedAct : VacancyShortFill.Active a c x y (u (i+1)) := ⟨by simp, hseed⟩
  have hT := VacancyShortFill.whole_component (graph n) a c x y (u (i+1)) hseedAct
  set T := {w | (VacancyShortFill.pairGraph (graph n) a c x y).Reachable (u (i+1)) w} with hTdef
  have hmem : ∀ w, w ∈ T ↔ InArc i (delta i j) w ∧ (c w = x ∨ c w = y) := by
    intro w
    constructor
    · intro r
      exact ⟨arc_reach hn hc hi hj hxb hyb gi gj ai2 r, (VacancyShortFill.whole_active _ hT r).2⟩
    · rintro ⟨h1, h2⟩
      exact hchain w h1 h2
  set c' := VacancyShortFill.swap c x y T with hc'
  have hc'arc : ∀ w, InArc i (delta i j) w → c' w = Equiv.swap x y (c w) := by
    intro w hw
    by_cases hcw : c w = x ∨ c w = y
    · exact VacancyShortFill.swap_in ((hmem w).mpr ⟨hw, hcw⟩)
    · rw [hc', VacancyShortFill.swap_out (fun h => hcw ((hmem w).mp h).2)]
      push Not at hcw
      exact (Equiv.swap_apply_of_ne_of_ne hcw.1 hcw.2).symm
  have hc'out : ∀ w, ¬ InArc i (delta i j) w → c' w = c w := fun w hw =>
    VacancyShortFill.swap_out (fun h => hw ((hmem w).mp h).1)
  have hstep : VacancyShortFill.KempeStep (graph n) a c c' := ⟨x, y, T, hxy, hT, rfl⟩
  have hpr' : PR n c' := VacancyShortFill.kempe_proper _ hc hstep
  have hjn : ∀ t, Jn c' t ↔ Jn c t := fun t => jn_swap hxb hyb t
  have hjset : jset c' = jset c := by
    ext t; rw [mem_jset, mem_jset]; exact hjn t
  -- R at i
  have Ri : R1 c' i ∨ R2 c' i := by
    have h := flip_J1 (c b) (c (v (i-1))) (c (v i)) (c (u (i-1))) z x y hPi hQi hPQi hm1b
      (fun h => hm1P h) (fun h => hm1Q h) hzb hz1 hxy hxb hxz hyb hyz
    have r1 : c' (u (i+1)) = Equiv.swap x y (c (u (i-1))) := by rw [hc'arc _ ai2, e1]
    have r2 : c' (v i) = Equiv.swap x y (c (v i)) := hc'arc _ ai1
    have r3 : c' (v (i-1)) = c (v (i-1)) := hc'out _ ai3
    have r4 : c' (u (i-1)) = c (u (i-1)) := hc'out _ ai4
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨(hjn i).mpr hi, by rw [r1, r3]; exact h1, by rw [r2, r4]; exact h2⟩
    · right; exact ⟨(hjn i).mpr hi, by rw [r2, r4]; exact h1, by rw [r1, r3]; exact h2⟩
  have Rj : R1 c' j ∨ R2 c' j := by
    have h := flip_J2 (c b) (c (v (j-1))) (c (v j)) (c (u (j+1))) z x y hPj hQj hPQj hm2b
      (fun h => hm2P h) (fun h => hm2Q h) hzb hz2 hxy hxb hxz hyb hyz
    have r1 : c' (v (j-1)) = Equiv.swap x y (c (v (j-1))) := hc'arc _ aj1
    have r2 : c' (u (j-1)) = Equiv.swap x y (c (u (j+1))) := by rw [hc'arc _ aj2, ← e2]
    have r3 : c' (v j) = c (v j) := hc'out _ aj3
    have r4 : c' (u (j+1)) = c (u (j+1)) := hc'out _ aj4
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨(hjn j).mpr hj, by rw [r4, r1]; exact h1, by rw [r2, r3]; exact h2⟩
    · right; exact ⟨(hjn j).mpr hj, by rw [r2, r3]; exact h1, by rw [r4, r1]; exact h2⟩
  have h3' : 3 ≤ (jset c').card := by rw [hjset]; exact h3
  obtain ⟨c'', hp2, hcard⟩ : ∃ c'', VacancyShortFill.PurePath (graph n) a 2 c' c'' ∧
      (jset c'').card + 1 = (jset c').card := by
    rcases l7 hn hpr' h3' hij.symm Ri Rj with h | h
    · exact rn_step hn hpr' h
    · exact rn_step hn hpr' h
  exact ⟨c'', .cons hstep hp2, by rw [← hjset]; exact hcard⟩

end flip

end SimpleGraph.TheoremPPole
