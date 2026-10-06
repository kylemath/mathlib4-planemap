/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TheoremPPoleCut

/-!
# Theorem P: junction types, degeneracy lemma, L7 and L8
-/

@[expose] public section
namespace SimpleGraph.TheoremPPole
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

variable {n : ℕ}

/-- The glue edge `v_{j-1} v_j` is active for the pair `{s,t}`. -/
def Glue (c : Vertex n → Colour) (j : ZMod n) (s t : Colour) : Prop :=
  (c (v (j-1)) = s ∨ c (v (j-1)) = t) ∧ (c (v j) = s ∨ c (v j) = t)

/-- R1 junction: ring neighbours `(m, p)`. -/
def R1 (c : Vertex n → Colour) (i : ZMod n) : Prop :=
  Jn c i ∧ c (u (i+1)) = c (v (i-1)) ∧ c (u (i-1)) ≠ c (v i)
/-- R2 junction: ring neighbours `(q, m)`. -/
def R2 (c : Vertex n → Colour) (i : ZMod n) : Prop :=
  Jn c i ∧ c (u (i-1)) = c (v i) ∧ c (u (i+1)) ≠ c (v (i-1))
/-- X junction: ring neighbours `(m, m)`. -/
def XJ (c : Vertex n → Colour) (i : ZMod n) : Prop :=
  Jn c i ∧ c (u (i-1)) ≠ c (v i) ∧ c (u (i+1)) ≠ c (v (i-1))

/-- Non-degeneracy of R1 / R2 (the kill component misses the far ring neighbour). -/
def ND1 (c : Vertex n → Colour) (i : ZMod n) : Prop :=
  ¬ (VacancyShortFill.pairGraph (graph n) a c (c (v i)) (c (u (i-1)))).Reachable
      (v i) (u (i-1))
def ND2 (c : Vertex n → Colour) (i : ZMod n) : Prop :=
  ¬ (VacancyShortFill.pairGraph (graph n) a c (c (v (i-1))) (c (u (i+1)))).Reachable
      (v (i-1)) (u (i+1))

/-- A non-degenerate R junction. -/
def RN (c : Vertex n → Colour) (i : ZMod n) : Prop :=
  (R1 c i ∧ ND1 c i) ∨ (R2 c i ∧ ND2 c i)

section degen
variable [NeZero n]

lemma delta_self (i : ZMod n) : delta i i = 0 := delta_zero.mpr rfl

lemma delta_prev (hn : 2 ≤ n) (i : ZMod n) : delta i (i-1) + 1 = n := by
  have h1 := delta_lt i (i-1)
  by_contra hh
  have h2 := delta_succ hn (i := i) (l := i-1) (by omega)
  rw [sub_add_cancel, delta_self] at h2
  omega

lemma delta_next (hn : 2 ≤ n) (i : ZMod n) : delta i (i+1) = 1 := by
  rw [delta_succ hn (by rw [delta_self]; omega), delta_self]

lemma two_le_delta (hn : 5 ≤ n) {c : Vertex n → Colour} (hc : PR n c) {i j : ZMod n}
    (hi : Jn c i) (hj : Jn c j) (hij : j ≠ i) : 2 ≤ delta i j := by
  have h0 : delta i j ≠ 0 := fun h => hij (delta_zero.mp h)
  by_contra hh
  have h1 : delta i j = delta i (i+1) := by rw [delta_next (by omega)]; omega
  have := delta_inj h1
  subst this
  exact cuu hn hc i (hi.trans hj.symm)

end degen

section
variable [NeZero n]

/-- Degeneracy lemma, R1. -/
theorem degen_R1 (hn : 5 ≤ n) {c : Vertex n → Colour} (hc : PR n c) {i j : ZMod n}
    (hR : R1 c i) (hj : Jn c j) (hij : j ≠ i)
    (hdeg : ¬ ND1 c i) : Glue c j (c (v i)) (c (u (i-1))) := by
  obtain ⟨hi, ha2, ha1⟩ := hR
  by_contra hg
  apply hdeg
  intro r
  have hβq : c (v i) ≠ c b := cvb hn hc i
  have hβm : c (u (i-1)) ≠ c b := fun h => cuu' hn hc i (h.trans hi.symm)
  have hpq : c (v (i-1)) ≠ c (v i) := cvv' hn hc i
  have hpm : c (u (i-1)) ≠ c (v (i-1)) := by simpa using cuv0 hn hc (i-1)
  have gi : ¬ Glue c i (c (v i)) (c (u (i-1))) := by
    rintro ⟨h1, _⟩
    rcases h1 with h | h
    · exact hpq h
    · exact hpm h.symm
  have hin : InArc i (delta i j) (v i) := by
    change delta i i < delta i j
    rw [delta_self]; have := two_le_delta hn hc hi hj hij; omega
  have := arc_reach hn hc hi hj hβq hβm gi hg hin r
  change 1 ≤ delta i (i-1) ∧ delta i (i-1) < delta i j at this
  have h1 := delta_prev (by omega) i
  have h2 := delta_lt i j
  omega

/-- Degeneracy lemma, R2. -/
theorem degen_R2 (hn : 5 ≤ n) {c : Vertex n → Colour} (hc : PR n c) {i j : ZMod n}
    (hR : R2 c i) (hj : Jn c j) (hij : j ≠ i)
    (hdeg : ¬ ND2 c i) : Glue c j (c (v (i-1))) (c (u (i+1))) := by
  obtain ⟨hi, ha1, ha2⟩ := hR
  by_contra hg
  apply hdeg
  intro r
  have hβp : c (v (i-1)) ≠ c b := cvb hn hc (i-1)
  have hβm : c (u (i+1)) ≠ c b := fun h => cuu hn hc i (hi.trans h.symm)
  have hpq : c (v (i-1)) ≠ c (v i) := cvv' hn hc i
  have hqm : c (u (i+1)) ≠ c (v i) := (cvu1 hn hc i).symm
  have gi : ¬ Glue c i (c (v (i-1))) (c (u (i+1))) := by
    rintro ⟨_, h1⟩
    rcases h1 with h | h
    · exact hpq h.symm
    · exact hqm h.symm
  have h2 := two_le_delta hn hc hi hj hij
  have hin : InArc i (delta i j) (u (i+1)) := by
    change 1 ≤ delta i (i+1) ∧ delta i (i+1) < delta i j
    rw [delta_next (by omega)]; omega
  have := arc_reach hn hc hi hj hβp hβm gi hg hin r.symm
  change delta i (i-1) < delta i j at this
  have h1 := delta_prev (by omega) i
  have h3 := delta_lt i j
  omega

end

/-- Pure colour core of L7. -/
lemma l7_core (si ti sj tj Pi Qi Pj Qj Pk Qk : Colour)
    (hti1 : ti ≠ Pi) (hti2 : ti ≠ Qi) (hPQi : Pi ≠ Qi) (hPQk : Pk ≠ Qk)
    (gk_i : (Pk = si ∨ Pk = ti) ∧ (Qk = si ∨ Qk = ti))
    (gk_j : (Pk = sj ∨ Pk = tj) ∧ (Qk = sj ∨ Qk = tj))
    (gi_j : (Pi = sj ∨ Pi = tj) ∧ (Qi = sj ∨ Qi = tj)) : False := by
  simp only [Fin.ext_iff, ne_eq] at *
  omega

/-- Third junction. -/
lemma exists_third [NeZero n] {c : Vertex n → Colour} (h3 : 3 ≤ (jset c).card)
    {i j : ZMod n} (hi : Jn c i) (hj : Jn c j) (hij : i ≠ j) :
    ∃ k, Jn c k ∧ k ≠ i ∧ k ≠ j := by
  have hi' : i ∈ jset c := mem_jset.mpr hi
  have hj' : j ∈ (jset c).erase i := Finset.mem_erase.mpr ⟨hij.symm, mem_jset.mpr hj⟩
  have hcard : (((jset c).erase i).erase j).card = (jset c).card - 2 := by
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi']; omega
  have : (((jset c).erase i).erase j).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨k, hk⟩ := this
  simp only [Finset.mem_erase] at hk
  exact ⟨k, mem_jset.mp hk.2.2, hk.2.1, hk.1⟩

/-- L7: with a third junction, two R junctions are not both degenerate. -/
theorem l7 (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c)
    (h3 : 3 ≤ (jset c).card) {i j : ZMod n} (hij : i ≠ j)
    (hRi : R1 c i ∨ R2 c i) (hRj : R1 c j ∨ R2 c j) : RN c i ∨ RN c j := by
  have hi : Jn c i := by rcases hRi with h | h <;> exact h.1
  have hj : Jn c j := by rcases hRj with h | h <;> exact h.1
  obtain ⟨k, hk, hki, hkj⟩ := exists_third h3 hi hj hij
  by_contra hh
  push Not at hh
  obtain ⟨hni, hnj⟩ := hh
  have deg : ∀ t, (R1 c t ∨ R2 c t) → ¬ RN c t →
      ∃ s t', (∀ m, Jn c m → m ≠ t → Glue c m s t') ∧ t' ≠ c (v (t-1)) ∧ t' ≠ c (v t) := by
    intro t hR hn'
    rcases hR with h | h
    · exact ⟨_, _, fun m hm hmt => degen_R1 hn hc h hm hmt (fun hd => hn' (Or.inl ⟨h, hd⟩)),
        by simpa using (cuv0 hn hc (t-1)), h.2.2⟩
    · exact ⟨_, _, fun m hm hmt => degen_R2 hn hc h hm hmt (fun hd => hn' (Or.inr ⟨h, hd⟩)),
        h.2.2, (cvu1 hn hc t).symm⟩
  obtain ⟨si, ti, gi, hti1, hti2⟩ := deg i hRi hni
  obtain ⟨sj, tj, gj, _, _⟩ := deg j hRj hnj
  exact l7_core si ti sj tj (c (v (i-1))) (c (v i)) (c (v (j-1))) (c (v j))
    (c (v (k-1))) (c (v k)) hti1 hti2 (cvv' hn hc i) (cvv' hn hc k)
    (gi k hk hki) (gj k hk hkj) (gj i hi hij)

/-- A non-free, non-R junction is of type X. -/
lemma classify_X (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c) {j : ZMod n}
    (hj : Jn c j) (hf : ¬ FreeAt c j) (h1 : ¬ R1 c j) (h2 : ¬ R2 c j) : XJ c j := by
  have hPQ := cvv' hn hc j
  have hβP : c (v (j-1)) ≠ c b := cvb hn hc (j-1)
  have hβQ : c (v j) ≠ c b := cvb hn hc j
  have hA1 : c (u (j-1)) ≠ c (v (j-1)) := by simpa using cuv0 hn hc (j-1)
  have hA2 : c (u (j+1)) ≠ c (v j) := (cvu1 hn hc j).symm
  have hA1b : c (u (j-1)) ≠ c b := fun h => cuu' hn hc j (h.trans hj.symm)
  have hA2b : c (u (j+1)) ≠ c b := fun h => cuu hn hc j (hj.trans h.symm)
  have hnf : ¬ (c (u (j-1)) = c (v j) ∧ c (u (j+1)) = c (v (j-1))) := by
    rintro ⟨e1, e2⟩
    obtain ⟨m, hm1, hm2, hm3⟩ := exists_fourth (c b) (c (v (j-1))) (c (v j)) hβP hβQ hPQ
    exact hf ⟨hj, m, hm1, by rw [e1]; exact hm3, by rw [e2]; exact hm2, hm2, hm3⟩
  unfold R1 at h1
  unfold R2 at h2
  refine ⟨hj, ?_, ?_⟩
  · intro h
    apply hnf ⟨h, ?_⟩
    by_contra hh
    exact h2 ⟨hj, h, hh⟩
  · intro h
    by_cases hq : c (u (j-1)) = c (v j)
    · exact hnf ⟨hq, h⟩
    · exact h1 ⟨hj, h, hq⟩

/-- Exposed vertices come from a junction on one side. -/
lemma exposed_cases {c : Vertex n → Colour} {x : Colour} {t : ZMod n} (h : Exposed c x t) :
    ∃ k, Jn c k ∧ (c (u (k+1)) = x ∨ c (u (k-1)) = x) := by
  obtain ⟨hx, h | h⟩ := h
  · exact ⟨t-1, h, Or.inl (by simpa using hx)⟩
  · exact ⟨t+1, h, Or.inr (by simpa using hx)⟩

/-- L8: if all R junctions are degenerate and there is no free junction, a colour is
never exposed (so rule T1 applies). -/
theorem l8 (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c)
    (h3 : 3 ≤ (jset c).card) (hnofree : ∀ t, ¬ FreeAt c t)
    (hdeg : ∀ t, (R1 c t ∨ R2 c t) → ¬ RN c t) (hex : ∃ t, R1 c t ∨ R2 c t) :
    ∃ x, x ≠ c b ∧ ∀ t, ¬ Exposed c x t := by
  obtain ⟨i, hRi⟩ := hex
  have hi : Jn c i := by rcases hRi with h | h <;> exact h.1
  -- every other junction is of type X
  have hX : ∀ j, Jn c j → j ≠ i → XJ c j := by
    intro j hj hji
    apply classify_X hn hc hj (hnofree j)
    · intro h1
      rcases l7 hn hc h3 hji (Or.inl h1) hRi with h | h
      · exact hdeg j (Or.inl h1) h
      · exact hdeg i hRi h
    · intro h2
      rcases l7 hn hc h3 hji (Or.inr h2) hRi with h | h
      · exact hdeg j (Or.inr h2) h
      · exact hdeg i hRi h
  have hPQ : ∀ t, c (v (t-1)) ≠ c (v t) := fun t => cvv' hn hc t
  have hA1 : ∀ t, c (u (t-1)) ≠ c (v (t-1)) := fun t => by simpa using cuv0 hn hc (t-1)
  have hA2 : ∀ t, c (u (t+1)) ≠ c (v t) := fun t => (cvu1 hn hc t).symm
  rcases hRi with hR | hR
  · refine ⟨c (v i), cvb hn hc i, fun t ht => ?_⟩
    obtain ⟨k, hk, hk'⟩ := exposed_cases ht
    have hd : ¬ ND1 c i := fun h => hdeg i (Or.inl hR) (Or.inl ⟨hR, h⟩)
    by_cases hki : k = i
    · subst hki
      obtain ⟨_, e2, e1⟩ := hR
      have := hPQ k
      simp only [Fin.ext_iff, ne_eq] at *
      omega
    · obtain ⟨_, x1, x2⟩ := hX k hk hki
      have hg := degen_R1 hn hc hR hk hki hd
      obtain ⟨g1, g2⟩ := hg
      have := hPQ k
      have := hA1 k
      have := hA2 k
      simp only [Fin.ext_iff, ne_eq] at *
      omega
  · refine ⟨c (v (i-1)), cvb hn hc (i-1), fun t ht => ?_⟩
    obtain ⟨k, hk, hk'⟩ := exposed_cases ht
    have hd : ¬ ND2 c i := fun h => hdeg i (Or.inr hR) (Or.inr ⟨hR, h⟩)
    by_cases hki : k = i
    · subst hki
      obtain ⟨_, e1, e2⟩ := hR
      have := hPQ k
      simp only [Fin.ext_iff, ne_eq] at *
      omega
    · obtain ⟨_, x1, x2⟩ := hX k hk hki
      have hg := degen_R2 hn hc hR hk hki hd
      obtain ⟨g1, g2⟩ := hg
      have := hPQ k
      have := hA1 k
      have := hA2 k
      simp only [Fin.ext_iff, ne_eq] at *
      omega

end SimpleGraph.TheoremPPole
