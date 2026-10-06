/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TheoremPPoleMoves

/-!
# Theorem P: rules F and K (free toggle and R-kill)
-/

@[expose] public section
namespace SimpleGraph.TheoremPPole
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

variable {n : ℕ}

/-- A junction one of whose non-`β` colours is absent from its four neighbours. -/
def FreeAt (c : Vertex n → Colour) (i : ZMod n) : Prop :=
  Jn c i ∧ ∃ m, m ≠ c b ∧ m ≠ c (u (i-1)) ∧ m ≠ c (u (i+1)) ∧
    m ≠ c (v (i-1)) ∧ m ≠ c (v i)

/-- Rule F: toggle a free junction. -/
theorem free_step (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c)
    {i : ZMod n} (hf : FreeAt c i) :
    ∃ c', VacancyShortFill.KempeStep (graph n) a c c' ∧
      (jset c').card + 1 = (jset c).card := by
  obtain ⟨hj, m, hmb, hm1, hm2, hm3, hm4⟩ := hf
  obtain ⟨hstep, hself, hother⟩ := single_step hc (w := u i) (by simp)
    (x := c b) (y := m) (fun h => hmb h.symm) hj (by
      intro v hv hva
      rcases (adj_u hn i v).mp hv with rfl | rfl | rfl | rfl | rfl
      · exact (hva rfl).elim
      · exact fun h => hm2 h.symm
      · exact fun h => hm4 h.symm
      · exact fun h => hm3 h.symm
      · exact fun h => hm1 h.symm)
  refine ⟨_, hstep, card_drop (i := i) ?_ hj⟩
  intro j
  have hb : VacancyShortFill.swap c (c b) m {u i} b = c b :=
    hother b (by simp)
  unfold Jn
  rw [hb]
  by_cases hji : j = i
  · subst hji
    rw [hself]
    simp [hmb]
  · rw [hother _ (by simpa using hji)]
    simp [hji]

/-- the unique colour absent from `{β, p, q}` -/
lemma exists_fourth (β p q : Colour) (hp : p ≠ β) (hq : q ≠ β) (hpq : p ≠ q) :
    ∃ m, m ≠ β ∧ m ≠ p ∧ m ≠ q := by
  revert β p q; decide

/-- R1 kill. -/
theorem k_step_R1 (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c)
    {i : ZMod n} (hj : Jn c i)
    (ha2 : c (u (i+1)) = c (v (i-1))) (ha1 : c (u (i-1)) ≠ c (v i))
    (hnd : ¬ (VacancyShortFill.pairGraph (graph n) a c (c (v i)) (c (u (i-1)))).Reachable
      (v i) (u (i-1))) :
    ∃ c'', VacancyShortFill.PurePath (graph n) a 2 c c'' ∧
      (jset c'').card + 1 = (jset c).card := by
  have hβq : c (v i) ≠ c b := cvb hn hc i
  have hβm : c (u (i-1)) ≠ c b := fun h => cuu' hn hc i (h.trans hj.symm)
  have hpq : c (v (i-1)) ≠ c (v i) := cvv' hn hc i
  have hpm : c (u (i-1)) ≠ c (v (i-1)) := by simpa using cuv0 hn hc (i-1)
  have hact : VacancyShortFill.Active a c (c (v i)) (c (u (i-1))) (v i) :=
    ⟨by simp, Or.inl rfl⟩
  have hK := VacancyShortFill.whole_component (graph n) a c (c (v i)) (c (u (i-1))) (v i) hact
  set K := {w | (VacancyShortFill.pairGraph (graph n) a c (c (v i)) (c (u (i-1)))).Reachable
    (v i) w} with hKdef
  set c' := VacancyShortFill.swap c (c (v i)) (c (u (i-1))) K with hc'
  have hstep : VacancyShortFill.KempeStep (graph n) a c c' :=
    ⟨_, _, K, fun h => ha1 h.symm, hK, rfl⟩
  have hvi : c' (v i) = c (u (i-1)) := by
    rw [hc', VacancyShortFill.swap_in (show v i ∈ K from Reachable.refl _)]
    exact Equiv.swap_apply_left _ _
  have hum : c' (u (i-1)) = c (u (i-1)) :=
    VacancyShortFill.swap_out (show u (i-1) ∉ K from hnd)
  have hup : c' (u (i+1)) = c (v (i-1)) := by
    rw [hc', VacancyShortFill.swap_other (by rw [ha2]; exact hpq)
      (by rw [ha2]; exact fun h => hpm h.symm), ha2]
  have hvp : c' (v (i-1)) = c (v (i-1)) :=
    VacancyShortFill.swap_other hpq (fun h => hpm h.symm)
  have hui : c' (u i) = c b := by
    rw [hc', VacancyShortFill.swap_other (by rw [hj]; exact hβq.symm)
      (by rw [hj]; exact hβm.symm), hj]
  have hb' : c' b = c b := swap_b hβq hβm
  have hjset : jset c' = jset c := by
    ext t; rw [mem_jset, mem_jset]; exact jn_swap hβq hβm t
  have hfree : FreeAt c' i := by
    refine ⟨by unfold Jn; rw [hui, hb'], c (v i), by rw [hb']; exact hβq, ?_, ?_, ?_, ?_⟩
    · rw [hum]; exact fun h => ha1 h.symm
    · rw [hup]; exact fun h => hpq h.symm
    · rw [hvp]; exact fun h => hpq h.symm
    · rw [hvi]; exact fun h => ha1 h.symm
  obtain ⟨c'', hstep2, hcard⟩ := free_step hn (VacancyShortFill.kempe_proper _ hc hstep) hfree
  exact ⟨c'', .cons hstep (.cons hstep2 (.nil _)), by rw [← hjset]; exact hcard⟩

/-- R2 kill (mirror image). -/
theorem k_step_R2 (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c)
    {i : ZMod n} (hj : Jn c i)
    (ha1 : c (u (i-1)) = c (v i)) (ha2 : c (u (i+1)) ≠ c (v (i-1)))
    (hnd : ¬ (VacancyShortFill.pairGraph (graph n) a c (c (v (i-1))) (c (u (i+1)))).Reachable
      (v (i-1)) (u (i+1))) :
    ∃ c'', VacancyShortFill.PurePath (graph n) a 2 c c'' ∧
      (jset c'').card + 1 = (jset c).card := by
  have hβp : c (v (i-1)) ≠ c b := cvb hn hc (i-1)
  have hβm : c (u (i+1)) ≠ c b := fun h => cuu hn hc i (hj.trans h.symm)
  have hpq : c (v (i-1)) ≠ c (v i) := cvv' hn hc i
  have hqm : c (u (i+1)) ≠ c (v i) := (cvu1 hn hc i).symm
  have hact : VacancyShortFill.Active a c (c (v (i-1))) (c (u (i+1))) (v (i-1)) :=
    ⟨by simp, Or.inl rfl⟩
  have hK := VacancyShortFill.whole_component (graph n) a c (c (v (i-1))) (c (u (i+1)))
    (v (i-1)) hact
  set K := {w | (VacancyShortFill.pairGraph (graph n) a c (c (v (i-1))) (c (u (i+1)))).Reachable
    (v (i-1)) w} with hKdef
  set c' := VacancyShortFill.swap c (c (v (i-1))) (c (u (i+1))) K with hc'
  have hstep : VacancyShortFill.KempeStep (graph n) a c c' :=
    ⟨_, _, K, fun h => ha2 h.symm, hK, rfl⟩
  have hvp : c' (v (i-1)) = c (u (i+1)) := by
    rw [hc', VacancyShortFill.swap_in (show v (i-1) ∈ K from Reachable.refl _)]
    exact Equiv.swap_apply_left _ _
  have hup : c' (u (i+1)) = c (u (i+1)) :=
    VacancyShortFill.swap_out (show u (i+1) ∉ K from hnd)
  have hum : c' (u (i-1)) = c (v i) := by
    rw [hc', VacancyShortFill.swap_other (by rw [ha1]; exact hpq.symm)
      (by rw [ha1]; exact hqm.symm), ha1]
  have hvi : c' (v i) = c (v i) :=
    VacancyShortFill.swap_other hpq.symm hqm.symm
  have hui : c' (u i) = c b := by
    rw [hc', VacancyShortFill.swap_other (by rw [hj]; exact hβp.symm)
      (by rw [hj]; exact hβm.symm), hj]
  have hb' : c' b = c b := swap_b hβp hβm
  have hjset : jset c' = jset c := by
    ext t; rw [mem_jset, mem_jset]; exact jn_swap hβp hβm t
  have hfree : FreeAt c' i := by
    refine ⟨by unfold Jn; rw [hui, hb'], c (v (i-1)), by rw [hb']; exact hβp, ?_, ?_, ?_, ?_⟩
    · rw [hum]; exact hpq
    · rw [hup]; exact fun h => ha2 h.symm
    · rw [hvp]; exact fun h => ha2 h.symm
    · rw [hvi]; exact hpq
  obtain ⟨c'', hstep2, hcard⟩ := free_step hn (VacancyShortFill.kempe_proper _ hc hstep) hfree
  exact ⟨c'', .cons hstep (.cons hstep2 (.nil _)), by rw [← hjset]; exact hcard⟩

end SimpleGraph.TheoremPPole
