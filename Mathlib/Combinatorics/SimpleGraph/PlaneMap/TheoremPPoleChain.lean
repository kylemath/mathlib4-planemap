/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TheoremPPoleDegen

/-!
# Theorem P: the chain lemma on a junction-free segment
-/

@[expose] public section
namespace SimpleGraph.TheoremPPole
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

variable {n : ℕ}

/-- Window lemma: of three pairwise distinct non-`β` colours, one in a 2-set
`{x,y}` forces another of the previous two into it. -/
lemma window (β x y p q r : Colour) (hxy : x ≠ y) (hxb : x ≠ β) (hyb : y ≠ β)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) (hpb : p ≠ β) (hqb : q ≠ β)
    (hr : r = x ∨ r = y) : (p = x ∨ p = y) ∨ (q = x ∨ q = y) := by
  have := p.isLt; have := q.isLt; have := r.isLt; have := x.isLt; have := y.isLt
  have := β.isLt
  simp only [Fin.ext_iff, ne_eq] at *
  omega

/-- Extending a reachable vertex along an active edge. -/
lemma reach_step {c : Vertex n → Colour} {x y : Colour} {s w w' : Vertex n}
    (hr : (VacancyShortFill.pairGraph (graph n) a c x y).Reachable s w)
    (e : (graph n).Adj w w') (hw : w ≠ a) (hw' : w' ≠ a)
    (cw : c w = x ∨ c w = y) (cw' : c w' = x ∨ c w' = y) :
    (VacancyShortFill.pairGraph (graph n) a c x y).Reachable s w' :=
  hr.trans (SimpleGraph.Adj.reachable ⟨e, ⟨hw, cw⟩, ⟨hw', cw'⟩⟩)

/-- Reachability from the seed, for the two vertices at ring index `l`. -/
def ChainAt (c : Vertex n → Colour) (x y : Colour) (s : Vertex n) (l : ZMod n) : Prop :=
  ((c (u l) = x ∨ c (u l) = y) →
      (VacancyShortFill.pairGraph (graph n) a c x y).Reachable s (u l)) ∧
  ((c (v l) = x ∨ c (v l) = y) →
      (VacancyShortFill.pairGraph (graph n) a c x y).Reachable s (v l))

theorem chain_step (hn : 5 ≤ n) {c : Vertex n → Colour} (hc : PR n c) {x y : Colour}
    (hxy : x ≠ y) (hx : x ≠ c b) (hy : y ≠ c b) {s : Vertex n} {l : ZMod n}
    (hl : ¬ Jn c l) (hl1 : ¬ Jn c (l+1)) (ih : ChainAt c x y s l) :
    ChainAt c x y s (l+1) := by
  have hβl : c (u l) ≠ c b := hl
  have hβl1 : c (u (l+1)) ≠ c b := hl1
  have hU : (c (u (l+1)) = x ∨ c (u (l+1)) = y) →
      (VacancyShortFill.pairGraph (graph n) a c x y).Reachable s (u (l+1)) := by
    intro hr
    rcases window (c b) x y (c (u l)) (c (v l)) (c (u (l+1))) hxy hx hy
      (cuv0 hn hc l) (cvu1 hn hc l) (cuu hn hc l) hβl (cvb hn hc l) hr with h | h
    · exact reach_step (ih.1 h) (adj_uu' hn l) (by simp) (by simp) h hr
    · exact reach_step (ih.2 h) (adj_vu1 hn l) (by simp) (by simp) h hr
  refine ⟨hU, fun hr => ?_⟩
  rcases window (c b) x y (c (v l)) (c (u (l+1))) (c (v (l+1))) hxy hx hy
    (cvu1 hn hc l) (cuv0 hn hc (l+1)) (cvv hn hc l) (cvb hn hc l) hβl1 hr with h | h
  · exact reach_step (ih.2 h) (adj_vv' hn l) (by simp) (by simp) h hr
  · exact reach_step (hU h) (adj_uv0 hn (l+1)) (by simp) (by simp) h hr

section
variable [NeZero n]

lemma delta_add (hn : 2 ≤ n) (i : ZMod n) (k : ℕ) (hk : k < n) :
    delta i (i + (k : ZMod n)) = k := by
  unfold delta
  rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

lemma eq_add_delta (i l : ZMod n) : l = i + ((delta i l : ℕ) : ZMod n) := by
  unfold delta
  rw [ZMod.natCast_zmod_val]; ring

/-- Chain lemma: on a junction-free segment, every vertex of the arc coloured in
`{x,y}` is reachable from the seed `u_{i+1}` in the `{x,y}` pair graph. -/
theorem arc_chain (hn : 5 ≤ n) {c : Vertex n → Colour} (hc : PR n c) {i j : ZMod n}
    (hi : Jn c i) (hj : Jn c j) (hij : j ≠ i) {x y : Colour}
    (hxy : x ≠ y) (hx : x ≠ c b) (hy : y ≠ c b)
    (hfree : ∀ k : ℕ, 1 ≤ k → k < delta i j → ¬ Jn c (i + (k : ZMod n)))
    (hseed : c (u (i+1)) = x ∨ c (u (i+1)) = y) :
    ∀ w, InArc i (delta i j) w → (c w = x ∨ c w = y) →
      (VacancyShortFill.pairGraph (graph n) a c x y).Reachable (u (i+1)) w := by
  have hd2 := two_le_delta hn hc hi hj hij
  have hdn := delta_lt i j
  have hn2 : 2 ≤ n := by omega
  have base : ChainAt c x y (u (i+1)) (i+1) := by
    refine ⟨fun _ => Reachable.refl _, fun hr => ?_⟩
    exact reach_step (Reachable.refl _) (adj_uv0 hn (i+1)) (by simp) (by simp) hseed hr
  have hall : ∀ k : ℕ, 1 ≤ k → k < delta i j →
      ChainAt c x y (u (i+1)) (i + (k : ZMod n)) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; simpa using base
    | succ k hk ih =>
      intro hlt
      have h1 := ih (by omega)
      have h2 := hfree k hk (by omega)
      have h3 := hfree (k+1) (by omega) hlt
      have e : i + ((k+1 : ℕ) : ZMod n) = (i + (k : ZMod n)) + 1 := by push_cast; ring
      rw [e] at h3 ⊢
      exact chain_step hn hc hxy hx hy h2 h3 h1
  intro w hw cw
  cases w with
  | a => exact absurd hw (by simp [InArc])
  | b => exact absurd hw (by simp [InArc])
  | u l =>
    obtain ⟨h1, h2⟩ := hw
    have := (hall (delta i l) h1 h2).1
    rw [← eq_add_delta] at this
    exact this cw
  | v l =>
    have h2 : delta i l < delta i j := hw
    by_cases h0 : delta i l = 0
    · have := delta_zero.mp h0
      subst this
      exact reach_step (Reachable.refl _) (adj_vu1 hn l).symm (by simp) (by simp) hseed cw
    · have := (hall (delta i l) (by omega) h2).2
      rw [← eq_add_delta] at this
      exact this cw

end

end SimpleGraph.TheoremPPole
