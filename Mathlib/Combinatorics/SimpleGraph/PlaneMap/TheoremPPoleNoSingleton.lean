/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TheoremPPoleFlip

/-!
# Theorem P: the no-singleton pole case of the belt theorem, without Florek

Let `c` be a proper colouring of `G_n - a` (the hole sits at the pole `a`).  Then at most
`3 (n₀ - 2) + n` Kempe swaps (with the hole fixed at `a`) reach a colouring whose ring uses
some colour at most once: a fill (the colour is absent from `N(a)`), or a singleton.
Here `n₀` is the number of ring vertices coloured `c b`.

The strategy is that of `pole-hole-noflorek.md` §5: T1 (zero interior vertices of a colour
with at most one exposed vertex), F (toggle a free junction), K (kill a non-degenerate R
junction), S (flip a segment between consecutive X junctions, then K).  Each round lowers `n₀`
by one with at most 3 swaps.
-/

@[expose] public section
namespace SimpleGraph.TheoremPPole
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

variable {n : ℕ}

lemma purePath_append {c d e : Vertex n → Colour} {k l : ℕ}
    (p : VacancyShortFill.PurePath (graph n) a k c d)
    (q : VacancyShortFill.PurePath (graph n) a l d e) :
    VacancyShortFill.PurePath (graph n) a (k + l) c e := by
  induction p with
  | nil => simpa using q
  | @cons m c' d' e' step rest ih =>
    have := VacancyShortFill.PurePath.cons step (ih q)
    have e : m + l + 1 = m + 1 + l := by omega
    rwa [e] at this

/-- One round: at most three swaps lower the junction count by one. -/
theorem round (hn : 5 ≤ n) [NeZero n] {c : Vertex n → Colour} (hc : PR n c)
    (h3 : 3 ≤ (jset c).card)
    (hE : ∀ x, x ≠ c b → ∃ i j, i ≠ j ∧ Exposed c x i ∧ Exposed c x j) :
    ∃ k, k ≤ 3 ∧ ∃ c'', VacancyShortFill.PurePath (graph n) a k c c'' ∧
      (jset c'').card + 1 = (jset c).card := by
  by_cases hF : ∃ t, FreeAt c t
  · obtain ⟨t, ht⟩ := hF
    obtain ⟨c', hs, hcard⟩ := free_step hn hc ht
    exact ⟨1, by omega, c', .cons hs (.nil _), hcard⟩
  push Not at hF
  by_cases hK : ∃ t, RN c t
  · obtain ⟨t, ht⟩ := hK
    obtain ⟨c', hp, hcard⟩ := rn_step hn hc ht
    exact ⟨2, by omega, c', hp, hcard⟩
  push Not at hK
  by_cases hR : ∃ t, R1 c t ∨ R2 c t
  · exfalso
    obtain ⟨x, hx, hno⟩ := l8 hn hc h3 hF (fun t _ => hK t) hR
    obtain ⟨i, j, hij, hi, hj⟩ := hE x hx
    exact hno i hi
  push Not at hR
  obtain ⟨i, j, hi, hj, hji, hfree⟩ := exists_consecutive (by omega : 2 ≤ n)
    (by omega : 2 ≤ (jset c).card)
  have hXi : XJ c i := classify_X hn hc hi (hF i) (fun h => (hR i).1 h) (fun h => (hR i).2 h)
  have hXj : XJ c j := classify_X hn hc hj (hF j) (fun h => (hR j).1 h) (fun h => (hR j).2 h)
  obtain ⟨c', hp, hcard⟩ := s_step hn hc h3 hi hj hji hfree hXi hXj
  exact ⟨3, le_rfl, c', hp, hcard⟩

/-- The induction on the number of junctions. -/
theorem main_induction (hn : 5 ≤ n) [NeZero n] :
    ∀ (N : ℕ) (c : Vertex n → Colour), PR n c → (jset c).card ≤ N + 2 →
    ∃ k, k ≤ 3 * N + n ∧ ∃ d, VacancyShortFill.PurePath (graph n) a k c d ∧ Good d := by
  intro N
  induction N with
  | zero =>
    intro c hc hcard
    by_cases hE : ∀ x, x ≠ c b → ∃ i j, i ≠ j ∧ Exposed c x i ∧ Exposed c x j
    · exfalso
      have := three_le_of_exposed hE
      omega
    · push Not at hE
      obtain ⟨x, hx, hxe⟩ := hE
      obtain ⟨k, hk, d, hd, hg⟩ := t1 hn n c hc (fun h => hx h.symm)
        (fun i j hi hj => by_contra fun hij => hxe i j hij hi hj)
        (by
          calc _ ≤ (Finset.univ : Finset (ZMod n)).card := Finset.card_le_univ _
            _ = n := by simp)
      exact ⟨k, by omega, d, hd, hg⟩
  | succ N ih =>
    intro c hc hcard
    by_cases hE : ∀ x, x ≠ c b → ∃ i j, i ≠ j ∧ Exposed c x i ∧ Exposed c x j
    · have h3 := three_le_of_exposed hE
      by_cases hsmall : (jset c).card ≤ N + 2
      · obtain ⟨k, hk, d, hd, hg⟩ := ih c hc hsmall
        exact ⟨k, by omega, d, hd, hg⟩
      · obtain ⟨k, hk, c'', hp, hc''⟩ := round hn hc h3 hE
        have hpr := hp.proper _ hc
        obtain ⟨k', hk', d, hd, hg⟩ := ih c'' hpr (by omega)
        exact ⟨k + k', by omega, d, purePath_append hp hd, hg⟩
    · push Not at hE
      obtain ⟨x, hx, hxe⟩ := hE
      obtain ⟨k, hk, d, hd, hg⟩ := t1 hn n c hc (fun h => hx h.symm)
        (fun i j hi hj => by_contra fun hij => hxe i j hij hi hj)
        (by
          calc _ ≤ (Finset.univ : Finset (ZMod n)).card := Finset.card_le_univ _
            _ = n := by simp)
      exact ⟨k, by omega, d, hd, hg⟩

/-- **Theorem P** (pole holes without Florek).  For `n ≥ 5` and every proper colouring `c`
of `G_n - a`, at most `3 (n₀ - 2) + n` Kempe swaps with the hole fixed at `a` reach a
colouring whose ring uses some colour at most once.  (`n₀` is the number of ring
vertices of colour `c b`.) -/
theorem theoremP (hn : 5 ≤ n) [NeZero n] (c : Vertex n → Colour) (hc : PR n c) :
    ∃ k, k ≤ 3 * ((jset c).card - 2) + n ∧
      ∃ d, VacancyShortFill.PurePath (graph n) a k c d ∧ Good d :=
  main_induction hn ((jset c).card - 2) c hc (by omega)

lemma adj_a_iff {v : Vertex n} : (graph n).Adj a v ↔ ∃ i, v = u i := by
  cases v <;> simp [graph, TwoPoleBelt.edge]

/-- Theorem P in the shape of the hand statement: from a start in which every colour occurs
at least twice on the ring, at most `3 (n₀ - 2) + n` swaps reach a *fill* (a colour absent
from `N(a)`, so the hole can be filled) or a *singleton* (a colour occurring exactly once on
the ring). -/
theorem theoremP_fill_or_singleton (hn : 5 ≤ n) [NeZero n] (c : Vertex n → Colour)
    (hc : PR n c)
    (_htwice : ∀ x : Colour, ∃ i j : ZMod n, i ≠ j ∧ c (u i) = x ∧ c (u j) = x) :
    ∃ k, k ≤ 3 * ((jset c).card - 2) + n ∧ ∃ d, PR n d ∧
      VacancyShortFill.PurePath (graph n) a k c d ∧
      (VacancyShortFill.Target (graph n) a d ∨
        ∃ x i, d (u i) = x ∧ ∀ j, d (u j) = x → j = i) := by
  obtain ⟨k, hk, d, hd, x, hx⟩ := theoremP hn c hc
  refine ⟨k, hk, d, hd.proper _ hc, hd, ?_⟩
  by_cases hex : ∃ i, d (u i) = x
  · obtain ⟨i, hi⟩ := hex
    exact Or.inr ⟨x, i, hi, fun j hj => hx j i hj hi⟩
  · push Not at hex
    refine Or.inl ⟨x, fun v hv => ?_⟩
    obtain ⟨i, rfl⟩ := adj_a_iff.mp hv
    exact hex i

end SimpleGraph.TheoremPPole
