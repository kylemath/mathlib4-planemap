/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyThreeMoveObstruction

/-!
# Lemma L4: tightening the three-move obstruction

Setting (all moves are the actual moves of `VacancyShortFill`).  `c` is proper off
the hole `h`, `u` is a uniquely coloured neighbour of `h` (colour `σ = c u`), and
`t = slide h u c` is the slid state at hole `u`.  The first of the two remaining
Kempe swaps of a three-move mixed fill is a whole `{σ,ρ}`-component `S` of `t`
(L3(b) says one of its two colours is `σ`).

* `l4a`: if `h ∉ S` (and no pure fill of length 3 exists) then
  `S` misses `N(h)`, `S` contains a `ρ`-neighbour of `u`, the `{σ,ρ}`-component `J` of
  `u` in `G - h` under `c` contains a `ρ`-neighbour of `h`, contains `S`, and `u` has a
  `ρ`-neighbour `y ∉ S` in `h`'s `{σ,ρ}`-component of `t`, joined in `t` to a
  `ρ`-neighbour of `h`.
* `l4b`: if `h ∈ S` and `u` has no `ρ`-neighbour in `S`, there is a pure fill of length
  `r`, where `r` is the number of `{σ,ρ}`-components (of `G - h` under `c`) that contain
  a `ρ`-neighbour of `h`; and `r ≤ m_ρ`, the number of `ρ`-neighbours of `h`.
* `l4c`: the corollary: if no pure fill of length `max 3 m_ρ` exists, `u` has a
  `ρ`-neighbour in the `{σ,ρ}`-component of `h` in `t`, for every decomposition.
-/

@[expose] public section
namespace SimpleGraph.VacancyLemmaL4
open VacancySlide VacancyShortFill VacancyThreeMoveObstruction
variable {V C : Type*} [DecidableEq V] [DecidableEq C] (G : SimpleGraph V)

/-! ### Basic transfer between the pair graphs of `c` at `h` and of `t` at `u` -/

lemma active_t {h u : V} {c : V → C} {a b : C} {v : V} (hvu : v ≠ u) (hvh : v ≠ h)
    (hv : c v = a ∨ c v = b) : Active u (slide h u c) a b v :=
  ⟨hvu, by rw [slide_away h u c hvh]; exact hv⟩

lemma active_s {h : V} {c : V → C} {a b : C} {v : V} (hvh : v ≠ h)
    (hv : c v = a ∨ c v = b) : Active h c a b v := ⟨hvh, hv⟩

lemma active_t_colour {h u : V} {c : V → C} {a b : C} {v : V} (hvh : v ≠ h)
    (hv : Active u (slide h u c) a b v) : c v = a ∨ c v = b := by
  have := hv.2
  rwa [slide_away h u c hvh] at this

omit [DecidableEq C] in
/-- Elements of a whole component are `t`-reachable from each other. -/
lemma whole_reach {h : V} {c : V → C} {a b : C} {S : Set V}
    (hS : Whole G h c a b S) {v w : V} (hv : v ∈ S) (hw : w ∈ S) :
    (pairGraph G h c a b).Reachable v w := by
  obtain ⟨s, _, hmem⟩ := hS
  exact ((hmem v).mp hv).symm.trans ((hmem w).mp hw)

omit [DecidableEq C] in
lemma whole_mem_of_reach {h : V} {c : V → C} {a b : C} {S : Set V}
    (hS : Whole G h c a b S) {v w : V} (hv : v ∈ S)
    (r : (pairGraph G h c a b).Reachable v w) : w ∈ S := by
  obtain ⟨s, _, hmem⟩ := hS
  exact (hmem w).mpr (((hmem v).mp hv).trans r)

/-- A `t`-walk starting in `S ∌ h` is a walk of the original pair graph at `h`. -/
lemma reach_t_to_s {h u : V} {c : V → C} {a b : C} {S : Set V}
    (hS : Whole G u (slide h u c) a b S) (hh : h ∉ S) {p q : V}
    (w : (pairGraph G u (slide h u c) a b).Walk p q) (hp : p ∈ S) :
    (pairGraph G h c a b).Reachable p q := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons p p' q e w ih =>
    have hp' : p' ∈ S := whole_closed G hS hp e.1 e.2.2
    have hph : p ≠ h := fun h' => hh (h' ▸ hp)
    have hp'h : p' ≠ h := fun h' => hh (h' ▸ hp')
    have edge : (pairGraph G h c a b).Adj p p' :=
      ⟨e.1, active_s hph (active_t_colour hph e.2.1),
        active_s hp'h (active_t_colour hp'h e.2.2)⟩
    exact edge.reachable.trans (ih hp')

/-! ### Splitting a `u`-walk at its last visit to `u` -/

lemma split_aux {h u : V} {c : V → C} {ρ : C} (hc : ProperOff G h c) (hu : u ≠ h)
    (hρ : c u ≠ ρ) {x : V} (hx : c x = ρ) {p : V}
    (w : (pairGraph G h c (c u) ρ).Walk p x) :
    (p ≠ u ∧ (pairGraph G u (slide h u c) (c u) ρ).Reachable p x) ∨
    ∃ y, G.Adj u y ∧ c y = ρ ∧ y ≠ h ∧
      (pairGraph G u (slide h u c) (c u) ρ).Reachable y x := by
  induction w with
  | nil =>
    left
    refine ⟨fun hp => hρ ?_, Reachable.refl _⟩
    rw [← hp]; exact hx
  | @cons p q r e w ih =>
    have ih := ih hx
    have hph : p ≠ h := e.2.1.1
    have hqh : q ≠ h := e.2.2.1
    by_cases hq : q = u
    · right
      rcases ih with ⟨hne, _⟩ | h2
      · exact (hne hq).elim
      · exact h2
    · rcases ih with ⟨_, hr⟩ | h2
      · by_cases hp : p = u
        · right
          refine ⟨q, ?_, ?_, hqh, hr⟩
          · rw [← hp]; exact e.1
          · rcases e.2.2.2 with h1 | h1
            · exfalso
              have := hc e.1 hph hqh
              rw [hp] at this
              exact this h1.symm
            · exact h1
        · left
          refine ⟨hp, ?_⟩
          have edge : (pairGraph G u (slide h u c) (c u) ρ).Adj p q :=
            ⟨e.1, active_t hp hph e.2.1.2, active_t hq hqh e.2.2.2⟩
          exact edge.reachable.trans hr
      · right; exact h2

/-- Any `{σ,ρ}`-path (avoiding `h`) from `u` to a `ρ`-vertex `x` has a last
`ρ`-neighbour `y` of `u`, and the rest survives in `t`. -/
lemma split_walk {h u : V} {c : V → C} {ρ : C} (hc : ProperOff G h c) (hu : u ≠ h)
    (hρ : c u ≠ ρ) {x : V} (hx : c x = ρ)
    (r : (pairGraph G h c (c u) ρ).Reachable u x) :
    ∃ y, G.Adj u y ∧ c y = ρ ∧ y ≠ h ∧
      (pairGraph G u (slide h u c) (c u) ρ).Reachable y x := by
  obtain ⟨w⟩ := r
  rcases split_aux G hc hu hρ hx w with ⟨hne, _⟩ | h2
  · exact (hne rfl).elim
  · exact h2

/-! ### The whole-component structure when `S` has no `ρ`-neighbour of `u` -/

lemma whole_s_of_no_rho {h u : V} {c : V → C} {ρ : C} {S : Set V}
    (hc : ProperOff G h c) (hu : u ≠ h)
    (hS : Whole G u (slide h u c) (c u) ρ S) (hh : h ∉ S)
    (hno : ∀ y ∈ S, G.Adj u y → c y ≠ ρ) : Whole G h c (c u) ρ S := by
  obtain ⟨s0, hs0, hmem⟩ := hS
  have hS' : Whole G u (slide h u c) (c u) ρ S := ⟨s0, hs0, hmem⟩
  have hs0S : s0 ∈ S := (hmem s0).mpr (Reachable.refl _)
  have hs0h : s0 ≠ h := fun h' => hh (h' ▸ hs0S)
  refine ⟨s0, active_s hs0h (active_t_colour hs0h hs0), fun v => ?_⟩
  constructor
  · intro hv
    exact reach_t_to_s G hS' hh ((hmem v).mp hv).some hs0S
  · intro hv
    refine reachable_invariant (H := pairGraph G h c (c u) ρ) (P := fun v => v ∈ S)
      ?_ hs0S hv
    intro p q e hp
    have hph : p ≠ h := e.2.1.1
    have hqh : q ≠ h := e.2.2.1
    by_cases hq : q = u
    · exfalso
      subst hq
      rcases e.2.1.2 with h1 | h1
      · exact hc e.1 hph hqh h1
      · exact hno p hp e.1.symm h1
    · exact whole_closed G hS' hp e.1 (active_t hq hqh e.2.2.2)

/-- If `S` has no `ρ`-neighbour of `u` and `h ∉ S` then a pure fill of length three
exists (this is the contradiction in L4(a)(2)). -/
lemma pure_three_of_no_rho {h u : V} {c : V → C} {ρ : C} {S : Set V} {d : V → C}
    (hc : ProperOff G h c) (adj : G.Adj h u) (unique : UniqueAt G h u c)
    (hρ : c u ≠ ρ) (hS : Whole G u (slide h u c) (c u) ρ S) (hh : h ∉ S)
    (hno : ∀ y ∈ S, G.Adj u y → c y ≠ ρ)
    (hN : ∀ v, G.Adj h v → v ∉ S)
    (second : KempeStep G u (swap (slide h u c) (c u) ρ S) d)
    (filled : Target G u d) : PureFill G h c 3 := by
  have hw := whole_s_of_no_rho G hc adj.ne.symm hS hh hno
  have first : KempeStep G h c (swap c (c u) ρ S) := ⟨c u, ρ, S, hρ, hw, rfl⟩
  have hc' := properOff_swap G hc hw
  have huS : u ∉ S := fun hin => (whole_active G hS hin).1 rfl
  have unique' : UniqueAt G h u (swap c (c u) ρ S) := by
    intro v e eq
    rw [swap_out (hN v e), swap_out huS] at eq
    exact unique e eq
  have comm : swap (slide h u c) (c u) ρ S = slide h u (swap c (c u) ρ S) := by
    funext v
    by_cases hvh : v = h
    · subst hvh
      rw [swap_out hh, slide_at, slide_at, swap_out huS]
    · rw [slide_away h u _ hvh]
      by_cases hv : v ∈ S
      · rw [swap_in hv, swap_in hv, slide_away h u c hvh]
      · rw [swap_out hv, swap_out hv, slide_away h u c hvh]
  rw [comm] at second
  exact prepend_kempe G first (slide_kempe G hc' adj unique' second filled)

/-! ### L4(a) -/

/-- **L4(a).**  Let `S` be the whole `{σ,ρ}`-component (`σ = c u`) that is the first of
the two Kempe swaps after the slide `h → u`, with `h ∉ S`, and suppose no pure fill of
length three exists.  Then
1. `S` contains no neighbour of `h`;
2. `S` contains a `ρ`-neighbour of `u`;
3. the `{σ,ρ}`-component `J` of `u` in `G - h` under `c` contains a `ρ`-neighbour of `h`;
4. `S ⊆ J`;
5. `u` has a `ρ`-neighbour `y ∉ S`, lying in the `{σ,ρ}`-component of `h` in `t`, and in
   `t` it is joined by a `{σ,ρ}`-path to a `ρ`-neighbour `x` of `h`.
So `u` has `ρ`-neighbours in two different `{σ,ρ}`-components of `t`. -/
theorem l4a {h u : V} {c : V → C} {ρ : C} {S : Set V} {d : V → C}
    (hc : ProperOff G h c) (no_pure : ¬ PureFill G h c 3)
    (adj : G.Adj h u) (unique : UniqueAt G h u c) (hρ : c u ≠ ρ)
    (hS : Whole G u (slide h u c) (c u) ρ S) (hh : h ∉ S)
    (second : KempeStep G u (swap (slide h u c) (c u) ρ S) d)
    (filled : Target G u d) :
    (∀ v, G.Adj h v → v ∉ S) ∧
    (∃ v ∈ S, G.Adj u v ∧ c v = ρ) ∧
    (∃ x, G.Adj h x ∧ c x = ρ ∧ (pairGraph G h c (c u) ρ).Reachable u x) ∧
    (∀ v ∈ S, (pairGraph G h c (c u) ρ).Reachable u v) ∧
    (∃ y, G.Adj u y ∧ c y = ρ ∧ y ∉ S ∧
      (pairGraph G u (slide h u c) (c u) ρ).Reachable h y ∧
      ∃ x, G.Adj h x ∧ c x = ρ ∧
        (pairGraph G u (slide h u c) (c u) ρ).Reachable y x) := by
  have hhu : h ≠ u := adj.ne
  have hhact : Active u (slide h u c) (c u) ρ h := ⟨hhu, Or.inl (slide_at h u c)⟩
  -- 1
  have hN : ∀ v, G.Adj h v → v ∉ S := fun v e hv =>
    hh (whole_closed G hS hv e.symm hhact)
  -- 2
  have two : ∃ v ∈ S, G.Adj u v ∧ c v = ρ := by
    by_contra hcon
    push Not at hcon
    exact no_pure (pure_three_of_no_rho G hc adj unique hρ hS hh hcon hN second filled)
  -- 3
  have three : ∃ x, G.Adj h x ∧ c x = ρ ∧ (pairGraph G h c (c u) ρ).Reachable u x := by
    by_contra hcon
    push Not at hcon
    apply no_pure
    exact pureFill_mono G (pureFill_one G
      (one_swap_target G hc adj unique hρ (fun v e hv => hcon v e hv))) (by decide)
  obtain ⟨x, hxa, hxc, hxr⟩ := three
  obtain ⟨v0, hv0S, hv0a, hv0c⟩ := two
  refine ⟨hN, ⟨v0, hv0S, hv0a, hv0c⟩, ⟨x, hxa, hxc, hxr⟩, ?_, ?_⟩
  · intro v hv
    have hv0h : v0 ≠ h := fun h' => hh (h' ▸ hv0S)
    have edge : (pairGraph G h c (c u) ρ).Adj u v0 :=
      ⟨hv0a, active_s adj.ne.symm (Or.inl rfl), active_s hv0h (Or.inr hv0c)⟩
    have rr := whole_reach G hS hv0S hv
    exact edge.reachable.trans (reach_t_to_s G hS hh rr.some hv0S)
  · obtain ⟨y, hya, hyc, hyh, hyx⟩ := split_walk G hc adj.ne.symm hρ hxc hxr
    have hxu : x ≠ u := fun h' => hρ (by rw [← h'] at *; exact hxc.symm ▸ rfl)
    have hxact : Active u (slide h u c) (c u) ρ x :=
      active_t hxu hxa.ne.symm (Or.inr hxc)
    have hhx : (pairGraph G u (slide h u c) (c u) ρ).Reachable h x :=
      (show (pairGraph G u (slide h u c) (c u) ρ).Adj h x from
        ⟨hxa, hhact, hxact⟩).reachable
    refine ⟨y, hya, hyc, ?_, hhx.trans hyx.symm, x, hxa, hxc, hyx⟩
    intro hyS
    exact hh (whole_mem_of_reach G hS hyS (hyx.trans hhx.symm))

/-! ### L4(b) -/

/-- The `ρ`-neighbours of `h`. -/
def rhoNbr (h : V) (c : V → C) (ρ : C) : Set V := {x | G.Adj h x ∧ c x = ρ}

/-- The `{σ,ρ}`-components of `G - h` under `c` that contain a `ρ`-neighbour of `h`. -/
def rhoComps (h : V) (c : V → C) (σ ρ : C) : Set (Set V) :=
  (fun x => {v | (pairGraph G h c σ ρ).Reachable x v}) '' rhoNbr G h c ρ

omit [DecidableEq V] in
lemma active_swap_iff [DecidableEq C] {h : V} {c : V → C} {a b : C} {S : Set V} {v : V} :
    Active h (swap c a b S) a b v ↔ Active h c a b v := by
  by_cases hv : v ∈ S
  · rw [Active, Active, swap_in hv]
    simp only [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, Equiv.swap_apply_right]
    tauto
  · rw [Active, Active, swap_out hv]

omit [DecidableEq V] in
lemma pairGraph_swap [DecidableEq C] (h : V) (c : V → C) (a b : C) (S : Set V) :
    pairGraph G h (swap c a b S) a b = pairGraph G h c a b := by
  ext p q
  change (G.Adj p q ∧ Active h (swap c a b S) a b p ∧ Active h (swap c a b S) a b q) ↔
    (G.Adj p q ∧ Active h c a b p ∧ Active h c a b q)
  rw [active_swap_iff, active_swap_iff]

/-- Peeling the `ρ`-components off `h` one at a time. -/
lemma peel [Finite V] {h : V} {σ ρ : C} (hne : σ ≠ ρ) :
    ∀ (n : ℕ) (c : V → C), ProperOff G h c →
      (∀ x, G.Adj h x → c x = ρ → ∀ v,
        (pairGraph G h c σ ρ).Reachable x v → ¬ (G.Adj h v ∧ c v = σ)) →
      (rhoComps G h c σ ρ).ncard ≤ n → PureFill G h c n := by
  intro n
  induction n with
  | zero =>
    intro c hc inv hn
    have hempty : rhoComps G h c σ ρ = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).mp (Nat.le_zero.mp hn)
    refine ⟨0, le_rfl, c, .nil c, ρ, fun v e he => ?_⟩
    have : (fun x => {v | (pairGraph G h c σ ρ).Reachable x v}) v ∈ rhoComps G h c σ ρ :=
      ⟨v, ⟨e, he⟩, rfl⟩
    rw [hempty] at this
    exact this
  | succ m ih =>
    intro c hc inv hn
    by_cases hB : ∃ x, G.Adj h x ∧ c x = ρ
    · obtain ⟨x0, hx0a, hx0c⟩ := hB
      let J : Set V := {v | (pairGraph G h c σ ρ).Reachable x0 v}
      have hJ : Whole G h c σ ρ J :=
        whole_component G h c σ ρ x0 (active_s hx0a.ne.symm (Or.inr hx0c))
      have hgraph := pairGraph_swap G h c σ ρ J
      have hc' := properOff_swap G hc hJ
      -- elements of the new `ρ`-neighbourhood
      have key : ∀ x, G.Adj h x → swap c σ ρ J x = ρ → x ∉ J ∧ c x = ρ := by
        intro x hxa hx
        by_cases hxJ : x ∈ J
        · exfalso
          rw [swap_in hxJ, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hx
          exact inv x0 hx0a hx0c x hxJ ⟨hxa, hx⟩
        · exact ⟨hxJ, by rwa [swap_out hxJ] at hx⟩
      have sub : rhoComps G h (swap c σ ρ J) σ ρ ⊆ rhoComps G h c σ ρ := by
        rintro _ ⟨x, ⟨hxa, hx⟩, rfl⟩
        obtain ⟨_, hxc⟩ := key x hxa hx
        exact ⟨x, ⟨hxa, hxc⟩, by simp only [hgraph]⟩
      have strict : rhoComps G h (swap c σ ρ J) σ ρ ⊂ rhoComps G h c σ ρ := by
        refine (Set.ssubset_iff_of_subset sub).mpr ⟨J, ⟨x0, ⟨hx0a, hx0c⟩, rfl⟩, ?_⟩
        rintro ⟨x, ⟨hxa, hx⟩, hxJ⟩
        obtain ⟨hxnot, _⟩ := key x hxa hx
        apply hxnot
        have : x ∈ {v | (pairGraph G h (swap c σ ρ J) σ ρ).Reachable x v} :=
          Reachable.refl _
        exact (show _ = J from hxJ) ▸ this
      have lt := Set.ncard_lt_ncard strict (Set.toFinite _)
      have inv' : ∀ x, G.Adj h x → swap c σ ρ J x = ρ → ∀ v,
          (pairGraph G h (swap c σ ρ J) σ ρ).Reachable x v →
          ¬ (G.Adj h v ∧ swap c σ ρ J v = σ) := by
        intro x hxa hx v hv ⟨hva, hvc⟩
        obtain ⟨hxnot, hxc⟩ := key x hxa hx
        rw [hgraph] at hv
        have hvJ : v ∉ J := by
          intro hvJ
          apply hxnot
          have r0 : (pairGraph G h c σ ρ).Reachable x0 v := hvJ
          exact r0.trans hv.symm
        rw [swap_out hvJ] at hvc
        exact inv x hxa hxc v hv ⟨hva, hvc⟩
      have rest := ih (swap c σ ρ J) hc' inv' (by omega)
      exact prepend_kempe G ⟨σ, ρ, J, hne, hJ, rfl⟩ rest
    · push Not at hB
      exact ⟨0, Nat.zero_le _, c, .nil c, ρ, fun v e he => hB v e he⟩

omit [DecidableEq V] [DecidableEq C] in
lemma rhoComps_ncard_le [Finite V] (h : V) (c : V → C) (σ ρ : C) :
    (rhoComps G h c σ ρ).ncard ≤ (rhoNbr G h c ρ).ncard :=
  Set.ncard_image_le (Set.toFinite _)

/-- **L4(b).**  If `h ∈ S` (so `S` is `h`'s `{σ,ρ}`-component in `t`) and `u` has no
`ρ`-neighbour in `S`, then a pure fill of length `r` exists, where `r` is the number of
`{σ,ρ}`-components of `G - h` under `c` containing a `ρ`-neighbour of `h`; and
`r ≤ m_ρ`, the number of `ρ`-neighbours of `h`. -/
theorem l4b [Finite V] {h u : V} {c : V → C} {ρ : C} {S : Set V}
    (hc : ProperOff G h c) (adj : G.Adj h u) (unique : UniqueAt G h u c)
    (hρ : c u ≠ ρ) (hS : Whole G u (slide h u c) (c u) ρ S) (hh : h ∈ S)
    (hno : ∀ y ∈ S, G.Adj u y → c y ≠ ρ) :
    PureFill G h c (rhoComps G h c (c u) ρ).ncard ∧
    (rhoComps G h c (c u) ρ).ncard ≤ (rhoNbr G h c ρ).ncard := by
  refine ⟨peel G hρ _ c hc ?_ le_rfl, rhoComps_ncard_le G h c (c u) ρ⟩
  intro x hxa hxc v hxv ⟨hva, hvc⟩
  have hvu : v = u := unique hva hvc
  subst hvu
  have hxu : x ≠ v := fun h' => hρ (by rw [← h'] at *; exact hxc ▸ rfl)
  have hxact : Active v (slide h v c) (c v) ρ x := active_t hxu hxa.ne.symm (Or.inr hxc)
  have hxS : x ∈ S := whole_closed G hS hh hxa hxact
  obtain ⟨y, hya, hyc, _, hyx⟩ := split_walk G hc adj.ne.symm hρ hxc hxv.symm
  have hyS : y ∈ S := whole_mem_of_reach G hS hxS hyx.symm
  exact hno y hyS hya hyc

/-- A finishing form of L4(b) with the bound `m_ρ` only. -/
theorem l4b_le [Finite V] {h u : V} {c : V → C} {ρ : C} {S : Set V}
    (hc : ProperOff G h c) (adj : G.Adj h u) (unique : UniqueAt G h u c)
    (hρ : c u ≠ ρ) (hS : Whole G u (slide h u c) (c u) ρ S) (hh : h ∈ S)
    (hno : ∀ y ∈ S, G.Adj u y → c y ≠ ρ) :
    PureFill G h c (rhoNbr G h c ρ).ncard := by
  obtain ⟨p, le⟩ := l4b G hc adj unique hρ hS hh hno
  exact pureFill_mono G p le

/-! ### L4(c) -/

/-- **L4(c).**  If no pure fill of length `max 3 m_ρ` exists (`κ(s) > max(3, m_ρ)`),
then for every decomposition `u` has a `ρ`-neighbour in the `{σ,ρ}`-component of `h`
in `t`: namely in `S` when `h ∈ S`, and the vertex `y` of L4(a) otherwise. -/
theorem l4c [Finite V] {h u : V} {c : V → C} {ρ : C} {S : Set V} {d : V → C}
    (hc : ProperOff G h c)
    (no_pure : ¬ PureFill G h c (max 3 (rhoNbr G h c ρ).ncard))
    (adj : G.Adj h u) (unique : UniqueAt G h u c) (hρ : c u ≠ ρ)
    (hS : Whole G u (slide h u c) (c u) ρ S)
    (second : KempeStep G u (swap (slide h u c) (c u) ρ S) d)
    (filled : Target G u d) :
    ∃ y, G.Adj u y ∧ c y = ρ ∧
      (pairGraph G u (slide h u c) (c u) ρ).Reachable h y := by
  by_cases hh : h ∈ S
  · by_contra hcon
    push Not at hcon
    have hno : ∀ y ∈ S, G.Adj u y → c y ≠ ρ := fun y hy ya yc =>
      hcon y ya yc (whole_reach G hS hh hy)
    exact no_pure (pureFill_mono G (l4b_le G hc adj unique hρ hS hh hno) (le_max_right _ _))
  · have np3 : ¬ PureFill G h c 3 := fun p =>
      no_pure (pureFill_mono G p (le_max_left _ _))
    obtain ⟨_, _, _, _, y, hya, hyc, _, hhy, _⟩ :=
      l4a G hc np3 adj unique hρ hS hh second filled
    exact ⟨y, hya, hyc, hhy⟩

end SimpleGraph.VacancyLemmaL4
