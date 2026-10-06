/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Relation

/-!
# Breadcrumb warnings are bounded by the dead-end region (Lemma W)

An abstract finite ranked move system: states `X`, a rank `rank : X → ℕ`, a target
predicate, and a macro relation `M2`. A state is *good* if it is a target or has a
rank-decreasing macro to a good state. The breadcrumb policy changes its warning
set only by warning a non-target state all of whose rank-decreasing macro
successors are already warned; every other policy step (move, back, restart)
leaves the warning set unchanged.

Under that abstraction, warned states are never good, so every reachable warning
set lies in the dead-end region `{x | ¬ Good x}`, and its size is at most the size
of that region. If every non-target state has a rank-decreasing macro, every state
is good and no warning is ever placed. No colouring, graph or spherical content is
used: the frozen GraphColour policy `breadcrumb-v1-global-min-depth3-canonical-lex`
is one instance.
-/

@[expose] public section
namespace Breadcrumb

variable {X : Type*} (rank : X → ℕ) (Tgt : X → Prop) (M2 : X → X → Prop)

/-- Good states: targets, or states with a rank-decreasing macro to a good state. -/
inductive Good : X → Prop
  | target {x : X} : Tgt x → Good x
  | descend {x z : X} : M2 x z → rank z < rank x → Good z → Good x

/-- A warning step: warn an unwarned non-target state all of whose rank-decreasing
macro successors are already warned. -/
def WarnStep [DecidableEq X] (W W' : Finset X) : Prop :=
  ∃ c, ¬ Tgt c ∧ c ∉ W ∧ (∀ z, M2 c z → rank z < rank c → z ∈ W) ∧ W' = insert c W

/-- A policy step either leaves the warning set unchanged or is a warning step. -/
def Step [DecidableEq X] (W W' : Finset X) : Prop :=
  W' = W ∨ WarnStep rank Tgt M2 W W'

variable {rank Tgt M2}

/-- **Lemma W1 (one-step invariant).** If no warned state is good, a warning step
keeps it that way. -/
theorem not_good_of_warnStep [DecidableEq X] {W W' : Finset X}
    (hW : ∀ w ∈ W, ¬ Good rank Tgt M2 w) (h : WarnStep rank Tgt M2 W W') :
    ∀ w ∈ W', ¬ Good rank Tgt M2 w := by
  obtain ⟨c, hct, -, hc, rfl⟩ := h
  intro w hw
  rcases Finset.mem_insert.1 hw with rfl | hw
  · intro hg
    cases hg with
    | target ht => exact hct ht
    | descend hm hr hz => exact hW _ (hc _ hm hr) hz
  · exact hW w hw

/-- **Lemma W2.** Every warning set reachable from `∅` lies in the dead-end region. -/
theorem not_good_of_reachable [DecidableEq X] {W : Finset X}
    (h : Relation.ReflTransGen (Step rank Tgt M2) ∅ W) :
    ∀ w ∈ W, ¬ Good rank Tgt M2 w := by
  induction h with
  | refl => intro w hw; simp at hw
  | tail _ hstep ih =>
    rcases hstep with rfl | hwarn
    · exact ih
    · exact not_good_of_warnStep ih hwarn

/-- **Warnings are at most the dead-end region.** -/
theorem card_le_deadEnd [Fintype X] [DecidableEq X] [DecidablePred (Good rank Tgt M2)]
    {W : Finset X} (h : Relation.ReflTransGen (Step rank Tgt M2) ∅ W) :
    W.card ≤ (Finset.univ.filter (fun x => ¬ Good rank Tgt M2 x)).card := by
  apply Finset.card_le_card
  intro w hw
  simpa using not_good_of_reachable h w hw

/-- Each warning step adds exactly one new warned state. -/
theorem card_warnStep [DecidableEq X] {W W' : Finset X} (h : WarnStep rank Tgt M2 W W') :
    W'.card = W.card + 1 := by
  obtain ⟨c, -, hcW, -, rfl⟩ := h
  exact Finset.card_insert_of_notMem hcW

/-- If every non-target state has a rank-decreasing macro, every state is good,
so the dead-end region is empty and no warning is ever placed. -/
theorem good_of_forall_descent
    (h : ∀ x, ¬ Tgt x → ∃ z, M2 x z ∧ rank z < rank x) :
    ∀ x, Good rank Tgt M2 x := by
  classical
  suffices H : ∀ k, ∀ x, rank x = k → Good rank Tgt M2 x from fun x => H _ x rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x hx
  by_cases ht : Tgt x
  · exact Good.target ht
  · obtain ⟨z, hm, hr⟩ := h x ht
    exact Good.descend hm hr (ih _ (hx ▸ hr) z rfl)

end Breadcrumb
