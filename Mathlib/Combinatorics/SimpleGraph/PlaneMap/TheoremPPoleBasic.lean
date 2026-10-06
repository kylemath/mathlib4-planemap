/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TwoPoleBelt
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyShortFill
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

/-!
# Theorem P (pole holes without Florek): basic layer

Definitions and the one-vertex moves (rules T1 and F of `pole-hole-noflorek.md`)
for the two-pole belt, with the hole fixed at the pole `a`.
-/

@[expose] public section
namespace SimpleGraph.TheoremPPole
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

variable {n : ℕ}

/-- Properness off the hole `a`. -/
abbrev PR (n : ℕ) (c : Vertex n → Colour) : Prop := ProperOff (graph n) a c

/-- A ring vertex is a junction when it carries the colour of the pole `b`. -/
def Jn (c : Vertex n → Colour) (i : ZMod n) : Prop := c (u i) = c b

instance (c : Vertex n → Colour) (i : ZMod n) : Decidable (Jn c i) := by
  unfold Jn; infer_instance

/-- Exposed `x`-vertex: ring neighbour of a junction. -/
def Exposed (c : Vertex n → Colour) (x : Colour) (i : ZMod n) : Prop :=
  c (u i) = x ∧ (Jn c (i-1) ∨ Jn c (i+1))

/-- Interior `x`-vertex: neither ring neighbour is a junction. -/
def Interior (c : Vertex n → Colour) (x : Colour) (i : ZMod n) : Prop :=
  c (u i) = x ∧ ¬ Jn c (i-1) ∧ ¬ Jn c (i+1)

instance (c : Vertex n → Colour) (x : Colour) (i : ZMod n) : Decidable (Interior c x i) := by
  unfold Interior; infer_instance

/-- The ring uses some colour at most once (so at most 3 colours, or a singleton). -/
def Good (c : Vertex n → Colour) : Prop :=
  ∃ x, ∀ i j : ZMod n, c (u i) = x → c (u j) = x → i = j

/-! ### Local adjacency -/

section local_facts
variable (hn : 5 ≤ n)
include hn

lemma adj_uu' (i : ZMod n) : (graph n).Adj (u i) (u (i+1)) := by
  rw [adj_u hn]; simp
lemma adj_uv0 (i : ZMod n) : (graph n).Adj (u i) (v i) := by
  rw [adj_u hn]; simp
lemma adj_uv1 (i : ZMod n) : (graph n).Adj (u i) (v (i-1)) := by
  rw [adj_u hn]; simp
lemma adj_vu1 (i : ZMod n) : (graph n).Adj (v i) (u (i+1)) := by
  rw [adj_v hn]; simp
lemma adj_vv' (i : ZMod n) : (graph n).Adj (v i) (v (i+1)) := by
  rw [adj_v hn]; simp
omit hn in
lemma adj_ua (i : ZMod n) : (graph n).Adj (u i) a := by
  simp [graph, TwoPoleBelt.edge]
omit hn in
lemma adj_vb (i : ZMod n) : (graph n).Adj (v i) b := by
  simp [graph, TwoPoleBelt.edge]

variable {c : Vertex n → Colour} (hc : PR n c)
include hc

lemma cuu (i : ZMod n) : c (u i) ≠ c (u (i+1)) := hc (adj_uu' hn i) (by simp) (by simp)
lemma cuv0 (i : ZMod n) : c (u i) ≠ c (v i) := hc (adj_uv0 hn i) (by simp) (by simp)
lemma cuv1 (i : ZMod n) : c (u i) ≠ c (v (i-1)) := hc (adj_uv1 hn i) (by simp) (by simp)
lemma cvu1 (i : ZMod n) : c (v i) ≠ c (u (i+1)) := hc (adj_vu1 hn i) (by simp) (by simp)
lemma cvv (i : ZMod n) : c (v i) ≠ c (v (i+1)) := hc (adj_vv' hn i) (by simp) (by simp)
lemma cvb (i : ZMod n) : c (v i) ≠ c b := hc (adj_vb i) (by simp) (by simp)

lemma cuu' (i : ZMod n) : c (u (i-1)) ≠ c (u i) := by
  simpa using cuu hn hc (i-1)
lemma cvu0 (i : ZMod n) : c (v i) ≠ c (u i) := (cuv0 hn hc i).symm
lemma cvv' (i : ZMod n) : c (v (i-1)) ≠ c (v i) := by
  simpa using cvv hn hc (i-1)
lemma cvu1' (i : ZMod n) : c (v (i-1)) ≠ c (u i) := by
  simpa using cvu1 hn hc (i-1)

end local_facts

/-! ### One-vertex Kempe moves -/

lemma swap_single_self [DecidableEq Colour] (c : Vertex n → Colour) (x y : Colour) (w : Vertex n) :
    VacancyShortFill.swap c x y {w} w = Equiv.swap x y (c w) :=
  VacancyShortFill.swap_in (Set.mem_singleton _)

lemma swap_single_other (c : Vertex n → Colour) (x y : Colour) {w v : Vertex n} (h : v ≠ w) :
    VacancyShortFill.swap c x y {w} v = c v :=
  VacancyShortFill.swap_out (by simpa using h)

/-- A one-vertex whole component: swapping it is a Kempe move. -/
lemma single_step {c : Vertex n → Colour} (hc : PR n c) {w : Vertex n} (hw : w ≠ a)
    {x y : Colour} (hxy : x ≠ y) (hcw : c w = x)
    (hiso : ∀ v, (graph n).Adj w v → v ≠ a → c v ≠ y) :
    VacancyShortFill.KempeStep (graph n) a c (VacancyShortFill.swap c x y {w}) ∧
    VacancyShortFill.swap c x y {w} w = y ∧
    ∀ v, v ≠ w → VacancyShortFill.swap c x y {w} v = c v := by
  have hwh : VacancyShortFill.Whole (graph n) a c x y {w} := by
    apply VacancyShortFill.whole_singleton (graph n) ⟨hw, Or.inl hcw⟩
    intro v e hva
    refine ⟨?_, hiso v e hva⟩
    have h1 := hc e hw hva
    exact fun h => h1 (hcw.trans h.symm)
  refine ⟨⟨x, y, {w}, hxy, hwh, rfl⟩, ?_, fun v hv => swap_single_other c x y hv⟩
  rw [swap_single_self, hcw, Equiv.swap_apply_left]

end SimpleGraph.TheoremPPole
