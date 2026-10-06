/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalDelete

/-!
# Moving a colouring vacancy

A uniquely coloured neighbour can receive the vacancy while the old vacancy
receives that neighbour's colour. This is a reversible move, not a descent rule.
The graph-level statements require neither finiteness nor spherical separation.
-/

@[expose] public section
namespace SimpleGraph.VacancySlide

variable {V C : Type*} (G : SimpleGraph V)

/-- Properness on all edges avoiding the vacant vertex. The vacant label has
an irrelevant stored colour. -/
def ProperOff (r : V) (c : V → C) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ≠ r → v ≠ r → c u ≠ c v

/-- The neighbour's colour occurs only there on the old vacancy's boundary. -/
def UniqueAt (r x : V) (c : V → C) : Prop :=
  ∀ ⦃y⦄, G.Adj r y → c y = c x → y = x

/-- Fill the old vacancy using the colour stored at the new vacancy. -/
def slide [DecidableEq V] (r x : V) (c : V → C) : V → C :=
  fun v => if v = r then c x else c v

@[simp] theorem slide_at [DecidableEq V] (r x : V) (c : V → C) :
    slide r x c r = c x := by simp [slide]

@[simp] theorem slide_away [DecidableEq V] (r x : V) (c : V → C)
    {v : V} (hv : v ≠ r) : slide r x c v = c v := by simp [slide, hv]

/-- A singleton boundary colour gives a proper colouring at the new vacancy. -/
theorem properOff_slide [DecidableEq V] {r x : V} {c : V → C}
    (hc : ProperOff G r c) (hunique : UniqueAt G r x c) :
    ProperOff G x (slide r x c) := by
  intro u v huv hux hvx
  by_cases hur : u = r
  · subst u
    simp only [slide_at]
    have hvr : v ≠ r := huv.ne.symm
    rw [slide_away r x c hvr]
    intro heq
    exact hvx (hunique huv heq.symm)
  · by_cases hvr : v = r
    · subst v
      rw [slide_away r x c hur, slide_at]
      intro heq
      exact hux (hunique huv.symm heq)
    · rw [slide_away r x c hur, slide_away r x c hvr]
      exact hc huv hur hvr

/-- The old vacancy is itself singleton-coloured at the new vacancy. Thus
vacancy sliding has a legal inverse, without a progress conclusion. -/
theorem uniqueAt_reverse [DecidableEq V] {r x : V} {c : V → C}
    (hc : ProperOff G r c) (hrx : G.Adj r x) :
    UniqueAt G x r (slide r x c) := by
  intro y hxy heq
  by_contra hyr
  rw [slide_away r x c hyr, slide_at] at heq
  exact hc hxy hrx.ne.symm hyr heq.symm

/-- Sliding back restores every relevant colour. The stored colour at the
original vacancy is immaterial and need not be restored. -/
theorem slide_reverse_away [DecidableEq V] {r x : V} {c : V → C}
    {v : V} (hvr : v ≠ r) :
    slide x r (slide r x c) v = c v := by
  by_cases hvx : v = x
  · subst v
    simp [slide]
  · simp [slide, hvx, hvr]

/-- A proper partial colouring is an actual colouring of the induced deletion. -/
def inducedColouring {r : V} {c : V → C} (hc : ProperOff G r c) :
    (G.induce {v | v ≠ r}).Coloring C :=
  Coloring.mk (fun v => c v.val) (fun {u v} huv => hc huv u.property v.property)

end SimpleGraph.VacancySlide

namespace SimpleGraph.SphericalMap

/-- The carrier's isolate graph uses exactly the generic vacancy properness. -/
theorem isolate_colouring_properOff {C : Type*} {n : ℕ} (M : SphericalMap n) (r : Fin n)
    (c : (M.isolateGraph r).Coloring C) :
    VacancySlide.ProperOff M.graph r c := by
  intro u v huv hur hvr
  exact c.valid ⟨huv, hur, hvr⟩

/-- The vacancy move constructs an actual colouring on the new isolated
carrier. It makes no assertion about the new vacancy's degree. -/
def slideIsolateColouring {C : Type*} {n : ℕ} (M : SphericalMap n) (r x : Fin n)
    (c : (M.isolateGraph r).Coloring C)
    (hunique : VacancySlide.UniqueAt M.graph r x c) :
    (M.isolateGraph x).Coloring C :=
  Coloring.mk (VacancySlide.slide r x c) (fun {_ _} huv =>
    VacancySlide.properOff_slide M.graph (M.isolate_colouring_properOff r c)
      hunique huv.1 huv.2.1 huv.2.2)

end SimpleGraph.SphericalMap
