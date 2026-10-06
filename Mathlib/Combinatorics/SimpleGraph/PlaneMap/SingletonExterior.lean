/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeBoundary
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! # Exterior vertices forced by a locked singleton chain

This is a graph-theoretic obstruction. No planarity assumption is used.
-/
@[expose] public section
namespace SimpleGraph.Kempe
variable {V : Type*} {k : ℕ}

/-- A singleton boundary colour linked to a different boundary colour, with no
boundary exit in that pair, forces two distinct exterior vertices in its chain. -/
theorem singleton_chain_two_exterior [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Fin k)
    (B : Finset V) (a b : Fin k) (hab : a ≠ b) (u v : V)
    (hu : c u = a) (hv : c v = b) (hvB : v ∈ B)
    (hc : IsProperColouring G c)
    (hunique : ∀ w ∈ B, c w = a → w = u)
    (hexit : ∀ w ∈ B, c w = b → ¬ G.Adj u w)
    (hr : (bichromaticSubgraph G c a b).Reachable u v) :
    ∃ x y, x ∉ B ∧ y ∉ B ∧ x ≠ y ∧ c x = b ∧ c y = a ∧
      (bichromaticSubgraph G c a b).Reachable u x ∧
      (bichromaticSubgraph G c a b).Reachable u y := by
  obtain ⟨p, hp⟩ := hr.exists_isPath
  cases p with
  | nil => exact False.elim (hab (hu.symm.trans hv))
  | @cons u x v hux p =>
    have hx : c x = b := hux.2.2.resolve_left (fun he => hc u x hux.1 (hu.trans he.symm))
    have hxB : x ∉ B := fun h => hexit x h hx hux.1
    cases p with
    | nil => exact False.elim (hxB hvB)
    | @cons x y v hxy q =>
      have hy : c y = a := hxy.2.2.resolve_right (fun he => hc x y hxy.1 (hx.trans he.symm))
      have hynu : y ≠ u := by
        have hnot := (Walk.cons_isPath_iff hux (Walk.cons hxy q)).mp hp |>.2
        intro he
        apply hnot
        rw [← he]
        simp
      have hyB : y ∉ B := fun h => hynu (hunique y h hy)
      refine ⟨x, y, hxB, hyB, hxy.ne, hx, hy, ?_, ?_⟩
      · exact hux.reachable
      · exact hux.reachable.trans hxy.reachable

end SimpleGraph.Kempe
