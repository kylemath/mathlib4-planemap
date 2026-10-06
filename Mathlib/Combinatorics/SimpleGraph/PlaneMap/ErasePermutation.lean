/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! # Removing a point from permutation cycles -/

@[expose] public section
namespace Equiv.Perm

variable {α β : Type*}

/-- Fix `a` and bypass it in its former permutation cycle. -/
noncomputable def erasePoint (σ : Perm α) (a : α) : Perm α := by
  classical
  exact swap a (σ a) * σ

@[simp] theorem erasePoint_self (σ : Perm α) (a : α) : erasePoint σ a a = a := by
  classical
  simp [erasePoint]

theorem erasePoint_preserves (σ : Perm α) (a : α) (f : α → β)
    (hf : ∀ z, f (σ z) = f z) (z : α) : f (erasePoint σ a z) = f z := by
  classical
  unfold erasePoint
  simp only [mul_apply, swap_apply_def]
  split_ifs <;> grind

theorem erasePoint_fixed (σ : Perm α) (a z : α) (hz : σ z = z) :
    erasePoint σ a z = z := by
  classical
  by_cases hza : z = a
  · subst z; exact erasePoint_self σ a
  · have hne : z ≠ σ a := fun hh => hza (σ.injective (hz.trans hh))
    simp [erasePoint, hz, swap_apply_of_ne_of_ne hza hne]

/-- Deleting a point does not separate any two other points of its orbit. -/
theorem erasePoint_iterate (σ : Perm α) (a x y : α) (hx : x ≠ a) (hy : y ≠ a)
    (h : ∃ k : ℕ, (⇑σ)^[k] x = y) :
    ∃ k : ℕ, (⇑(erasePoint σ a))^[k] x = y := by
  classical
  let τ := erasePoint σ a
  let collapse : α → α := fun z => if z = a then σ a else z
  have step (z : α) : ∃ k : ℕ, (⇑τ)^[k] (collapse z) = collapse (σ z) := by
    by_cases hz : z = a
    · subst z
      exact ⟨0, by simp [collapse]⟩
    · refine ⟨1, ?_⟩
      have hn : σ z ≠ σ a := σ.injective.ne hz
      simp only [Function.iterate_one]
      by_cases hza : σ z = a
      · simp [τ, erasePoint, collapse, hz, hza]
      · simp [τ, erasePoint, collapse, hz, hza, swap_apply_of_ne_of_ne hza hn]
  have lift : ∀ k : ℕ, ∃ j : ℕ, (⇑τ)^[j] x = collapse ((⇑σ)^[k] x) := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp [collapse, hx]⟩
    | succ k ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨l, hl⟩ := step ((⇑σ)^[k] x)
      refine ⟨l + j, ?_⟩
      rw [Function.iterate_add_apply, hj, hl, Function.iterate_succ_apply']
  obtain ⟨k, hk⟩ := h
  obtain ⟨j, hj⟩ := lift k
  exact ⟨j, by simpa [hk, collapse, hy] using hj⟩

/-- Bypassing a point preserves any observable that agrees there with its successor. -/
theorem erasePoint_observe (σ : Perm α) (a : α) (f : α → β)
    (hf : f a = f (σ a)) (z : α) : f (erasePoint σ a z) = f (σ z) := by
  classical
  unfold erasePoint
  simp only [mul_apply, swap_apply_def]
  split_ifs <;> grind

end Equiv.Perm
