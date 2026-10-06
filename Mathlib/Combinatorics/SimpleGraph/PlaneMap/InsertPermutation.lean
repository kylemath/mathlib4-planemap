/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.ErasePermutation

/-! # Permutation orbit lemmas for inserting an edge

The generic successor exchange merges two distinct old cycles. Inserting fresh
symbols into the exchanged transitions gives the two new edge orientations.
The same-cycle chord split is already supplied by `Construction.splitFaceEquiv`.
-/

@[expose] public section
namespace Equiv.Perm
variable {α : Type*} [DecidableEq α]

/-- Exchange the successors of two old points. -/
def successorSwap (σ : Perm α) (a b : α) : Perm α := σ * swap a b

@[simp] theorem successorSwap_left (σ : Perm α) (a b : α) :
    successorSwap σ a b a = σ b := by simp [successorSwap]
@[simp] theorem successorSwap_right (σ : Perm α) (a b : α) :
    successorSwap σ a b b = σ a := by simp [successorSwap]

theorem successorSwap_other (σ : Perm α) (a b x : α) (ha : x ≠ a) (hb : x ≠ b) :
    successorSwap σ a b x = σ x := by
  simp [successorSwap, swap_apply_of_ne_of_ne ha hb]

/-- Exchanging successors of distinct cycles joins their distinguished points.
This statement allows fixed points and arbitrary other cycles. -/
theorem successorSwap_sameCycle_of_not_sameCycle [Finite α] (σ : Perm α)
    (a b : α) (hab : ¬ σ.SameCycle a b) :
    (successorSwap σ a b).SameCycle a b := by
  have hex : ∃ L : ℕ, 0 < L ∧ (σ ^ L) a = a :=
    (SameCycle.refl σ a).exists_pow_eq'' |>.imp fun _ h => ⟨h.1, h.2.2⟩
  let L := Nat.find hex
  have hLpos : 0 < L := (Nat.find_spec hex).1
  have hL : (σ ^ L) a = a := (Nat.find_spec hex).2
  have hnot (k : ℕ) (hk : 0 < k) (hkL : k < L) : (σ ^ k) a ≠ a := by
    intro heq
    exact (Nat.find_min' hex ⟨hk, heq⟩).not_gt hkL
  have hnotb (k : ℕ) : (σ ^ k) a ≠ b := by
    intro heq
    apply hab
    exact ⟨(k : ℤ), by simpa using heq⟩
  have hwalk (k : ℕ) (hk : k < L) :
      (successorSwap σ a b ^ (k + 1)) b = (σ ^ (k + 1)) a := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hp : k + 1 < L := hk
      have hprev := ih (by omega)
      rw [pow_succ', mul_apply, hprev]
      rw [successorSwap_other σ a b _ (hnot (k + 1) (by omega) hp) (hnotb _)]
      simp only [pow_succ', mul_apply]
  have hreach : (successorSwap σ a b ^ L) b = a := by
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hLpos)), hL]
      using hwalk (L - 1) (by omega)
  exact (show (successorSwap σ a b).SameCycle b a from
    ⟨(L : ℤ), by simpa using hreach⟩).symm

omit [DecidableEq α] in
/-- Simulating each permutation step transports its finite orbit relation. -/
theorem sameCycle_lift_of_step {β : Type*} [Finite α]
    (σ : Perm α) (τ : Perm β) (f : α → β)
    (hstep : ∀ z, τ.SameCycle (f z) (f (σ z)))
    {x y : α} (h : σ.SameCycle x y) : τ.SameCycle (f x) (f y) := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => simpa using SameCycle.refl τ (f x)
  | succ k ih =>
    simpa only [pow_succ', mul_apply] using ih.trans (hstep ((σ ^ k) x))

/-- Every old orbit embeds in the merged successor-exchange orbit. -/
theorem successorSwap_preserves_sameCycle [Finite α] (σ : Perm α)
    (a b : α) (hab : ¬ σ.SameCycle a b) {x y : α} (h : σ.SameCycle x y) :
    (successorSwap σ a b).SameCycle x y := by
  have hm := successorSwap_sameCycle_of_not_sameCycle σ a b hab
  apply sameCycle_lift_of_step σ (successorSwap σ a b) id _ h
  intro z
  by_cases ha : z = a
  · subst z
    simpa using hm.apply_right
  · by_cases hb : z = b
    · subst z
      simpa using hm.symm.apply_right
    · exact ⟨1, by simp [successorSwap_other σ a b z ha hb]⟩

omit [DecidableEq α] in
/-- An invariant observable is constant on finite permutation orbits. -/
theorem sameCycle_observable [Finite α] {β : Type*} (σ : Perm α)
    (f : α → β) (hf : ∀ z, f (σ z) = f z) {x y : α} (h : σ.SameCycle x y) :
    f x = f y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => simp
  | succ k ih => simpa only [pow_succ', mul_apply, hf] using ih

/-- Face coefficients can descend through a merge after their two old values
have been normalized to agree. -/
theorem successorSwap_observable {β : Type*} (σ : Perm α) (a b : α)
    (f : α → β) (hf : ∀ z, f (σ z) = f z) (hab : f a = f b) (z : α) :
    f (successorSwap σ a b z) = f z := by
  by_cases ha : z = a
  · subst z; simpa [hf] using hab.symm
  · by_cases hb : z = b
    · subst z; simpa [hf] using hab
    · rw [successorSwap_other σ a b z ha hb, hf]

/-- Orbits outside the two chosen old cycles remain distinct after merging. -/
theorem successorSwap_other_cycle_iff [Finite α] (σ : Perm α) (a b x y : α)
    (hab : ¬ σ.SameCycle a b) (hxa : ¬ σ.SameCycle x a)
    (hxb : ¬ σ.SameCycle x b) :
    (successorSwap σ a b).SameCycle x y ↔ σ.SameCycle x y := by
  constructor
  · intro h
    have hf (z : α) : σ.SameCycle x (σ z) = σ.SameCycle x z :=
      propext sameCycle_apply_right
    have heq : σ.SameCycle x a = σ.SameCycle x b := by simp [hxa, hxb]
    have ho := sameCycle_observable (successorSwap σ a b)
      (fun z => σ.SameCycle x z) (successorSwap_observable σ a b _ hf heq) h
    exact ho ▸ SameCycle.refl σ x
  · exact successorSwap_preserves_sameCycle σ a b hab

/-- Exchange successors, then subdivide both exchanged transitions by two fresh
symbols. These are the face transitions of an inserted oriented edge. -/
def insertFacePermutation (σ : Perm α) (a b : α) : Perm (α ⊕ Bool) :=
  swap (.inl (σ a)) (.inr true) * swap (.inl (σ b)) (.inr false) *
    Equiv.sumCongr (successorSwap σ a b) (Equiv.refl Bool)

@[simp] theorem insertFacePermutation_left (σ : Perm α) (a b : α) :
    insertFacePermutation σ a b (.inl a) = .inr false := by
  simp [insertFacePermutation, mul_apply, swap_apply_def]

@[simp] theorem insertFacePermutation_right (σ : Perm α) (a b : α) (hab : a ≠ b) :
    insertFacePermutation σ a b (.inl b) = .inr true := by
  simp [insertFacePermutation, mul_apply, swap_apply_of_ne_of_ne,
    σ.injective.ne hab]

@[simp] theorem insertFacePermutation_false (σ : Perm α) (a b : α) (hab : a ≠ b) :
    insertFacePermutation σ a b (.inr false) = .inl (σ b) := by
  simp [insertFacePermutation, mul_apply, swap_apply_of_ne_of_ne,
    (σ.injective.ne hab).symm]

@[simp] theorem insertFacePermutation_true (σ : Perm α) (a b : α) :
    insertFacePermutation σ a b (.inr true) = .inl (σ a) := by
  simp [insertFacePermutation, mul_apply, swap_apply_of_ne_of_ne]

theorem insertFacePermutation_other (σ : Perm α) (a b z : α)
    (ha : z ≠ a) (hb : z ≠ b) :
    insertFacePermutation σ a b (.inl z) = .inl (σ z) := by
  simp [insertFacePermutation, mul_apply, successorSwap_other σ a b z ha hb,
    swap_apply_of_ne_of_ne, σ.injective.ne ha, σ.injective.ne hb]

/-- Subdividing the exchanged transitions preserves every exchanged orbit. -/
theorem insertFacePermutation_preserves_sameCycle [Finite α] (σ : Perm α)
    (a b : α) (hab : a ≠ b) {x y : α}
    (h : (successorSwap σ a b).SameCycle x y) :
    (insertFacePermutation σ a b).SameCycle (.inl x) (.inl y) := by
  apply sameCycle_lift_of_step (successorSwap σ a b) (insertFacePermutation σ a b)
    Sum.inl _ h
  intro z
  by_cases ha : z = a
  · subst z
    exact ⟨2, by simp [pow_succ', mul_apply, hab]⟩
  · by_cases hb : z = b
    · subst z
      exact ⟨2, by simp [pow_succ', mul_apply, hab]⟩
    · exact ⟨1, by simp [insertFacePermutation_other σ a b z ha hb,
        successorSwap_other σ a b z ha hb]⟩

/-- Both new edge orientations are in the same merged face when the two old
corners belonged to different permutation cycles. -/
theorem insertFacePermutation_fresh_sameCycle [Finite α] (σ : Perm α)
    (a b : α) (h : ¬ σ.SameCycle a b) :
    (insertFacePermutation σ a b).SameCycle (.inr false) (.inr true) := by
  have hab : a ≠ b := fun heq => h (heq.sameCycle σ)
  have hm := insertFacePermutation_preserves_sameCycle σ a b hab
    (successorSwap_sameCycle_of_not_sameCycle σ a b h)
  have hleft : (insertFacePermutation σ a b).SameCycle (.inl a) (.inr false) :=
    ⟨1, by simp⟩
  have hright : (insertFacePermutation σ a b).SameCycle (.inl b) (.inr true) :=
    ⟨1, by simp [hab]⟩
  exact hleft.symm.trans (hm.trans hright)

/-- Extend old face coefficients across the two inserted darts. -/
def insertFaceObservable {β : Type*} (f : α → β) (a b : α) : α ⊕ Bool → β
  | .inl z => f z
  | .inr false => f b
  | .inr true => f a

/-- Equal normalized old coefficients yield an invariant new face observable.
This is a coefficient-descent interface, with no spherical filling assumption. -/
theorem insertFacePermutation_observable {β : Type*} (σ : Perm α) (a b : α)
    (hab : a ≠ b) (f : α → β) (hf : ∀ z, f (σ z) = f z) (hfab : f a = f b)
    (z : α ⊕ Bool) :
    insertFaceObservable f a b (insertFacePermutation σ a b z) =
      insertFaceObservable f a b z := by
  cases z with
  | inl z =>
    by_cases ha : z = a
    · subst z; simpa [insertFaceObservable] using hfab.symm
    · by_cases hb : z = b
      · subst z; simpa [insertFaceObservable, hab] using hfab
      · rw [insertFacePermutation_other σ a b z ha hb]
        exact hf z
  | inr z =>
    cases z
    · rw [insertFacePermutation_false σ a b hab]; exact hf b
    · rw [insertFacePermutation_true]; exact hf a

/-- Every old cycle except the two selected cycles is unchanged by insertion. -/
theorem insertFacePermutation_other_cycle_iff [Finite α] (σ : Perm α)
    (a b x y : α) (hab : ¬ σ.SameCycle a b)
    (hxa : ¬ σ.SameCycle x a) (hxb : ¬ σ.SameCycle x b) :
    (insertFacePermutation σ a b).SameCycle (.inl x) (.inl y) ↔ σ.SameCycle x y := by
  have hne : a ≠ b := fun heq => hab (heq.sameCycle σ)
  constructor
  · intro h
    have hf (z : α) : σ.SameCycle x (σ z) = σ.SameCycle x z :=
      propext sameCycle_apply_right
    have heq : σ.SameCycle x a = σ.SameCycle x b := by simp [hxa, hxb]
    have ho := sameCycle_observable (insertFacePermutation σ a b)
      (insertFaceObservable (fun z => σ.SameCycle x z) a b)
      (insertFacePermutation_observable σ a b hne _ hf heq) h
    change σ.SameCycle x x = σ.SameCycle x y at ho
    exact ho ▸ SameCycle.refl σ x
  · intro h
    exact insertFacePermutation_preserves_sameCycle σ a b hne
      (successorSwap_preserves_sameCycle σ a b hab h)

/-- The convention inserting immediately before target corners `a,b`.
The interrupted sources are their old face predecessors. -/
def insertFaceBeforePermutation (σ : Perm α) (a b : α) : Perm (α ⊕ Bool) :=
  insertFacePermutation σ (σ.symm a) (σ.symm b)

@[simp] theorem insertFaceBeforePermutation_false (σ : Perm α) (a b : α)
    (hab : a ≠ b) : insertFaceBeforePermutation σ a b (.inr false) = .inl b := by
  simpa [insertFaceBeforePermutation] using
    insertFacePermutation_false σ (σ.symm a) (σ.symm b) (σ.symm.injective.ne hab)

@[simp] theorem insertFaceBeforePermutation_true (σ : Perm α) (a b : α) :
    insertFaceBeforePermutation σ a b (.inr true) = .inl a := by
  simp [insertFaceBeforePermutation]

theorem insertFaceBeforePermutation_old (σ : Perm α) (a b d : α) (hab : a ≠ b) :
    insertFaceBeforePermutation σ a b (.inl d) =
      if σ d = a then .inr false else if σ d = b then .inr true else .inl (σ d) := by
  by_cases ha : σ d = a
  · have he : d = σ.symm a := (σ.eq_symm_apply).mpr ha
    subst d
    simp [insertFaceBeforePermutation]
  · by_cases hb : σ d = b
    · have he : d = σ.symm b := (σ.eq_symm_apply).mpr hb
      subst d
      simp [insertFaceBeforePermutation, hab.symm, σ.symm.injective.ne hab]
    · have hda : d ≠ σ.symm a := fun h => ha (by simp [h])
      have hdb : d ≠ σ.symm b := fun h => hb (by simp [h])
      simp [insertFaceBeforePermutation,
        insertFacePermutation_other σ (σ.symm a) (σ.symm b) d hda hdb, ha, hb]

/-- The two fresh darts merge when the target corner faces differ, in the
before-corner convention of `PlaneMapConstruction.split`. -/
theorem insertFaceBeforePermutation_fresh_sameCycle [Finite α] (σ : Perm α)
    (a b : α) (h : ¬ σ.SameCycle a b) :
    (insertFaceBeforePermutation σ a b).SameCycle (.inr false) (.inr true) := by
  apply insertFacePermutation_fresh_sameCycle
  simpa only [sameCycle_symm_apply_left, sameCycle_symm_apply_right] using h

/-- The unchanged-other-orbits theorem in the before-corner convention. -/
theorem insertFaceBeforePermutation_other_cycle_iff [Finite α] (σ : Perm α)
    (a b x y : α) (hab : ¬ σ.SameCycle a b)
    (hxa : ¬ σ.SameCycle x a) (hxb : ¬ σ.SameCycle x b) :
    (insertFaceBeforePermutation σ a b).SameCycle (.inl x) (.inl y) ↔
      σ.SameCycle x y := by
  apply insertFacePermutation_other_cycle_iff
  · simpa only [sameCycle_symm_apply_left, sameCycle_symm_apply_right] using hab
  · simpa only [sameCycle_symm_apply_right] using hxa
  · simpa only [sameCycle_symm_apply_right] using hxb

/-- Normalized coefficients descend for before-corner insertion as well. -/
theorem insertFaceBeforePermutation_observable {β : Type*} (σ : Perm α) (a b : α)
    (hab : a ≠ b) (f : α → β) (hf : ∀ z, f (σ z) = f z) (hfab : f a = f b)
    (z : α ⊕ Bool) :
    insertFaceObservable f (σ.symm a) (σ.symm b)
      (insertFaceBeforePermutation σ a b z) =
      insertFaceObservable f (σ.symm a) (σ.symm b) z := by
  apply insertFacePermutation_observable σ _ _ (σ.symm.injective.ne hab) f hf
  have ha : f a = f (σ.symm a) := by simpa using hf (σ.symm a)
  have hb : f b = f (σ.symm b) := by simpa using hf (σ.symm b)
  exact ha.symm.trans (hfab.trans hb)

end Equiv.Perm
