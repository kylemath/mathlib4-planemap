import Mathlib.Combinatorics.SimpleGraph.PlaneMap.InsertPermutation
import Mathlib.Tactic


/-- info: 'Equiv.Perm.successorSwap_sameCycle_of_not_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equiv.Perm.successorSwap_sameCycle_of_not_sameCycle

/-- info: 'Equiv.Perm.insertFacePermutation_fresh_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equiv.Perm.insertFacePermutation_fresh_sameCycle

/-- info: 'Equiv.Perm.insertFacePermutation_other_cycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equiv.Perm.insertFacePermutation_other_cycle_iff

/-- info: 'Equiv.Perm.insertFacePermutation_observable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equiv.Perm.insertFacePermutation_observable

/-- info: 'Equiv.Perm.insertFaceBeforePermutation_fresh_sameCycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equiv.Perm.insertFaceBeforePermutation_fresh_sameCycle

open Equiv.Perm

def twoOldCycles : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem twoOldCycles_distinct : ¬ twoOldCycles.SameCycle 0 2 := by
  intro h
  have hf (z : Fin 5) : decide ((twoOldCycles z).val < 2) = decide (z.val < 2) := by
    fin_cases z <;> decide
  have heq := sameCycle_observable twoOldCycles (fun z => decide (z.val < 2)) hf h
  norm_num at heq

def joinedFaces : Equiv.Perm (Fin 5 ⊕ Bool) := insertFacePermutation twoOldCycles 0 2

def pointLabel : Fin 5 ⊕ Bool → Nat
  | .inl z => z.val
  | .inr false => 5
  | .inr true => 6

-- The entire six-point merged cycle is traversed; the fifth old point stays fixed.
/-- info: [5, 3, 2, 6, 1, 0] -/
#guard_msgs in
#eval List.ofFn (fun k : Fin 6 => pointLabel ((joinedFaces ^ k.val) (.inr false)))

example : joinedFaces.SameCycle (.inr false) (.inr true) :=
  insertFacePermutation_fresh_sameCycle twoOldCycles 0 2 twoOldCycles_distinct

example : joinedFaces (.inl 4) = .inl 4 := by decide

example : ¬ joinedFaces.SameCycle (.inl 4) (.inl 0) := by
  have ha : ¬ twoOldCycles.SameCycle 4 0 := by
    intro h
    have heq := h.eq_of_left (show twoOldCycles 4 = 4 by decide)
    exact (by decide : (4 : Fin 5) ≠ 0) heq
  have hb : ¬ twoOldCycles.SameCycle 4 2 := by
    intro h
    have heq := h.eq_of_left (show twoOldCycles 4 = 4 by decide)
    exact (by decide : (4 : Fin 5) ≠ 2) heq
  exact fun h => ha ((insertFacePermutation_other_cycle_iff twoOldCycles 0 2 4 0
    twoOldCycles_distinct ha hb).mp h)

-- The before-corner convention is separately executed and theorem checked.
example : (insertFaceBeforePermutation twoOldCycles 0 2).SameCycle
    (.inr false) (.inr true) :=
  insertFaceBeforePermutation_fresh_sameCycle twoOldCycles 0 2 twoOldCycles_distinct

/-- info: [5, 2, 3, 6, 0, 1] -/
#guard_msgs in
#eval List.ofFn (fun k : Fin 6 => pointLabel
  ((insertFaceBeforePermutation twoOldCycles 0 2 ^ k.val) (.inr false)))
