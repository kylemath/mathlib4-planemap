module

import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyShortFill

open SimpleGraph
open SimpleGraph.VacancySlide
open SimpleGraph.VacancyShortFill

namespace VacancyShortFillTest

/-- A degree-two original hole: the theorem has no degree-five restriction. -/
def star : SimpleGraph (Fin 3) where
  Adj x y := x ≠ y ∧ (x = 0 ∨ y = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel star.Adj := fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (_ = 0 ∨ _ = 0)))

def colours (v : Fin 3) : Fin 2 := if v = 1 then 1 else 0

lemma proper : ProperOff star 0 colours := by unfold ProperOff; decide
lemma unique : UniqueAt star 0 1 colours := by unfold UniqueAt; decide
lemma not_target : ¬ Target star 0 colours := by unfold Target Missing; decide
lemma filled : Target star 1 (slide 0 1 colours) := by unfold Target Missing; decide

example : PureFill star 0 colours 1 :=
  pureFill_one star (terminal_slide star proper (u := 1) (by decide) unique filled)

example : PureOptimal star 0 colours 1 := by
  apply optimal_short star proper (by decide)
  constructor
  · exact ⟨(1,slide 0 1 colours),.cons (.slide (by decide) unique) (.nil _),filled⟩
  · intro m hm ⟨t,path,filled⟩
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hm)
    subst m
    cases path
    exact not_target filled

end VacancyShortFillTest

/--
info: 'SimpleGraph.VacancyShortFill.terminal_slide' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SimpleGraph.VacancyShortFill.terminal_slide
/--
info: 'SimpleGraph.VacancyShortFill.slide_swap_same' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SimpleGraph.VacancyShortFill.slide_swap_same
/--
info: 'SimpleGraph.VacancyShortFill.slide_kempe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SimpleGraph.VacancyShortFill.slide_kempe
/--
info: 'SimpleGraph.VacancyShortFill.short_fill' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SimpleGraph.VacancyShortFill.short_fill
/--
info: 'SimpleGraph.VacancyShortFill.optimal_short' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SimpleGraph.VacancyShortFill.optimal_short

#print SimpleGraph.VacancyShortFill.short_fill
#print SimpleGraph.VacancyShortFill.optimal_short
