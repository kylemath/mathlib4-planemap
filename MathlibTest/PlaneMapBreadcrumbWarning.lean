module
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.BreadcrumbWarning
import Mathlib.Tactic.FinCases

/-- info: 'Breadcrumb.not_good_of_warnStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Breadcrumb.not_good_of_warnStep
/-- info: 'Breadcrumb.not_good_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Breadcrumb.not_good_of_reachable
/-- info: 'Breadcrumb.card_le_deadEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Breadcrumb.card_le_deadEnd
/-- info: 'Breadcrumb.card_warnStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Breadcrumb.card_warnStep
/-- info: 'Breadcrumb.good_of_forall_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Breadcrumb.good_of_forall_descent

namespace BreadcrumbRegression

/-- A three-state descending chain: 2 → 1 → 0, with 0 the only target. -/
def rank : Fin 3 → ℕ := Fin.val
def Tgt (x : Fin 3) : Prop := x = 0
def M2 (x z : Fin 3) : Prop := z.val + 1 = x.val

-- Every non-target state descends, so every state is good: the dead-end region is empty.
example : ∀ x, Breadcrumb.Good rank Tgt M2 x :=
  Breadcrumb.good_of_forall_descent (fun x hx => by
    fin_cases x
    · exact absurd rfl hx
    · exact ⟨0, rfl, by decide⟩
    · exact ⟨1, rfl, by decide⟩)

-- Hence no reachable warning set can contain any state.
example (W : Finset (Fin 3))
    (h : Relation.ReflTransGen (Breadcrumb.Step rank Tgt M2) ∅ W) : W = ∅ := by
  have hall : ∀ x, Breadcrumb.Good rank Tgt M2 x :=
    Breadcrumb.good_of_forall_descent (fun x hx => by
      fin_cases x
      · exact absurd rfl hx
      · exact ⟨0, rfl, by decide⟩
      · exact ⟨1, rfl, by decide⟩)
  ext w
  simp only [Finset.notMem_empty, iff_false]
  intro hw
  exact Breadcrumb.not_good_of_reachable h w hw (hall w)

end BreadcrumbRegression
