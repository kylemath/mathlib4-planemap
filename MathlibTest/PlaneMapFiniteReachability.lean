import Mathlib.Combinatorics.SimpleGraph.Coloring.FiniteReachability
open SimpleGraph SimpleGraph.FiniteReachability

namespace PlaneMapFiniteReachabilityTest
-- Components remain separate even though both contain edges.
def paired : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
    (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2)
  symm := ⟨by intro u v h; aesop⟩
  loopless := ⟨by intro u h; rcases h with h | h | h | h <;> omega⟩
instance : DecidableRel paired.Adj := fun u v => inferInstanceAs
  (Decidable ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
    (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2)))
def labels (v : Fin 4) : Fin 4 := if v = 0 ∨ v = 2 then 0 else 1
/-- info: [0, 1] -/
#guard_msgs in
#eval (component paired 0).sort (· ≤ ·)
/-- info: [1, 0, 0, 1] -/
#guard_msgs in
#eval List.ofFn (componentSwap paired labels 0 1 0)
/-- info: true -/
#guard_msgs in
#eval ((component paired 0).card = 2 && 2 ∉ component paired 0)
example : component paired 0 = {0, 1} := by decide
example : List.ofFn (componentSwap paired labels 0 1 0) = [1, 0, 0, 1] := by decide
/-- info: 'SimpleGraph.FiniteReachability.expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.FiniteReachability.expand
/-- info: 'SimpleGraph.FiniteReachability.component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.FiniteReachability.component
/-- info: 'SimpleGraph.FiniteReachability.componentSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.FiniteReachability.componentSwap
/-- info: 'SimpleGraph.FiniteReachability.mem_component_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.FiniteReachability.mem_component_iff
/-- info: 'SimpleGraph.FiniteReachability.componentSwap_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.FiniteReachability.componentSwap_proper
/-- info: 'SimpleGraph.FiniteReachability.component_scanBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.FiniteReachability.component_scanBudget
example : Kempe.IsProperColouring paired labels := by
  intro u v huv
  fin_cases u <;> fin_cases v
  all_goals simp_all [paired, labels]
example : Kempe.IsProperColouring paired (componentSwap paired labels 0 1 0) := by
  apply componentSwap_proper paired labels 0 1 (by decide) 0 (by decide)
  intro u v huv
  fin_cases u <;> fin_cases v
  all_goals simp_all [paired, labels]
/-- info: 64 -/
#guard_msgs in
#eval (scannedRounds paired {0} 4).2
example : (scannedRounds paired {0} 4).2 = 64 := by decide

end PlaneMapFiniteReachabilityTest
