module

import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeRepartition

open SimpleGraph SimpleGraph.Kempe

/-- info: 'SimpleGraph.Kempe.kempeSwap_eq_left_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms kempeSwap_eq_left_iff
/-- info: 'SimpleGraph.Kempe.kempeSwap_eq_right_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms kempeSwap_eq_right_iff
/-- info: 'SimpleGraph.Kempe.kempeSwap_eq_other_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms kempeSwap_eq_other_iff
/-- info: 'SimpleGraph.Kempe.mixedActive_kempeSwap_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixedActive_kempeSwap_left
/-- info: 'SimpleGraph.Kempe.mixedActive_kempeSwap_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixedActive_kempeSwap_right
/-- info: 'SimpleGraph.Kempe.mixedCarrier_kempeSwap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mixedCarrier_kempeSwap
/-- info: 'SimpleGraph.Kempe.mixedFixedGraph_kempeSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixedFixedGraph_kempeSwap
/-- info: 'SimpleGraph.Kempe.bichromatic_sup_eq_mixedFixedGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bichromatic_sup_eq_mixedFixedGraph
/-- info: 'SimpleGraph.Kempe.bichromatic_eq_restrict_mixedFixedGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bichromatic_eq_restrict_mixedFixedGraph
/-- info: 'SimpleGraph.Kempe.bichromatic_kempeSwap_eq_repartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bichromatic_kempeSwap_eq_repartition
/-- info: 'SimpleGraph.Kempe.bichromatic_kempeSwap_eq_repartition_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bichromatic_kempeSwap_eq_repartition_right

namespace RepartitionRegression

/-- A path on 0,1,2, an edge on 3,4, and an isolated vertex 5. -/
def graph : SimpleGraph (Fin 6) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
    (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
    (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 3)
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro v; omega⟩

instance : DecidableRel graph.Adj := by
  intro u v
  dsimp [graph]
  infer_instance

def colour (v : Fin 6) : Fin 4 := if v = 0 ∨ v = 4 then 0 else if v = 2 then 1 else 2

def swapSet : Set (Fin 6) := {0}

instance : DecidablePred (· ∈ swapSet) := by
  intro v
  dsimp [swapSet]
  infer_instance

def swapped := kempeSwap colour swapSet 0 1

lemma proper : IsProperColouring graph colour := by
  intro u v huv
  fin_cases u <;> fin_cases v <;> simp_all [graph, colour]

lemma swapped_proper : IsProperColouring graph swapped := by
  intro u v huv
  fin_cases u <;> fin_cases v <;> simp_all [graph, colour, swapped, swapSet, kempeSwap]

-- One edge transfers from the left mixed pair to the right mixed pair.
example : (bichromaticSubgraph graph colour 0 2).Adj 0 1 := by
  simp [bichromaticSubgraph, bichromaticAdj, graph, colour]
example : ¬ (bichromaticSubgraph graph swapped 0 2).Adj 0 1 := by
  simp [bichromaticSubgraph, bichromaticAdj, graph, colour, swapped, swapSet, kempeSwap]
example : (bichromaticSubgraph graph swapped 1 2).Adj 0 1 := by
  simp [bichromaticSubgraph, bichromaticAdj, graph, colour, swapped, swapSet, kempeSwap]
example : mixedFixedGraph graph swapped 0 1 2 = mixedFixedGraph graph colour 0 1 2 :=
  mixedFixedGraph_kempeSwap graph colour swapSet 0 1 2 (by decide) (by decide) (by decide)

-- The isolated third-colour vertex is explicitly active in both descriptions.
example : (5 : Fin 6) ∈ mixedActive colour 0 2 := by
  simp [mixedActive, colour]
example : (5 : Fin 6) ∈ mixedActive swapped 0 2 := by
  simp [mixedActive, colour, swapped, swapSet, kempeSwap]
example : ∀ v, ¬ graph.Adj 5 v := by intro v; simp [graph]

example : bichromaticSubgraph graph swapped 0 2 =
    restrictAmbient (mixedFixedGraph graph colour 0 1 2)
      {v | (v ∉ swapSet ∧ colour v = 0) ∨ (v ∈ swapSet ∧ colour v = 1) ∨
        colour v = 2} :=
  bichromatic_kempeSwap_eq_repartition graph colour swapSet 0 1 2
    (by decide) (by decide) (by decide) swapped_proper

example : bichromaticSubgraph graph colour 0 2 ⊔ bichromaticSubgraph graph colour 1 2 =
    mixedFixedGraph graph colour 0 1 2 :=
  bichromatic_sup_eq_mixedFixedGraph graph colour 0 1 2 proper

end RepartitionRegression
