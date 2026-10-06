module

import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeMass

open SimpleGraph SimpleGraph.Kempe

/-- info: 'SimpleGraph.Kempe.bichromaticSubgraph_swap_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bichromaticSubgraph_swap_pair

/-- info: 'SimpleGraph.Kempe.bichromaticSubgraph_swap_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bichromaticSubgraph_swap_disjoint

/-- info: 'SimpleGraph.Kempe.pairMass_swap_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairMass_swap_pair

/-- info: 'SimpleGraph.Kempe.pairMass_swap_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairMass_swap_disjoint

/-- info: 'SimpleGraph.Kempe.sixPairMass_swap_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sixPairMass_swap_change

/-- info: 'SimpleGraph.Kempe.pairMass_le_card_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairMass_le_card_sq

/-- info: 'SimpleGraph.Kempe.sixPairMass_le_six_card_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sixPairMass_le_six_card_sq

example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Fin 4) (a b : Fin 4) :
    pairMass G c ∅ a b = 0 := by
  classical
  simp [pairMass, boundaryPairComponents]

example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Fin 4) (a b : Fin 4) :
    pairMass G c Finset.univ a b = 0 := by
  classical
  simp [pairMass]

namespace KempeMassRegression

/-- A proper two-colouring of the four-cycle viewed as `K₂,₂`. -/
def colour (v : Fin 4) : Fin 4 := ⟨v.val % 2, by omega⟩

def graph : SimpleGraph (Fin 4) where
  Adj u v := colour u ≠ colour v
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

example : IsProperColouring graph colour := fun _ _ h => h

lemma active (v : Fin 4) : colour v = 0 ∨ colour v = 1 := by
  fin_cases v <;> decide

lemma connected (u v : Fin 4) : (bichromaticSubgraph graph colour 0 1).Reachable u v := by
  by_cases h : colour u = colour v
  · let w : Fin 4 := if colour u = 0 then 1 else 0
    have huw : graph.Adj u w := by
      unfold graph
      dsimp only
      fin_cases u <;> decide
    have hwv : graph.Adj w v := by
      change colour w ≠ colour v
      rw [← h]
      exact huw.symm
    exact SimpleGraph.Reachable.trans
      ⟨Walk.cons ⟨huw, active u, active w⟩ Walk.nil⟩
      ⟨Walk.cons ⟨hwv, active w, active v⟩ Walk.nil⟩
  · exact ⟨Walk.cons ⟨h, active u, active v⟩ Walk.nil⟩

lemma component (v : Fin 4) : pairComponent graph colour 0 1 v = Finset.univ := by
  classical
  ext w
  simp [pairComponent, connected]

/-- Two boundary representatives of one component must not count its mass twice. -/
lemma mass : pairMass graph colour {0, 1} 0 1 = 4 := by
  classical
  have hcomponents : boundaryPairComponents graph colour {0, 1} 0 1 =
      {Finset.univ} := by
    have hc : pairComponent graph colour 0 1 = fun _ => Finset.univ :=
      funext component
    simp [boundaryPairComponents, hc, active]
  rw [pairMass, hcomponents]
  simp only [Finset.sum_singleton]
  decide

/-- Even swapping an incomplete component leaves the pair mass unchanged.
The locality theorem itself does not assert preservation of properness. -/
example : pairMass graph (kempeSwap colour ({0} : Set (Fin 4)) 0 1) {0, 1} 0 1 = 4 := by
  classical
  rw [pairMass_swap_pair]
  exact mass

end KempeMassRegression
