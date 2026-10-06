module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Kempe
public import Mathlib.Tactic

/-!
# Repartitioning the fixed mixed-colour graph

A swap of two colours preserves the graph joining a third colour to their union.
Explicit active vertex sets accompany graphs on the fixed ambient vertex type;
vertices with no incident edge are therefore retained in the descriptions.
No connectedness or properness is required for the swap identities. Properness
is used only to identify the union and restrictions of bichromatic subgraphs.
-/

@[expose] public section
namespace SimpleGraph.Kempe

variable {V : Type*} {k : ℕ}

/-- The active vertices of a bichromatic graph, including its isolated vertices. -/
def mixedActive (c : V → Fin k) (a e : Fin k) : Set V :=
  {v | c v = a ∨ c v = e}

/-- The fixed active carrier of the two mixed pairs. -/
def mixedCarrier (c : V → Fin k) (a b e : Fin k) : Set V :=
  {v | c v = a ∨ c v = b ∨ c v = e}

/-- Keep only edges from the third colour to the two swap colours. -/
def mixedFixedGraph (G : SimpleGraph V) (c : V → Fin k)
    (a b e : Fin k) : SimpleGraph V where
  Adj u v := G.Adj u v ∧
    ((c u = e ∧ (c v = a ∨ c v = b)) ∨
     ((c u = a ∨ c u = b) ∧ c v = e))
  symm := ⟨by
    intro u v h
    have hs := h.1.symm
    aesop⟩
  loopless := ⟨by intro v h; exact h.1.ne rfl⟩

/-- Restrict edges to an active set while keeping the ambient vertex type. -/
def restrictAmbient (G : SimpleGraph V) (A : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ A ∧ v ∈ A
  symm := ⟨by
    intro u v h
    have hs := h.1.symm
    aesop⟩
  loopless := ⟨by intro v h; exact h.1.ne rfl⟩

lemma kempeSwap_eq_left_iff (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b : Fin k) (hab : a ≠ b) (v : V) :
    kempeSwap c S a b v = a ↔
      (v ∉ S ∧ c v = a) ∨ (v ∈ S ∧ c v = b) := by
  by_cases hv : v ∈ S <;> by_cases ha : c v = a <;>
    by_cases hb : c v = b <;> simp_all [kempeSwap, Ne.symm hab]

lemma kempeSwap_eq_right_iff (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b : Fin k) (hab : a ≠ b) (v : V) :
    kempeSwap c S a b v = b ↔
      (v ∉ S ∧ c v = b) ∨ (v ∈ S ∧ c v = a) := by
  by_cases hv : v ∈ S <;> by_cases ha : c v = a <;>
    by_cases hb : c v = b <;> simp_all [kempeSwap, Ne.symm hab]

lemma kempeSwap_eq_other_iff (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b e : Fin k) (hea : e ≠ a) (heb : e ≠ b)
    (v : V) : kempeSwap c S a b v = e ↔ c v = e := by
  by_cases hv : v ∈ S <;> by_cases ha : c v = a <;>
    by_cases hb : c v = b <;> simp_all [kempeSwap, Ne.symm hea, Ne.symm heb]

lemma mixedActive_kempeSwap_left (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b e : Fin k)
    (hab : a ≠ b) (hea : e ≠ a) (heb : e ≠ b) :
    mixedActive (kempeSwap c S a b) a e =
      {v | (v ∉ S ∧ c v = a) ∨ (v ∈ S ∧ c v = b) ∨ c v = e} := by
  ext v
  simp only [mixedActive, Set.mem_ofPred_eq,
    kempeSwap_eq_left_iff c S a b hab, kempeSwap_eq_other_iff c S a b e hea heb]
  tauto

lemma mixedActive_kempeSwap_right (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b e : Fin k)
    (hab : a ≠ b) (hea : e ≠ a) (heb : e ≠ b) :
    mixedActive (kempeSwap c S a b) b e =
      {v | (v ∉ S ∧ c v = b) ∨ (v ∈ S ∧ c v = a) ∨ c v = e} := by
  ext v
  simp only [mixedActive, Set.mem_ofPred_eq,
    kempeSwap_eq_right_iff c S a b hab, kempeSwap_eq_other_iff c S a b e hea heb]
  tauto

lemma mixedCarrier_kempeSwap (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b e : Fin k)
    (hab : a ≠ b) (hea : e ≠ a) (heb : e ≠ b) :
    mixedCarrier (kempeSwap c S a b) a b e = mixedCarrier c a b e := by
  ext v
  simp only [mixedCarrier, Set.mem_ofPred_eq,
    kempeSwap_eq_left_iff c S a b hab, kempeSwap_eq_right_iff c S a b hab,
    kempeSwap_eq_other_iff c S a b e hea heb]
  by_cases hv : v ∈ S <;> simp [hv, or_comm, or_left_comm]

lemma mixedFixedGraph_kempeSwap (G : SimpleGraph V) (c : V → Fin k)
    (S : Set V) [DecidablePred (· ∈ S)] (a b e : Fin k)
    (hab : a ≠ b) (hea : e ≠ a) (heb : e ≠ b) :
    mixedFixedGraph G (kempeSwap c S a b) a b e = mixedFixedGraph G c a b e := by
  ext u v
  simp only [mixedFixedGraph,
    kempeSwap_eq_left_iff c S a b hab, kempeSwap_eq_right_iff c S a b hab,
    kempeSwap_eq_other_iff c S a b e hea heb]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv] <;> tauto

lemma bichromatic_sup_eq_mixedFixedGraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b e : Fin k) (hproper : IsProperColouring G c) :
    bichromaticSubgraph G c a e ⊔ bichromaticSubgraph G c b e =
      mixedFixedGraph G c a b e := by
  ext u v
  change (G.Adj u v ∧ (c u = a ∨ c u = e) ∧ (c v = a ∨ c v = e)) ∨
      (G.Adj u v ∧ (c u = b ∨ c u = e) ∧ (c v = b ∨ c v = e)) ↔ _
  change _ ↔ G.Adj u v ∧
    ((c u = e ∧ (c v = a ∨ c v = b)) ∨ ((c u = a ∨ c u = b) ∧ c v = e))
  by_cases h : G.Adj u v
  · have hn := hproper u v h
    aesop
  · simp [h]

lemma bichromatic_eq_restrict_mixedFixedGraph (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Fin k) (a b e : Fin k)
    (hab : a ≠ b) (hea : e ≠ a) (heb : e ≠ b)
    (hproper : IsProperColouring G c) :
    bichromaticSubgraph G c a e =
      restrictAmbient (mixedFixedGraph G c a b e) (mixedActive c a e) := by
  ext u v
  change (G.Adj u v ∧ (c u = a ∨ c u = e) ∧ (c v = a ∨ c v = e)) ↔ _
  change _ ↔ (G.Adj u v ∧
    ((c u = e ∧ (c v = a ∨ c v = b)) ∨ ((c u = a ∨ c u = b) ∧ c v = e))) ∧
    (c u = a ∨ c u = e) ∧ (c v = a ∨ c v = e)
  by_cases h : G.Adj u v
  · have hn := hproper u v h
    aesop
  · simp [h]

/-- The new mixed graph is a restriction of the old fixed graph to the
repartitioned active set. Properness of the new colouring is explicit. -/
lemma bichromatic_kempeSwap_eq_repartition (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Fin k) (S : Set V) [DecidablePred (· ∈ S)]
    (a b e : Fin k) (hab : a ≠ b) (hea : e ≠ a) (heb : e ≠ b)
    (hproper : IsProperColouring G (kempeSwap c S a b)) :
    bichromaticSubgraph G (kempeSwap c S a b) a e =
      restrictAmbient (mixedFixedGraph G c a b e)
        {v | (v ∉ S ∧ c v = a) ∨ (v ∈ S ∧ c v = b) ∨ c v = e} := by
  rw [bichromatic_eq_restrict_mixedFixedGraph G _ a b e hab hea heb hproper,
    mixedFixedGraph_kempeSwap G c S a b e hab hea heb,
    mixedActive_kempeSwap_left c S a b e hab hea heb]

/-- Symmetric repartition for the other mixed pair. -/
lemma bichromatic_kempeSwap_eq_repartition_right (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Fin k) (S : Set V) [DecidablePred (· ∈ S)]
    (a b e : Fin k) (hab : a ≠ b) (hea : e ≠ a) (heb : e ≠ b)
    (hproper : IsProperColouring G (kempeSwap c S a b)) :
    bichromaticSubgraph G (kempeSwap c S a b) b e =
      restrictAmbient (mixedFixedGraph G c a b e)
        {v | (v ∉ S ∧ c v = b) ∨ (v ∈ S ∧ c v = a) ∨ c v = e} := by
  have hsymm (d : V → Fin k) : mixedFixedGraph G d b a e =
      mixedFixedGraph G d a b e := by
    ext u v
    simp only [mixedFixedGraph]
    tauto
  rw [bichromatic_eq_restrict_mixedFixedGraph G _ b a e hab.symm heb hea hproper,
    hsymm, mixedFixedGraph_kempeSwap G c S a b e hab hea heb,
    mixedActive_kempeSwap_right c S a b e hab hea heb]

end SimpleGraph.Kempe
