/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Kempe
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

/-! # Executable finite components and Kempe swaps

The component routine performs `card V` finite frontier expansions. Its correctness
uses the simple-path bound; no classical decision procedure occurs in the executable data.
-/
@[expose] public section
namespace SimpleGraph.FiniteReachability
variable {k : ℕ}
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def expand (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter (fun v => ∃ u ∈ S, G.Adj u v)

def component (x : V) : Finset V := (expand G)^[Fintype.card V] {x}

lemma subset_expand (S : Finset V) : S ⊆ expand G S := Finset.subset_union_left

lemma iterate_mono_time {i j : ℕ} (h : i ≤ j) (S : Finset V) :
    (expand G)^[i] S ⊆ (expand G)^[j] S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, Function.iterate_succ_apply']
    exact Finset.Subset.trans ih (subset_expand G _)

lemma walk_mem_iterate {u v : V} (p : G.Walk u v) (S : Finset V) (hu : u ∈ S) :
    v ∈ (expand G)^[p.length] S := by
  induction p generalizing S with
  | nil => simpa using hu
  | @cons u v w h p ih =>
    rw [Walk.length_cons, Function.iterate_succ_apply]
    apply ih
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, u, hu, h⟩)

lemma iterate_reachable (x : V) (i : ℕ) :
    ∀ v ∈ (expand G)^[i] {x}, G.Reachable x v := by
  induction i with
  | zero => intro v hv; simpa using (show G.Reachable x x from Reachable.refl x)
      |> fun h => by simpa using (Finset.mem_singleton.mp hv ▸ h)
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ih v hv
    · obtain ⟨_, u, hu, huv⟩ := Finset.mem_filter.mp hv
      exact (ih u hu).trans huv.reachable

theorem mem_component_iff (x v : V) : v ∈ component G x ↔ G.Reachable x v := by
  constructor
  · exact iterate_reachable G x _ v
  · intro h
    apply h.elim_path
    intro p
    exact iterate_mono_time G (Nat.le_of_lt p.property.length_lt) {x}
      (walk_mem_iterate G p.val {x} (Finset.mem_singleton_self x))

instance bichromaticDecidable (c : V → Fin k) (a b : Fin k) :
    DecidableRel (Kempe.bichromaticSubgraph G c a b).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧
    (c u = a ∨ c u = b) ∧ (c v = a ∨ c v = b)))

def componentSwap (c : V → Fin k) (a b : Fin k) (x : V) : V → Fin k :=
  Kempe.kempeSwap c (component (Kempe.bichromaticSubgraph G c a b) x : Set V) a b

theorem componentSwap_eq (c : V → Fin k) (a b : Fin k) (x : V) :
    componentSwap G c a b x = Kempe.kempeSwap c (Kempe.kempeChain G c a b x) a b := by
  classical
  funext v
  unfold componentSwap Kempe.kempeSwap
  change (if v ∈ component (Kempe.bichromaticSubgraph G c a b) x then
    (if c v = a then b else if c v = b then a else c v) else c v) =
    (if (Kempe.bichromaticSubgraph G c a b).Reachable x v then
    (if c v = a then b else if c v = b then a else c v) else c v)
  have hm := mem_component_iff (Kempe.bichromaticSubgraph G c a b) x v
  by_cases h : (Kempe.bichromaticSubgraph G c a b).Reachable x v
  · rw [ite_eq_left (hm.mpr h), ite_eq_left h]
  · have hn : v ∉ component (Kempe.bichromaticSubgraph G c a b) x :=
      fun hv => h (hm.mp hv)
    rw [ite_eq_right hn, ite_eq_right h]

theorem componentSwap_proper (c : V → Fin k) (a b : Fin k) (hab : a ≠ b)
    (x : V) (hx : c x = a) (hc : Kempe.IsProperColouring G c) :
    Kempe.IsProperColouring G (componentSwap G c a b x) := by
  rw [componentSwap_eq]
  exact Kempe.kempeSwap_chain_proper G c a b hab x hx hc

/-- Charge a full `vertices × vertices` adjacency scan per frontier expansion.
This abstract accounting model excludes representation and compiler runtime costs. -/
def scannedRounds (S : Finset V) : ℕ → Finset V × ℕ
  | 0 => (S, 0)
  | t + 1 =>
    let previous := scannedRounds S t
    (expand G previous.1, previous.2 + Fintype.card V * Fintype.card V)

theorem scannedRounds_result (S : Finset V) (t : ℕ) :
    (scannedRounds G S t).1 = (expand G)^[t] S := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [scannedRounds, ih, Function.iterate_succ_apply']

theorem scannedRounds_budget (S : Finset V) (t : ℕ) :
    (scannedRounds G S t).2 = t * Fintype.card V * Fintype.card V := by
  induction t with
  | zero => simp [scannedRounds]
  | succ t ih => simp only [scannedRounds, ih]; ring

theorem component_scanBudget (x : V) :
    (scannedRounds G {x} (Fintype.card V)).2 = Fintype.card V ^ 3 := by
  rw [scannedRounds_budget]
  ring

end SimpleGraph.FiniteReachability
