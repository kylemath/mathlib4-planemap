/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationDelete

/-! # Edge deletion preserves the spherical filling property -/

@[expose] public section
namespace SimpleGraph.RotationSystem

open scoped BigOperators
variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem eraseGraph_mem_edgeSet (a : G.Dart) (e : Sym2 (Fin n)) :
    e ∈ (eraseGraph a).edgeSet ↔ e ∈ G.edgeSet ∧ e ≠ a.edge := by
  induction e using Sym2.ind with
  | _ u v => rfl

/-- Surviving edges viewed in the original graph. -/
def eraseEdge (a : G.Dart) (e : (eraseGraph a).edgeSet) : G.edgeSet :=
  ⟨e.val, ((eraseGraph_mem_edgeSet a e.val).mp e.property).1⟩

def eraseEdgeTotalEquiv (a : G.Dart) : (eraseGraph a).edgeSet ⊕ Unit ≃ G.edgeSet where
  toFun
    | .inl e => eraseEdge a e
    | .inr _ => edgeOfDart a
  invFun e := if h : e.val ≠ a.edge then
    .inl ⟨e.val, (eraseGraph_mem_edgeSet a e.val).mpr ⟨e.property, h⟩⟩ else .inr ()
  left_inv z := by
    classical
    cases z with
    | inl e =>
      have h := ((eraseGraph_mem_edgeSet a e.val).mp e.property).2
      dsimp only [eraseEdge]
      rw [dite_eq_left h]
    | inr u => cases u; simp [edgeOfDart]
  right_inv e := by
    classical
    dsimp only
    split_ifs with h
    · rfl
    · apply Subtype.ext
      exact (not_ne_iff.mp h).symm

/-- Lift an edge combination by assigning coefficient zero to the removed edge. -/
noncomputable def extendErase (a : G.Dart) (φ : (eraseGraph a).edgeSet → ZMod 2)
    (e : G.edgeSet) : ZMod 2 :=
  match (eraseEdgeTotalEquiv a).symm e with
  | .inl e => φ e
  | .inr _ => 0

@[simp] theorem extendErase_old (a : G.Dart) (φ : (eraseGraph a).edgeSet → ZMod 2)
    (e : (eraseGraph a).edgeSet) : extendErase a φ (eraseEdge a e) = φ e := by
  change extendErase a φ ((eraseEdgeTotalEquiv a) (.inl e)) = φ e
  simp [extendErase]

@[simp] theorem extendErase_new (a : G.Dart) (φ : (eraseGraph a).edgeSet → ZMod 2) :
    extendErase a φ (edgeOfDart a) = 0 := by
  change extendErase a φ ((eraseEdgeTotalEquiv a) (.inr ())) = 0
  simp [extendErase]

/-- Extension by zero preserves the incidence boundary. -/
theorem incidence_extendErase (a : G.Dart) (φ : (eraseGraph a).edgeSet → ZMod 2)
    (x : Fin n) : edgeIncidence G (extendErase a φ) x =
      edgeIncidence (eraseGraph a) φ x := by
  classical
  let E := eraseEdgeTotalEquiv a
  have hh := Fintype.sum_equiv E
    (fun z => if x ∈ (E z).val then extendErase a φ (E z) else 0)
    (fun e => if x ∈ e.val then extendErase a φ e else 0) (fun _ => rfl)
  rw [Fintype.sum_sum_type] at hh
  have hleft : (∑ e : (eraseGraph a).edgeSet,
      if x ∈ (E (.inl e)).val then extendErase a φ (E (.inl e)) else 0) =
      edgeIncidence (eraseGraph a) φ x := by
    unfold edgeIncidence
    apply Finset.sum_congr rfl
    intro e _
    change (if x ∈ e.val then extendErase a φ (eraseEdge a e) else 0) = _
    rw [extendErase_old]
  have hright : (∑ u : Unit,
      if x ∈ (E (.inr u)).val then extendErase a φ (E (.inr u)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    change (if x ∈ (edgeOfDart a).val then extendErase a φ (edgeOfDart a) else 0) = 0
    simp
  rw [hleft, hright, add_zero] at hh
  exact hh.symm

private theorem eq_of_add_zero (a b : ZMod 2) (h : a + b = 0) : a = b := by
  have hb : b + b = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
  calc
    a = a + (b + b) := by rw [hb, add_zero]
    _ = (a + b) + b := (add_assoc _ _ _).symm
    _ = b := by rw [h, zero_add]

/-- Removing an edge preserves the filling property, including bridge removal. -/
theorem fills_eraseRotation (R : RotationSystem G) (hR : R.Fills) (a : G.Dart) :
    (R.eraseRotation a).Fills := by
  classical
  intro φ hφ
  let φG := extendErase a φ
  obtain ⟨c, hc⟩ := hR φG (fun x => (incidence_extendErase a φ x).trans (hφ x))
  let k : G.Dart → ZMod 2 := fun d => c (R.faceOf d)
  have hzero : φG (edgeOfDart a) = 0 := extendErase_new a φ
  have hea : k a = k a.symm := eq_of_add_zero _ _ ((hc a).symm.trans hzero)
  have hka : k a = k (R.next a) := by
    have hh := congrArg c (R.face_of_face_next a.symm)
    change k (R.next a) = k a.symm at hh
    exact hea.trans hh.symm
  have hkas : k a.symm = k (R.next a.symm) := by
    have hh := congrArg c (R.face_of_face_next a)
    change k (R.next a.symm) = k a at hh
    exact hea.symm.trans hh.symm
  have obs1 (z : G.Dart) : k (R.next.erasePoint a z) = k (R.next z) :=
    Equiv.Perm.erasePoint_observe R.next a k hka z
  have obs (z : G.Dart) : k (R.eraseNext a z) = k (R.next z) :=
    (Equiv.Perm.erasePoint_observe (R.next.erasePoint a) a.symm k
      (hkas.trans (obs1 a.symm).symm) z).trans (obs1 z)
  let R' := R.eraseRotation a
  let k' : (eraseGraph a).Dart → ZMod 2 := fun d => k (eraseDart a d)
  have hface (d : (eraseGraph a).Dart) : k' (R'.faceNext d) = k' d := by
    change k (eraseDart a ((R.eraseRotation a).next d.symm)) = k (eraseDart a d)
    rw [eraseRotation_next, eraseDart_symm, obs]
    exact congrArg c (R.face_of_face_next (eraseDart a d))
  have hrel : ∀ d e, R'.FaceRelation d e → k' d = k' e := by
    intro d e h
    induction h with
    | refl => rfl
    | step d => exact (hface d).symm
    | symm h ih => exact ih.symm
    | trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  let c' : R'.Face → ZMod 2 := Sum.elim (Quotient.lift k' hrel) (fun _ => 0)
  refine ⟨c', fun d => ?_⟩
  have he : edgeOfDart (eraseDart a d) = eraseEdge a (edgeOfDart d) := by
    apply Subtype.ext
    rfl
  have hh := hc (eraseDart a d)
  rw [he] at hh
  change extendErase a φ (eraseEdge a (edgeOfDart d)) = _ at hh
  rw [extendErase_old] at hh
  exact hh

end SimpleGraph.RotationSystem

namespace SimpleGraph.SphericalMap
variable {n : ℕ}

/-- The algebraic spherical carrier after deleting one edge. -/
noncomputable def eraseEdge (M : SphericalMap n) (a : M.Dart) : SphericalMap n where
  graph := RotationSystem.eraseGraph a
  rotation := M.rotation.eraseRotation a
  fills := M.rotation.fills_eraseRotation M.fills a

end SimpleGraph.SphericalMap

namespace SimpleGraph.SphericalMap
variable {n : ℕ}

/-- Every spanning subgraph has a spherical rotation system, proved by deleting
edges one at a time. Isolated vertices and disconnected subgraphs are allowed. -/
theorem subgraph_closed (M : SphericalMap n) (H : SimpleGraph (Fin n))
    (hsub : H ≤ M.graph) : ∃ N : SphericalMap n, N.graph = H := by
  classical
  generalize hk : Fintype.card M.graph.edgeSet = k
  induction k using Nat.strong_induction_on generalizing M H with
  | h k ih =>
    by_cases heq : M.graph = H
    · exact ⟨M, heq⟩
    · have hex : ∃ u v, M.Adj u v ∧ ¬ H.Adj u v := by
        by_contra hh
        push Not at hh
        exact heq (le_antisymm (fun u v huv => hh u v huv) hsub)
      obtain ⟨u, v, huv, hnot⟩ := hex
      let a : M.Dart := ⟨(u, v), huv⟩
      let N := M.eraseEdge a
      have hcount : Fintype.card N.graph.edgeSet < k := by
        have hh := Fintype.card_congr (RotationSystem.eraseEdgeTotalEquiv a)
        simp only [Fintype.card_sum, Fintype.card_unit] at hh
        change Fintype.card N.graph.edgeSet + 1 = Fintype.card M.graph.edgeSet at hh
        omega
      have hsub' : H ≤ N.graph := by
        intro x y hxy
        refine ⟨hsub hxy, ?_⟩
        intro he
        have hemem : s(x, y) ∈ H.edgeSet := hxy
        rw [he] at hemem
        exact hnot hemem
      exact ih _ hcount N H hsub' rfl

/-- Delete all edges incident to a vertex, retaining its isolated label. -/
def isolateGraph (M : SphericalMap n) (x : Fin n) : SimpleGraph (Fin n) where
  Adj u v := M.Adj u v ∧ u ≠ x ∧ v ≠ x
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- Vertex deletion closes the carrier as a spanning graph with an isolated label.
The number of edges strictly decreases whenever the vertex is nonisolated. -/
theorem isolate_closed (M : SphericalMap n) (x : Fin n)
    (hx : 0 < M.graph.degree x) :
    ∃ N : SphericalMap n, N.graph = M.isolateGraph x ∧
      Fintype.card N.graph.edgeSet < Fintype.card M.graph.edgeSet := by
  classical
  obtain ⟨N, hN⟩ := M.subgraph_closed (M.isolateGraph x) (fun _ _ h => h.1)
  refine ⟨N, hN, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hN]
  let f : (M.isolateGraph x).edgeSet → M.graph.edgeSet :=
    fun e => ⟨e.val,
      edgeSet_mono (show M.isolateGraph x ≤ M.graph from fun _ _ h => h.1) e.property⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun e : M.graph.edgeSet => e.val) h)
  obtain ⟨y, hxy⟩ := M.graph.mem_support.mp ((M.graph.degree_pos_iff_mem_support x).mp hx)
  let a : M.Dart := ⟨(x, y), hxy⟩
  have hmiss : RotationSystem.edgeOfDart a ∉ Set.range f := by
    rintro ⟨e, he⟩
    have hev := congrArg Subtype.val he
    change e.val = s(x, y) at hev
    have hh : s(x, y) ∈ (M.isolateGraph x).edgeSet := hev ▸ e.property
    exact hh.2.1 rfl
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem f hf hmiss

end SimpleGraph.SphericalMap
