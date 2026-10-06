/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalMap
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalDelete
public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section
namespace SimpleGraph.SphericalMap
open scoped BigOperators

variable {n s : ℕ} (M : SphericalMap n) (i : M.graph.support ≃ Fin s)

/-- The old label of a support label. -/
def supportLabel (x : Fin s) : Fin n := (i.symm x).val

def supportGraph : SimpleGraph (Fin s) := M.graph.comap (supportLabel M i)

noncomputable instance : DecidableRel (supportGraph M i).Adj := Classical.decRel _

@[simp] theorem supportGraph_adj (x y : Fin s) :
    (supportGraph M i).Adj x y ↔ M.graph.Adj (supportLabel M i x) (supportLabel M i y) := Iff.rfl

def supportEmbedding : supportGraph M i ↪g M.graph where
  toFun := supportLabel M i
  inj' := fun _ _ h => i.symm.injective (Subtype.ext h)
  map_rel_iff' := Iff.rfl

/-- All darts survive removal of isolated labels. -/
def supportDartEquiv : (supportGraph M i).Dart ≃ M.Dart where
  toFun d := ⟨(supportLabel M i d.fst, supportLabel M i d.snd), d.adj⟩
  invFun d := ⟨(i ⟨d.fst, d.adj.mem_support_left⟩,
      i ⟨d.snd, d.adj.mem_support_right⟩), by simp [supportGraph, supportLabel]⟩
  left_inv d := by apply Dart.ext; simp [supportLabel]
  right_inv d := by apply Dart.ext; simp [supportLabel]

@[simp] theorem supportDartEquiv_symm (d : (supportGraph M i).Dart) :
    supportDartEquiv M i d.symm = (supportDartEquiv M i d).symm := rfl

/-- Conjugate the rotation, preserving its cyclic order. -/
def supportRotation : RotationSystem (supportGraph M i) where
  next := (supportDartEquiv M i).trans (M.rotation.next.trans (supportDartEquiv M i).symm)
  next_fst d := by
    change i ⟨(M.rotation.next (supportDartEquiv M i d)).fst, _⟩ = d.fst
    simp only [M.rotation.next_fst]
    simp [supportDartEquiv, supportLabel]
  cyclic d e h := by
    have hfst : (supportDartEquiv M i d).fst = (supportDartEquiv M i e).fst :=
      congrArg (supportLabel M i) h
    obtain ⟨k, hk⟩ := M.rotation.cyclic _ _ hfst
    refine ⟨k, (supportDartEquiv M i).injective ?_⟩
    have hc : Function.Semiconj (supportDartEquiv M i)
        ((supportDartEquiv M i).trans (M.rotation.next.trans (supportDartEquiv M i).symm))
        M.rotation.next := by intro a; simp
    exact (hc.iterate_right k d).trans hk

@[simp] theorem supportRotation_faceNext (d : (supportGraph M i).Dart) :
    supportDartEquiv M i ((supportRotation M i).faceNext d) =
      M.rotation.faceNext (supportDartEquiv M i d) := by
  simp [supportRotation, RotationSystem.face_next_apply]

/-- A face orbit after support relabelling maps to its original orbit. -/
def supportFaceMap : (supportRotation M i).Face → M.Face
  | .inl q => .inl (Quotient.map (supportDartEquiv M i) (by
      intro d e h
      exact RotationSystem.FaceRelation.map _ (by
        intro a
        rw [supportRotation_faceNext]
        exact .step _) h) q)
  | .inr h => .inr ⟨(), ⟨fun d => h.property.false ((supportDartEquiv M i).symm d)⟩⟩

@[simp] theorem supportFaceMap_faceOf (d : (supportGraph M i).Dart) :
    supportFaceMap M i ((supportRotation M i).faceOf d) =
      M.faceOf (supportDartEquiv M i d) := rfl

/-- The old edge embedding is surjective because every edge endpoint is in support. -/
noncomputable def supportEdgeEquiv : (supportGraph M i).edgeSet ≃ M.graph.edgeSet :=
  Equiv.ofBijective (supportEmbedding M i).mapEdgeSet ⟨(supportEmbedding M i).mapEdgeSet.injective, by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      change M.graph.Adj u v at he
      refine ⟨⟨s(i ⟨u, he.mem_support_left⟩, i ⟨v, he.mem_support_right⟩), ?_⟩, ?_⟩
      · change M.graph.Adj _ _
        simpa [supportLabel] using he
      · apply Subtype.ext
        simp [Embedding.mapEdgeSet, Hom.mapEdgeSet, supportEmbedding, supportLabel]⟩

@[simp] theorem supportEdgeEquiv_edgeOfDart (d : (supportGraph M i).Dart) :
    supportEdgeEquiv M i (RotationSystem.edgeOfDart d) =
      RotationSystem.edgeOfDart (supportDartEquiv M i d) := rfl

/-- Extending coefficients along the edge equivalence preserves vertex incidence. -/
theorem support_incidence (φ : (supportGraph M i).edgeSet → ZMod 2) (x : Fin s) :
    edgeIncidence M.graph (fun e => φ ((supportEdgeEquiv M i).symm e)) (supportLabel M i x) =
      edgeIncidence (supportGraph M i) φ x := by
  classical
  unfold edgeIncidence
  rw [← (supportEdgeEquiv M i).sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  dsimp only
  rw [Equiv.symm_apply_apply]
  have hm : supportLabel M i x ∈ (supportEdgeEquiv M i e).val ↔ x ∈ e.val := by
    change supportLabel M i x ∈ Sym2.map (supportLabel M i) e.val ↔ _
    rw [Sym2.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have h := (supportEmbedding M i).injective hxy
      simpa [h] using hy
    · exact fun hx => ⟨x, hx, rfl⟩
  simp only [hm]

/-- Incidence is zero on isolated labels, independently of edge coefficients. -/
theorem incidence_zero_outside_support (φ : M.graph.edgeSet → ZMod 2) (x : Fin n)
    (hx : x ∉ M.graph.support) : edgeIncidence M.graph φ x = 0 := by
  classical
  unfold edgeIncidence
  apply Finset.sum_eq_zero
  intro e _
  have hn : x ∉ e.val := by
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      change M.graph.Adj u v at he
      simp only [Sym2.mem_iff]
      rintro (rfl | rfl)
      · exact hx he.mem_support_left
      · exact hx he.mem_support_right
  simp [hn]

/-- Removing isolated labels preserves the spherical filling condition. -/
theorem support_fills : (supportRotation M i).Fills := by
  classical
  intro φ hφ
  let ψ : M.graph.edgeSet → ZMod 2 := fun e => φ ((supportEdgeEquiv M i).symm e)
  have hψ : ∀ x, edgeIncidence M.graph ψ x = 0 := by
    intro x
    by_cases hx : x ∈ M.graph.support
    · have h := support_incidence M i φ (i ⟨x, hx⟩)
      simpa [supportLabel, ψ] using h.trans (hφ (i ⟨x, hx⟩))
    · exact incidence_zero_outside_support M ψ x hx
  obtain ⟨c, hc⟩ := M.fills ψ hψ
  refine ⟨fun f => c (supportFaceMap M i f), fun d => ?_⟩
  have h := hc (supportDartEquiv M i d)
  dsimp only [ψ] at h
  rw [← supportEdgeEquiv_edgeOfDart, Equiv.symm_apply_apply] at h
  simpa only [supportFaceMap_faceOf, supportDartEquiv_symm] using h

/-- The spherical map carried exactly by the nonisolated vertices. -/
def supportTransport : SphericalMap s where
  graph := supportGraph M i
  rotation := supportRotation M i
  fills := support_fills M i

/-- A support colouring extends over all isolated labels with a fixed colour. -/
noncomputable def extendSupportColoring {α : Type*} (a : α)
    (c : (supportGraph M i).Coloring α) : M.graph.Coloring α := by
  classical
  refine Coloring.mk (fun x => if hx : x ∈ M.graph.support then c (i ⟨x, hx⟩) else a) ?_
  intro x y hxy
  simp only [dite_eq_left hxy.mem_support_left, dite_eq_left hxy.mem_support_right]
  apply c.valid
  simpa [supportGraph, supportLabel] using hxy

/-- Every original neighbour survives in the support carrier. -/
def supportNeighborEquiv (x : Fin s) :
    (supportGraph M i).neighborSet x ≃ M.graph.neighborSet (supportLabel M i x) where
  toFun y := ⟨supportLabel M i y.val, y.property⟩
  invFun y := ⟨i ⟨y.val, y.property.mem_support_right⟩, by
    simpa [supportGraph, supportLabel] using y.property⟩
  left_inv y := by apply Subtype.ext; simp [supportLabel]
  right_inv y := by apply Subtype.ext; simp [supportLabel]

/-- Support relabelling preserves all surviving vertex degrees. -/
theorem support_degree (x : Fin s) :
    (supportGraph M i).degree x = M.graph.degree (supportLabel M i x) := by
  classical
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr (supportNeighborEquiv M i x)

/-- The support carrier has no isolated vertices, including when it is empty. -/
theorem support_degree_pos (x : Fin s) : 0 < (supportGraph M i).degree x := by
  classical
  rw [support_degree, M.graph.degree_pos_iff_mem_support]
  exact (i.symm x).property

theorem support_min_degree (k : ℕ) (hk : ∀ x ∈ M.graph.support, k ≤ M.graph.degree x)
    (x : Fin s) : k ≤ (supportTransport M i).graph.degree x := by
  change k ≤ (supportGraph M i).degree x
  rw [support_degree]
  exact hk _ (i.symm x).property

theorem supportTransport_support : (supportTransport M i).graph.support = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact ((supportTransport M i).graph.degree_pos_iff_mem_support x).mp
    (support_degree_pos M i x)

/-- Choose finite support labels. This carrier construction is classical, not executable. -/
noncomputable def supportEquivFin : M.graph.support ≃ Fin (Nat.card M.graph.support) := by
  classical
  exact Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)

noncomputable def onSupport : SphericalMap (Nat.card M.graph.support) :=
  supportTransport M (supportEquivFin M)

/-- The precise support-carrier existence statement needed before triangulation completion. -/
theorem exists_supportTransport :
    ∃ (N : SphericalMap (Nat.card M.graph.support))
      (i : M.graph.support ≃ Fin (Nat.card M.graph.support)),
      (∀ u v : M.graph.support, N.graph.Adj (i u) (i v) ↔ M.graph.Adj u.val v.val) ∧
      N.graph.support = Set.univ ∧
      (∀ x, N.graph.degree (i x) = M.graph.degree x.val) := by
  classical
  refine ⟨onSupport M, supportEquivFin M, ?_, supportTransport_support M _, ?_⟩
  · intro u v
    change M.graph.Adj ((supportEquivFin M).symm ((supportEquivFin M) u)).val
      ((supportEquivFin M).symm ((supportEquivFin M) v)).val ↔ _
    simp only [Equiv.symm_apply_apply]
  · intro x
    change (supportGraph M (supportEquivFin M)).degree _ = _
    rw [support_degree]
    change M.graph.degree ((supportEquivFin M).symm ((supportEquivFin M) x)).val = _
    rw [Equiv.symm_apply_apply]

/-- Isolating a nonisolated vertex strictly decreases the recursive support measure. -/
theorem isolate_support_card_lt (x : Fin n) (hx : x ∈ M.graph.support) :
    Nat.card (M.isolateGraph x).support < Nat.card M.graph.support := by
  classical
  have hsub : (M.isolateGraph x).support ⊆ M.graph.support := by
    rintro u ⟨v, huv⟩
    exact huv.1.mem_support_left
  have hnot : x ∉ (M.isolateGraph x).support := by
    rintro ⟨v, hxv⟩
    exact hxv.2.1 rfl
  have hstrict : (M.isolateGraph x).support ⊂ M.graph.support := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    exact hnot (heq.symm ▸ hx)
  exact Set.ncard_lt_ncard hstrict

end SimpleGraph.SphericalMap
