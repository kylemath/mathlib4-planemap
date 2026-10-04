/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Jordan

/-!
# Face boundaries are even

At a vertex the outgoing and incoming face darts pair under `faceNext`.
The incident sum of a face boundary is therefore even, so adding one
face to an even combination stays even.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators

namespace PlaneMap

open Classical

variable {n : ℕ}

/-- Pair outgoing face darts at `v` with the incoming ones, via `faceNext`. -/
def faceVertexDartEquiv (M : PlaneMap n) (f : M.Face) (v : Fin n) :
    {d : M.Dart // M.faceOf d = f ∧ d.fst = v} ≃
      {d : M.Dart // M.faceOf d = f ∧ d.snd = v} where
  toFun d := ⟨M.rotation.faceNext.symm d.val, by
    constructor
    · have h := M.rotation.face_of_face_next (M.rotation.faceNext.symm d.val)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm.trans d.property.1
    · have h := M.rotation.face_next_fst (M.rotation.faceNext.symm d.val)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm.trans d.property.2⟩
  invFun d := ⟨M.rotation.faceNext d.val, by
    constructor
    · exact (M.rotation.face_of_face_next d.val).trans d.property.1
    · exact (M.rotation.face_next_fst d.val).trans d.property.2⟩
  left_inv d := Subtype.ext (M.rotation.faceNext.apply_symm_apply d.val)
  right_inv d := Subtype.ext (M.rotation.faceNext.symm_apply_apply d.val)

theorem mem_edge_of_dart_iff {G : SimpleGraph (Fin n)} (d : G.Dart) (v : Fin n) :
    v ∈ (RotationSystem.edgeOfDart d).val ↔ d.fst = v ∨ d.snd = v := by
  change v ∈ d.edge ↔ d.fst = v ∨ d.snd = v
  simp [Dart.edge, Sym2.mem_iff, eq_comm]

/-- The darts of a face through `v` split into an equal outgoing and incoming set. -/
theorem face_vertex_card_even (M : PlaneMap n) (f : M.Face) (v : Fin n) :
    (Fintype.card {d : M.Dart // M.faceOf d = f ∧
      v ∈ (RotationSystem.edgeOfDart d).val} : ZMod 2) = 0 := by
  let O := {d : M.Dart // M.faceOf d = f ∧ d.fst = v}
  let I := {d : M.Dart // M.faceOf d = f ∧ d.snd = v}
  let S := {d : M.Dart // M.faceOf d = f ∧
    v ∈ (RotationSystem.edgeOfDart d).val}
  have hpair : ∀ d : S, d.val.fst = v ∨ d.val.snd = v :=
    fun d => (mem_edge_of_dart_iff d.val v).1 d.property.2
  let e : S ≃ O ⊕ I :=
    { toFun := fun d =>
        if h : d.val.fst = v then Sum.inl ⟨d.val, And.intro d.property.1 h⟩
        else Sum.inr ⟨d.val, And.intro d.property.1 ((hpair d).resolve_left h)⟩
      invFun := fun x => match x with
        | .inl d => ⟨d.val, And.intro d.property.1
            ((mem_edge_of_dart_iff d.val v).2 (Or.inl d.property.2))⟩
        | .inr d => ⟨d.val, And.intro d.property.1
            ((mem_edge_of_dart_iff d.val v).2 (Or.inr d.property.2))⟩
      left_inv := fun d => by
        by_cases h : d.val.fst = v
        · simp [h]
        · simp [h]
      right_inv := fun x => by
        cases x with
        | inl d => simp [d.property.2]
        | inr d =>
          have hne : d.val.fst ≠ v := fun hf =>
            d.val.fst_ne_snd (hf.trans d.property.2.symm)
          simp [hne] }
  have hcard : Fintype.card S = Fintype.card O + Fintype.card I :=
    (Fintype.card_congr e).trans (Fintype.card_sum (α := O) (β := I))
  have hOI : Fintype.card O = Fintype.card I :=
    Fintype.card_congr (faceVertexDartEquiv M f v)
  have h2 : Fintype.card S = 2 * Fintype.card O := by omega
  rw [h2, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- Bundle the face-edge-vertex fibre as a dependent sum over edges. -/
def faceIncidentSigmaEquiv (M : PlaneMap n) (f : M.Face) (v : Fin n) :
    (Σ e : M.graph.edgeSet,
      {d : M.Dart // M.faceOf d = f ∧
        RotationSystem.edgeOfDart d = e ∧ v ∈ e.val}) ≃
      {d : M.Dart // M.faceOf d = f ∧
        v ∈ (RotationSystem.edgeOfDart d).val} where
  toFun p := ⟨p.2.val, And.intro p.2.property.1 (by
    have h := p.2.property.2.1
    change v ∈ (RotationSystem.edgeOfDart p.2.val).val
    rw [h]
    exact p.2.property.2.2)⟩
  invFun d := ⟨RotationSystem.edgeOfDart d.val,
    ⟨d.val, And.intro d.property.1 (And.intro rfl d.property.2)⟩⟩
  left_inv p := by
    rcases p with ⟨e, d, hf, he, hv⟩
    subst he
    rfl
  right_inv d := Subtype.ext rfl

theorem incident_sum_boundary (M : PlaneMap n) (f : M.Face) (v : Fin n) :
    incidentSum M (M.boundary f) v = 0 := by
  unfold incidentSum
  let S := {d : M.Dart // M.faceOf d = f ∧
    v ∈ (RotationSystem.edgeOfDart d).val}
  have hfib :
      (∑ e : M.graph.edgeSet,
        (Fintype.card {d : M.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val} : ZMod 2)) =
      (Fintype.card S : ZMod 2) := by
    have hsumF : (∑ e : M.graph.edgeSet,
        Fintype.card {d : M.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val}) =
      Fintype.card (Σ e : M.graph.edgeSet,
        {d : M.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val}) :=
      (Fintype.card_sigma
        (α := fun e : M.graph.edgeSet =>
          {d : M.Dart // M.faceOf d = f ∧
            RotationSystem.edgeOfDart d = e ∧ v ∈ e.val})).symm
    have hF : Fintype.card (Σ e : M.graph.edgeSet,
        {d : M.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val}) = Fintype.card S :=
      Fintype.card_congr (faceIncidentSigmaEquiv M f v)
    rw [← Nat.cast_sum]
    exact congrArg Nat.cast (hsumF.trans hF)
  have hterm : ∀ e : M.graph.edgeSet,
      (if v ∈ e.val then M.boundary f e else 0) =
        (Fintype.card {d : M.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val} : ZMod 2) := by
    intro e
    by_cases hv : v ∈ e.val
    · rw [ite_eq_left hv, boundary_eq]
      refine congrArg Nat.cast (Fintype.card_congr ?_)
      exact {
        toFun := fun d => ⟨d.val, And.intro d.property.1
          (And.intro d.property.2 hv)⟩
        invFun := fun d => ⟨d.val, And.intro d.property.1 d.property.2.1⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
    · rw [ite_eq_right hv]
      have : IsEmpty {d : M.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val} :=
        ⟨fun d => hv (d.property.2.1 ▸ d.property.2.2)⟩
      simp [Fintype.card_eq_zero]
  have hrewrite : (∑ e, if v ∈ e.val then M.boundary f e else 0) =
      (Fintype.card S : ZMod 2) :=
    (Finset.sum_congr rfl (fun e _ => hterm e)).trans hfib
  exact hrewrite.trans (face_vertex_card_even M f v)

/-- Every face boundary is an even edge combination. -/
theorem face_boundary_even (M : PlaneMap n) (f : M.Face) :
    IsEven M (M.boundary f) :=
  incident_sum_boundary M f

theorem even_add_face (M : PlaneMap n) (φ : M.graph.edgeSet → ZMod 2)
    (hφ : IsEven M φ) (f : M.Face) :
    IsEven M (fun e => φ e + M.boundary f e) := by
  intro v
  unfold incidentSum
  have hsplit :
      (∑ e, if v ∈ e.val then φ e + M.boundary f e else 0) =
        (∑ e, if v ∈ e.val then φ e else 0) +
          (∑ e, if v ∈ e.val then M.boundary f e else 0) := by
    refine (Finset.sum_congr rfl (fun e _ => ?_)).trans (Finset.sum_add_distrib)
    by_cases hv : v ∈ e.val
    · simp [hv]
    · simp [hv]
  change incidentSum M (fun e => φ e + M.boundary f e) v = 0
  unfold incidentSum
  rw [hsplit]
  have hφv : (∑ e, if v ∈ e.val then φ e else 0) = 0 := hφ v
  have hfv : (∑ e, if v ∈ e.val then M.boundary f e else 0) = 0 :=
    incident_sum_boundary M f v
  rw [hφv, hfv, add_zero]

end PlaneMap

end SimpleGraph
