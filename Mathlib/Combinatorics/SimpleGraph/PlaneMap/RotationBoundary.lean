/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalMap

/-!
# Raw rotation face boundaries are even

At a vertex the outgoing and incoming face darts pair under `faceNext`.
The incident sum of a face boundary is therefore even, so adding one
face to an even combination stays even.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators

namespace RotationSystem

open Classical

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- Mod-two face boundary for a raw rotation system, without filling assumptions. -/
noncomputable def faceBoundary (R : RotationSystem G) (f : R.Face)
    (e : G.edgeSet) : ZMod 2 :=
  (Fintype.card {d : G.Dart // R.faceOf d = f ∧ edgeOfDart d = e} : ZMod 2)

lemma faceBoundary_eq (R : RotationSystem G) (f : R.Face) (e : G.edgeSet) :
    faceBoundary R f e =
      (Fintype.card {d : G.Dart // R.faceOf d = f ∧ edgeOfDart d = e} : ZMod 2) := rfl

def FaceEven (φ : G.edgeSet → ZMod 2) : Prop := ∀ v, edgeIncidence G φ v = 0

/-- Pair outgoing face darts at `v` with the incoming ones, via `faceNext`. -/
def faceVertexDartEquiv (M : RotationSystem G) (f : M.Face) (v : Fin n) :
    {d : G.Dart // M.faceOf d = f ∧ d.fst = v} ≃
      {d : G.Dart // M.faceOf d = f ∧ d.snd = v} where
  toFun d := ⟨M.faceNext.symm d.val, by
    constructor
    · have h := M.face_of_face_next (M.faceNext.symm d.val)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm.trans d.property.1
    · have h := M.face_next_fst (M.faceNext.symm d.val)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm.trans d.property.2⟩
  invFun d := ⟨M.faceNext d.val, by
    constructor
    · exact (M.face_of_face_next d.val).trans d.property.1
    · exact (M.face_next_fst d.val).trans d.property.2⟩
  left_inv d := Subtype.ext (M.faceNext.apply_symm_apply d.val)
  right_inv d := Subtype.ext (M.faceNext.symm_apply_apply d.val)

omit [DecidableRel G.Adj] in
theorem mem_edge_of_dart_iff (d : G.Dart) (v : Fin n) :
    v ∈ (RotationSystem.edgeOfDart d).val ↔ d.fst = v ∨ d.snd = v := by
  change v ∈ d.edge ↔ d.fst = v ∨ d.snd = v
  simp [Dart.edge, Sym2.mem_iff, eq_comm]

/-- The darts of a face through `v` split into an equal outgoing and incoming set. -/
theorem face_vertex_card_even (M : RotationSystem G) (f : M.Face) (v : Fin n) :
    (Fintype.card {d : G.Dart // M.faceOf d = f ∧
      v ∈ (RotationSystem.edgeOfDart d).val} : ZMod 2) = 0 := by
  let O := {d : G.Dart // M.faceOf d = f ∧ d.fst = v}
  let I := {d : G.Dart // M.faceOf d = f ∧ d.snd = v}
  let S := {d : G.Dart // M.faceOf d = f ∧
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
def faceIncidentSigmaEquiv (M : RotationSystem G) (f : M.Face) (v : Fin n) :
    (Σ e : G.edgeSet,
      {d : G.Dart // M.faceOf d = f ∧
        RotationSystem.edgeOfDart d = e ∧ v ∈ e.val}) ≃
      {d : G.Dart // M.faceOf d = f ∧
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

theorem incident_sum_boundary (M : RotationSystem G) (f : M.Face) (v : Fin n) :
    edgeIncidence G (faceBoundary M f) v = 0 := by
  unfold edgeIncidence
  let S := {d : G.Dart // M.faceOf d = f ∧
    v ∈ (RotationSystem.edgeOfDart d).val}
  have hfib :
      (∑ e : G.edgeSet,
        (Fintype.card {d : G.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val} : ZMod 2)) =
      (Fintype.card S : ZMod 2) := by
    have hsumF : (∑ e : G.edgeSet,
        Fintype.card {d : G.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val}) =
      Fintype.card (Σ e : G.edgeSet,
        {d : G.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val}) :=
      (Fintype.card_sigma
        (α := fun e : G.edgeSet =>
          {d : G.Dart // M.faceOf d = f ∧
            RotationSystem.edgeOfDart d = e ∧ v ∈ e.val})).symm
    have hF : Fintype.card (Σ e : G.edgeSet,
        {d : G.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val}) = Fintype.card S :=
      Fintype.card_congr (faceIncidentSigmaEquiv M f v)
    rw [← Nat.cast_sum]
    exact congrArg Nat.cast (hsumF.trans hF)
  have hterm : ∀ e : G.edgeSet,
      (if v ∈ e.val then faceBoundary M f e else 0) =
        (Fintype.card {d : G.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val} : ZMod 2) := by
    intro e
    by_cases hv : v ∈ e.val
    · rw [ite_eq_left hv, faceBoundary_eq]
      refine congrArg Nat.cast (Fintype.card_congr ?_)
      exact {
        toFun := fun d => ⟨d.val, And.intro d.property.1
          (And.intro d.property.2 hv)⟩
        invFun := fun d => ⟨d.val, And.intro d.property.1 d.property.2.1⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
    · rw [ite_eq_right hv]
      have : IsEmpty {d : G.Dart // M.faceOf d = f ∧
          RotationSystem.edgeOfDart d = e ∧ v ∈ e.val} :=
        ⟨fun d => hv (d.property.2.1 ▸ d.property.2.2)⟩
      simp [Fintype.card_eq_zero]
  have hrewrite : (∑ e, if v ∈ e.val then faceBoundary M f e else 0) =
      (Fintype.card S : ZMod 2) :=
    (Finset.sum_congr rfl (fun e _ => hterm e)).trans hfib
  convert hrewrite.trans (face_vertex_card_even M f v) using 1
  congr 1
  ext
  simp

/-- Every face boundary is an even edge combination. -/
theorem face_boundary_even (M : RotationSystem G) (f : M.Face) :
    FaceEven (faceBoundary M f) :=
  incident_sum_boundary M f

theorem even_add_face (M : RotationSystem G) (φ : G.edgeSet → ZMod 2)
    (hφ : FaceEven φ) (f : M.Face) :
    FaceEven (fun e => φ e + faceBoundary M f e) := by
  intro v
  unfold edgeIncidence
  have hsplit :
      (∑ e, if v ∈ e.val then φ e + faceBoundary M f e else 0) =
        (∑ e, if v ∈ e.val then φ e else 0) +
          (∑ e, if v ∈ e.val then faceBoundary M f e else 0) := by
    refine (Finset.sum_congr rfl (fun e _ => ?_)).trans (Finset.sum_add_distrib)
    by_cases hv : v ∈ e.val
    · simp [hv]
    · simp [hv]
  change edgeIncidence G (fun e => φ e + faceBoundary M f e) v = 0
  unfold edgeIncidence
  have hφv : (∑ e, if v ∈ e.val then φ e else 0) = 0 := by
    convert hφ v using 1; congr 1; ext; simp
  have hfv : (∑ e, if v ∈ e.val then faceBoundary M f e else 0) = 0 := by
    convert incident_sum_boundary M f v using 1; congr 1; ext; simp
  have hz : ((∑ e, if v ∈ e.val then φ e else 0) +
      (∑ e, if v ∈ e.val then faceBoundary M f e else 0)) = 0 := by
    rw [hφv, hfv, add_zero]
  convert hsplit.trans hz using 1; congr 1; ext; simp

/-- Linear combination of raw face boundaries. -/
noncomputable def faceSum (R : RotationSystem G) (c : R.Face → ZMod 2)
    (e : G.edgeSet) : ZMod 2 := ∑ f, c f * faceBoundary R f e

theorem faceSum_eq_dart_sum (M : RotationSystem G) (c : M.Face → ZMod 2)
    (e : G.edgeSet) :
    faceSum M c e =
      ∑ d : {d : G.Dart // RotationSystem.edgeOfDart d = e},
        c (M.faceOf d.val) := by
  classical
  let S (f : M.Face) :=
    {d : G.Dart // M.faceOf d = f ∧ RotationSystem.edgeOfDart d = e}
  let T := {d : G.Dart // RotationSystem.edgeOfDart d = e}
  let hσ : (Σ f : M.Face, S f) ≃ T :=
    { toFun := fun p => ⟨p.2.val, p.2.property.2⟩
      invFun := fun d => ⟨M.faceOf d.val, ⟨d.val, And.intro rfl d.property⟩⟩
      left_inv := fun p => by
        rcases p with ⟨f, d, hf, he⟩
        subst hf
        rfl
      right_inv := fun _ => Subtype.ext rfl }
  have hsum : (∑ f, c f * faceBoundary M f e) =
      ∑ f, ∑ _d : S f, c f := by
    apply Finset.sum_congr rfl
    intro f _
    have : ∑ _d : S f, c f = (Fintype.card (S f) : ZMod 2) * c f := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [faceBoundary_eq, this, mul_comm]
  have hconst : (∑ f, ∑ d : S f, c f) =
      ∑ f, ∑ d : S f, c (M.faceOf d.val) := by
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro d _
    exact congrArg c d.property.1.symm
  have hsigma :
      (∑ f, ∑ d : S f, c (M.faceOf d.val)) =
        ∑ p : Σ f : M.Face, S f, c (M.faceOf p.2.val) :=
    (Fintype.sum_sigma (ι := M.Face) (α := S)
      (fun p => c (M.faceOf p.2.val))).symm
  change (∑ f, c f * faceBoundary M f e) = _
  exact (hsum.trans hconst).trans
    (hsigma.trans (Fintype.sum_equiv hσ
      (fun p => c (M.faceOf p.2.val))
      (fun d => c (M.faceOf d.val))
      (fun p => by dsimp [hσ])))


/-- A face potential has the two incident face values on each edge. -/
theorem faceSum_edgeOfDart (R : RotationSystem G) (c : R.Face → ZMod 2) (d : G.Dart) :
    faceSum R c (edgeOfDart d) = c (R.faceOf d) + c (R.faceOf d.symm) := by
  classical
  rw [faceSum_eq_dart_sum]
  let e := edgeOfDart d
  let E := edgeFiberBoolEquiv e d rfl
  have hfun : ∀ w : {w : G.Dart // edgeOfDart w = e},
      c (R.faceOf w.val) = if E w = true then c (R.faceOf d) else c (R.faceOf d.symm) := by
    intro w
    obtain h | h := (edge_of_dart_eq_iff w.val d).mp w.property
    · simp [E, edgeFiberBoolEquiv, h]
    · simp [E, edgeFiberBoolEquiv, h, Ne.symm (dart_ne_symm d)]
  rw [Fintype.sum_equiv E (fun w => c (R.faceOf w.val))
    (fun b => if b = true then c (R.faceOf d) else c (R.faceOf d.symm)) hfun]
  simp


/-- A single raw face boundary records the two dart incidences mod two. -/
theorem faceBoundary_edgeOfDart (R : RotationSystem G) (f : R.Face) (d : G.Dart) :
    faceBoundary R f (edgeOfDart d) =
      (if R.faceOf d = f then 1 else 0) +
        (if R.faceOf d.symm = f then 1 else 0) := by
  classical
  have h := faceSum_edgeOfDart R (fun F => if F = f then 1 else 0) d
  simpa [faceSum] using h

/-- Any linear combination of raw face boundaries is even. -/
theorem faceSum_even (R : RotationSystem G) (c : R.Face → ZMod 2) :
    FaceEven (faceSum R c) := by
  classical
  intro v
  unfold edgeIncidence faceSum
  have hterm : ∀ e : G.edgeSet,
      (if v ∈ e.val then ∑ f, c f * faceBoundary R f e else 0) =
        ∑ f, c f * (if v ∈ e.val then faceBoundary R f e else 0) := by
    intro e
    by_cases hv : v ∈ e.val <;> simp [hv]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro f _
  rw [← Finset.mul_sum]
  have hf : (∑ e : G.edgeSet, if v ∈ e.val then faceBoundary R f e else 0) = 0 := by
    convert incident_sum_boundary R f v using 1
    congr 1
    ext
    simp
  rw [← mul_zero (c f)]
  congr 1
  convert hf
  simp


end RotationSystem

end SimpleGraph
