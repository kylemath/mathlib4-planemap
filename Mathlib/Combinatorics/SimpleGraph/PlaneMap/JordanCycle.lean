/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Jordan
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.JordanSides
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.JordanEven

/-!
# Cycle edge combinations

This file associates a mod-two edge combination to a `CycleCut`.  The
combination is even using only the local inverse axioms of the cut; in
particular, it does not depend on the constructor induction in `JordanEven`.

The current `CycleCut` structure may describe several disjoint cycles.
Consequently a face-sum representation alone does not imply the global
reachability statement `cycle_two_sides`: sectors belonging to different
components need not use a common choice of left and right.  The local
face-coefficient and degree-five sector lemmas below record the parts that
remain valid without a connected-cycle hypothesis.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators

namespace PlaneMap

open Classical

variable {n : ℕ}

/-- The mod-two characteristic function of the unoriented cycle edges. -/
noncomputable def cycleEdgeCoeff (M : PlaneMap n) (C : CycleCut M) :
    M.graph.edgeSet → ZMod 2 :=
  fun e =>
    if ∃ v : C.verts,
        RotationSystem.edgeOfDart (C.left v) = e ∨
          RotationSystem.edgeOfDart (C.right v) = e then 1 else 0

theorem cycleEdgeCoeff_eq_one_iff (M : PlaneMap n) (C : CycleCut M)
    (e : M.graph.edgeSet) :
    cycleEdgeCoeff M C e = 1 ↔
      ∃ v : C.verts,
        RotationSystem.edgeOfDart (C.left v) = e ∨
          RotationSystem.edgeOfDart (C.right v) = e := by
  unfold cycleEdgeCoeff
  by_cases h : ∃ v : C.verts,
      RotationSystem.edgeOfDart (C.left v) = e ∨
        RotationSystem.edgeOfDart (C.right v) = e
  · simp [h]
  · simp [h]

theorem cycleEdgeCoeff_eq_zero_iff (M : PlaneMap n) (C : CycleCut M)
    (e : M.graph.edgeSet) :
    cycleEdgeCoeff M C e = 0 ↔
      ¬ ∃ v : C.verts,
        RotationSystem.edgeOfDart (C.left v) = e ∨
          RotationSystem.edgeOfDart (C.right v) = e := by
  unfold cycleEdgeCoeff
  by_cases h : ∃ v : C.verts,
      RotationSystem.edgeOfDart (C.left v) = e ∨
        RotationSystem.edgeOfDart (C.right v) = e
  · simp [h]
  · simp [h]

theorem mem_edgeOfDart_iff {G : SimpleGraph (Fin n)} (d : G.Dart)
    (x : Fin n) :
    x ∈ (RotationSystem.edgeOfDart d).val ↔
      d.fst = x ∨ d.snd = x := by
  change x ∈ d.edge ↔ d.fst = x ∨ d.snd = x
  simp [Dart.edge, Sym2.mem_iff, eq_comm]

/-- Every endpoint of an edge selected by `cycleEdgeCoeff` is a cut vertex. -/
theorem cycleEdgeCoeff_closed (M : PlaneMap n) (C : CycleCut M)
    (e : M.graph.edgeSet) (he : cycleEdgeCoeff M C e = 1)
    (x : Fin n) (hx : x ∈ e.val) : x ∈ C.verts := by
  obtain ⟨v, hv | hv⟩ := (cycleEdgeCoeff_eq_one_iff M C e).1 he
  · rw [← hv] at hx
    rcases (mem_edgeOfDart_iff (C.left v) x).1 hx with h | h
    · have hxv : x = v.val := h.symm.trans (C.left_fst v)
      simpa [hxv] using v.property
    · simpa [h] using C.left_snd_mem v
  · rw [← hv] at hx
    rcases (mem_edgeOfDart_iff (C.right v) x).1 hx with h | h
    · have hxv : x = v.val := h.symm.trans (C.right_fst v)
      simpa [hxv] using v.property
    · simpa [h] using C.right_snd_mem v

theorem cycle_left_edge_ne_right_edge (M : PlaneMap n) (C : CycleCut M)
    (v : C.verts) :
    RotationSystem.edgeOfDart (C.left v) ≠
      RotationSystem.edgeOfDart (C.right v) := by
  intro h
  rcases (RotationSystem.edge_of_dart_eq_iff (C.left v) (C.right v)).1 h
      with hsame | hsymm
  · exact C.left_ne_right v hsame
  · have hfst := congrArg (fun d : M.Dart => d.fst) hsymm
    have hsnd := congrArg (fun d : M.Dart => d.snd) hsymm
    have hv : (C.left v).fst = (C.right v).fst := by
      rw [C.left_fst v, C.right_fst v]
    exact (C.left v).fst_ne_snd (hv.trans hsnd.symm)

/-- At a cut vertex, the selected incident edges are exactly its two
outgoing cycle edges. -/
theorem cycleEdgeCoeff_incident_iff (M : PlaneMap n) (C : CycleCut M)
    (v : C.verts) (e : M.graph.edgeSet) (hv : v.val ∈ e.val) :
    cycleEdgeCoeff M C e = 1 ↔
      e = RotationSystem.edgeOfDart (C.left v) ∨
        e = RotationSystem.edgeOfDart (C.right v) := by
  constructor
  · intro he
    obtain ⟨w, hw | hw⟩ := (cycleEdgeCoeff_eq_one_iff M C e).1 he
    · have hmem : v.val ∈
          (RotationSystem.edgeOfDart (C.left w)).val := by
        rwa [hw]
      rcases (mem_edgeOfDart_iff (C.left w) v.val).1 hmem with h | h
      · left
        have hwv : w = v :=
          Subtype.ext ((C.left_fst w).symm.trans h)
        subst w
        exact hw.symm
      · right
        let z : C.verts := ⟨(C.left w).snd, C.left_snd_mem w⟩
        have hzv : z = v := Subtype.ext h
        have hinv : C.right z = (C.left w).symm :=
          C.left_right_inv w
        rw [hzv] at hinv
        rw [← hw, hinv, RotationSystem.edge_of_dart_symm]
    · have hmem : v.val ∈
          (RotationSystem.edgeOfDart (C.right w)).val := by
        rwa [hw]
      rcases (mem_edgeOfDart_iff (C.right w) v.val).1 hmem with h | h
      · right
        have hwv : w = v :=
          Subtype.ext ((C.right_fst w).symm.trans h)
        subst w
        exact hw.symm
      · left
        let z : C.verts := ⟨(C.right w).snd, C.right_snd_mem w⟩
        have hzv : z = v := Subtype.ext h
        have hinv : C.left z = (C.right w).symm :=
          C.right_left_inv w
        rw [hzv] at hinv
        rw [← hw, hinv, RotationSystem.edge_of_dart_symm]
  · intro h
    apply (cycleEdgeCoeff_eq_one_iff M C e).2
    refine ⟨v, ?_⟩
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem cycleEdgeCoeff_incident_value (M : PlaneMap n) (C : CycleCut M)
    (v : C.verts) (e : M.graph.edgeSet) :
    (if v.val ∈ e.val then cycleEdgeCoeff M C e else 0) =
      if e = RotationSystem.edgeOfDart (C.left v) ∨
          e = RotationSystem.edgeOfDart (C.right v) then 1 else 0 := by
  by_cases hv : v.val ∈ e.val
  · rw [ite_eq_left hv]
    by_cases he : e = RotationSystem.edgeOfDart (C.left v) ∨
        e = RotationSystem.edgeOfDart (C.right v)
    · rw [ite_eq_left he, (cycleEdgeCoeff_incident_iff M C v e hv).2 he]
    · rw [ite_eq_right he]
      apply (cycleEdgeCoeff_eq_zero_iff M C e).2
      intro h
      exact he ((cycleEdgeCoeff_incident_iff M C v e hv).1
        ((cycleEdgeCoeff_eq_one_iff M C e).2 h))
  · rw [ite_eq_right hv]
    have hne : ¬ (e = RotationSystem.edgeOfDart (C.left v) ∨
        e = RotationSystem.edgeOfDart (C.right v)) := by
      intro h
      rcases h with h | h
      · apply hv
        rw [h, mem_edgeOfDart_iff]
        exact Or.inl (C.left_fst v)
      · apply hv
        rw [h, mem_edgeOfDart_iff]
        exact Or.inl (C.right_fst v)
    rw [ite_eq_right hne]

/-- The edge combination carried by a cycle cut has even incidence at every
vertex. -/
theorem cycleEdgeCoeff_even (M : PlaneMap n) (C : CycleCut M) :
    IsEven M (cycleEdgeCoeff M C) := by
  intro x
  by_cases hx : x ∈ C.verts
  · let v : C.verts := ⟨x, hx⟩
    unfold incidentSum
    rw [show x = v.val from rfl]
    calc
      (∑ e : M.graph.edgeSet,
          if v.val ∈ e.val then cycleEdgeCoeff M C e else 0) =
          ∑ e : M.graph.edgeSet,
            if e = RotationSystem.edgeOfDart (C.left v) ∨
                e = RotationSystem.edgeOfDart (C.right v) then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro e _
              exact cycleEdgeCoeff_incident_value M C v e
      _ = 1 + 1 := by
        rw [Finset.sum_ite]
        have hfilter :
            Finset.univ.filter (fun e : M.graph.edgeSet =>
              e = RotationSystem.edgeOfDart (C.left v) ∨
                e = RotationSystem.edgeOfDart (C.right v)) =
              {RotationSystem.edgeOfDart (C.left v),
                RotationSystem.edgeOfDart (C.right v)} := by
          ext e
          simp [eq_comm]
        rw [hfilter]
        simp [Finset.card_pair (cycle_left_edge_ne_right_edge M C v),
          Finset.sum_const_zero, nsmul_eq_mul]
        norm_num
      _ = 0 := by decide
  · unfold incidentSum
    apply Finset.sum_eq_zero
    intro e _
    by_cases hxe : x ∈ e.val
    · rw [ite_eq_left hxe]
      by_cases he : cycleEdgeCoeff M C e = 1
      · exact (hx (cycleEdgeCoeff_closed M C e he x hxe)).elim
      · have h01 : cycleEdgeCoeff M C e = 0 := by
          rw [cycleEdgeCoeff_eq_zero_iff]
          intro hex
          exact he ((cycleEdgeCoeff_eq_one_iff M C e).2 hex)
        exact h01
    · rw [ite_eq_right hxe]

/-- The cycle edge combination is a mod-two sum of face boundaries. -/
theorem cycleEdgeCoeff_is_face_sum (M : PlaneMap n) (C : CycleCut M) :
    ∃ c : M.Face → ZMod 2, ∀ e,
      cycleEdgeCoeff M C e = faceSum M c e :=
  even_is_face_sum M (cycleEdgeCoeff M C) (cycleEdgeCoeff_even M C)

/-- Expand a face-boundary sum as the sum of the coefficients of the two
darts above an edge. -/
theorem cycle_faceSum_eq_dart_sum (M : PlaneMap n)
    (c : M.Face → ZMod 2) (e : M.graph.edgeSet) :
    faceSum M c e =
      ∑ d : {d : M.Dart // RotationSystem.edgeOfDart d = e},
        c (M.faceOf d.val) := by
  exact faceSum_eq_dart_sum M c e

theorem cycle_faceSum_edgeOfDart (M : PlaneMap n)
    (c : M.Face → ZMod 2) (d : M.Dart) :
    faceSum M c (RotationSystem.edgeOfDart d) =
      c (M.faceOf d) + c (M.faceOf d.symm) := by
  rw [cycle_faceSum_eq_dart_sum]
  let E := RotationSystem.edgeFiberBoolEquiv
    (RotationSystem.edgeOfDart d) d rfl
  have hsum := Fintype.sum_equiv E
    (fun x => c (M.faceOf x.val))
    (fun b => c (M.faceOf (E.symm b).val))
    (fun x => congrArg (fun y => c (M.faceOf y.val))
      (E.symm_apply_apply x).symm)
  rw [hsum]
  change (∑ b : Bool, c (M.faceOf
    ((if b = true then
      (⟨d, rfl⟩ :
        {x : M.Dart //
          RotationSystem.edgeOfDart x =
            RotationSystem.edgeOfDart d})
    else ⟨d.symm, RotationSystem.edge_of_dart_symm d⟩)).val)) =
      c (M.faceOf d) + c (M.faceOf d.symm)
  simp

/-- On a non-cycle edge, the two incident face coefficients in a face sum
agree.  This is the local propagation fact needed by any global sides proof. -/
theorem face_coeff_eq_of_cycleEdgeCoeff_zero (M : PlaneMap n)
    (C : CycleCut M) (c : M.Face → ZMod 2)
    (hc : ∀ e, cycleEdgeCoeff M C e = faceSum M c e)
    (d : M.Dart)
    (hzero : cycleEdgeCoeff M C (RotationSystem.edgeOfDart d) = 0) :
    c (M.faceOf d) = c (M.faceOf d.symm) := by
  have hsum : c (M.faceOf d) + c (M.faceOf d.symm) = 0 := by
    rw [← cycle_faceSum_edgeOfDart M c d, ← hc]
    exact hzero
  calc
    c (M.faceOf d) =
        c (M.faceOf d) +
          (c (M.faceOf d.symm) + c (M.faceOf d.symm)) := by
      have hself :
          c (M.faceOf d.symm) + c (M.faceOf d.symm) = 0 := by
        rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2,
          zero_mul]
      rw [hself, add_zero]
    _ = (c (M.faceOf d) + c (M.faceOf d.symm)) +
          c (M.faceOf d.symm) := by rw [add_assoc]
    _ = c (M.faceOf d.symm) := by rw [hsum, zero_add]

/-- The degree-five sector conclusion in the form used by the five-colour
link: the neighbour after the right boundary dart lies in the right open
sector, while the supplied middle neighbour lies in the left open sector. -/
theorem opposite_sectors_of_pentagon (M : PlaneMap n) (C : CycleCut M)
    (x : C.verts) (v0 v1 v2 v3 : Fin n)
    (d0 d1 d2 d3 : M.Dart)
    (hdeg : M.graph.degree x.val = 5)
    (hd0 : d0 = C.left x) (hd2 : d2 = C.right x)
    (h0 : d0.fst = x.val) (h1 : d1.snd = v1)
    (h2 : d2.snd = v2) (h3 : d3.snd = v3)
    (hv0 : d0.snd = v0)
    (hleft : LeftSector C x d1)
    (hnext : M.rotation.next d2 = d3)
    (hne : d3 ≠ d0) :
    LeftSector C x d1 ∧ RightSector C x d3 := by
  refine ⟨hleft, ?_⟩
  unfold RightSector
  rw [← hd2, ← hd0, ← hnext]
  apply inOpenInterval_of_next_ne
  rw [hnext]
  exact hne

end PlaneMap

end SimpleGraph
