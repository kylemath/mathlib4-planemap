/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationSplitFills

/-!
# Bridge insertion preserves filling on a raw rotation carrier

Inserting an edge between corners in two different connected components
preserves `Fills`. An even combination vanishes on the bridge, because summing
the even condition over one old component counts every old edge twice and the
bridge once. Restrict it to the old map and take the old face potential. Adding
a constant to the face coefficients of one component changes no edge sum, so
the two selected corner faces can be made to agree. Then lift through `split`.
No connectedness of the old map, face-merging description, or face-length
premise is used.
-/

@[expose] public section
namespace SimpleGraph
open scoped BigOperators
open PlaneMapConstruction
namespace RotationSystem
open Classical
variable {n : ℕ} {G : SimpleGraph (Fin n)}

private theorem zmod2_add_self'' (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- Summing the incidence of any edge combination over one connected component
gives zero: each edge has both or neither endpoint in the component. -/
theorem sum_incidence_component (ψ : G.edgeSet → ZMod 2) (u : Fin n) :
    ∑ v, (if G.Reachable u v then edgeIncidence G ψ v else 0) = 0 := by
  classical
  unfold edgeIncidence
  have hswap : (∑ v, if G.Reachable u v then
        ∑ e : G.edgeSet, (if v ∈ e.val then ψ e else 0) else 0) =
      ∑ e : G.edgeSet, ∑ v, (if G.Reachable u v ∧ v ∈ e.val then ψ e else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : G.Reachable u v
    · simp only [hv, ite_true, true_and]
    · simp only [hv, ite_false, false_and, Finset.sum_const_zero]
  rw [hswap]
  apply Finset.sum_eq_zero
  intro e _
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : G.Adj x y := he
    have hne : x ≠ y := hxy.ne
    have hiff : G.Reachable u x ↔ G.Reachable u y :=
      ⟨fun h => h.trans hxy.reachable, fun h => h.trans hxy.symm.reachable⟩
    have hpt : ∀ v : Fin n,
        (if G.Reachable u v ∧ v ∈ s(x, y) then ψ ⟨s(x, y), he⟩ else 0) =
          (if v = x then (if G.Reachable u x then ψ ⟨s(x, y), he⟩ else 0) else 0) +
            (if v = y then (if G.Reachable u y then ψ ⟨s(x, y), he⟩ else 0) else 0) := by
      intro v
      by_cases hvx : v = x
      · subst hvx
        simp [hne]
      · by_cases hvy : v = y
        · subst hvy
          simp [hvx]
        · simp [hvx, hvy, Sym2.mem_iff]
    rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    by_cases hx : G.Reachable u x
    · rw [ite_eq_left hx, ite_eq_left (hiff.1 hx), zmod2_add_self'']
    · rw [ite_eq_right hx, ite_eq_right (fun h => hx (hiff.2 h)), add_zero]

/-- An even combination on the bridged graph vanishes on the bridge. -/
theorem bridge_coeff_zero (a b : G.Dart) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) (hsep : ¬ G.Reachable a.fst b.fst)
    (φ : (splitGraph G a.fst b.fst hfst).edgeSet → ZMod 2)
    (hφ : ∀ x, edgeIncidence (splitGraph G a.fst b.fst hfst) φ x = 0) :
    φ (splitNewEdge G a b hfst hadj) = 0 := by
  classical
  have hzero : (∑ v, if G.Reachable a.fst v then
      edgeIncidence (splitGraph G a.fst b.fst hfst) φ v else 0) = 0 :=
    Finset.sum_eq_zero (fun v _ => by simp [hφ v])
  simp_rw [incident_sum_split G a b hfst hadj φ] at hzero
  have hdist : (∑ v, if G.Reachable a.fst v then
        edgeIncidence G (restrictSplit G a b hfst hadj φ) v +
          (if v = a.fst ∨ v = b.fst then φ (splitNewEdge G a b hfst hadj) else 0) else 0) =
      (∑ v, if G.Reachable a.fst v then
        edgeIncidence G (restrictSplit G a b hfst hadj φ) v else 0) +
      ∑ v, (if G.Reachable a.fst v ∧ (v = a.fst ∨ v = b.fst) then
        φ (splitNewEdge G a b hfst hadj) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : G.Reachable a.fst v <;> simp [hv]
  rw [hdist, sum_incidence_component, zero_add] at hzero
  have hpt : ∀ v : Fin n,
      (if G.Reachable a.fst v ∧ (v = a.fst ∨ v = b.fst) then
        φ (splitNewEdge G a b hfst hadj) else 0) =
      if v = a.fst then φ (splitNewEdge G a b hfst hadj) else 0 := by
    intro v
    by_cases hva : v = a.fst
    · subst hva
      simp
    · by_cases hvb : v = b.fst
      · subst hvb
        simp [hva, hsep]
      · simp [hva, hvb]
  rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_ite_eq'] at hzero
  simpa using hzero

/-- Face orbits stay inside one connected component. -/
theorem reachable_iff_of_faceRelation (R : RotationSystem G) (u : Fin n)
    {d e : G.Dart} (h : R.FaceRelation d e) :
    G.Reachable u d.fst ↔ G.Reachable u e.fst := by
  induction h with
  | refl => rfl
  | step d =>
    rw [R.face_next_fst d]
    exact ⟨fun h => h.trans d.adj.reachable, fun h => h.trans d.adj.symm.reachable⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

/-- The value `k` on faces in the component of `u`, and `0` elsewhere. -/
noncomputable def componentValue (R : RotationSystem G) (u : Fin n) (k : ZMod 2) :
    R.Face → ZMod 2
  | .inl q => Quotient.lift (fun d : G.Dart => if G.Reachable u d.fst then k else 0)
      (fun _ _ h => if_congr (reachable_iff_of_faceRelation R u h) rfl rfl) q
  | .inr _ => 0

theorem componentValue_faceOf (R : RotationSystem G) (u : Fin n) (k : ZMod 2)
    (d : G.Dart) :
    componentValue R u k (R.faceOf d) = if G.Reachable u d.fst then k else 0 := rfl

/-- **Bridge insertion preserves filling.** Inserting an edge between corners in
two different connected components of a filling rotation system yields a filling
rotation system. -/
theorem split_fills_bridge (R : RotationSystem G) (hR : R.Fills) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst) (hadj : ¬ G.Adj a.fst b.fst)
    (hsep : ¬ G.Reachable a.fst b.fst) :
    (split R a b hfst hadj).Fills := by
  intro φ hφ
  have h0 := bridge_coeff_zero a b hfst hadj hsep φ hφ
  obtain ⟨c0, hc0⟩ := hR (restrictSplit G a b hfst hadj φ)
    (even_restrict_split G a b hfst hadj φ hφ h0)
  let k : ZMod 2 := c0 (R.faceOf a) + c0 (R.faceOf b)
  let c1 : R.Face → ZMod 2 := fun F => c0 F + componentValue R b.fst k F
  have hba : ¬ G.Reachable b.fst a.fst := fun h => hsep h.symm
  have hc1a : c1 (R.faceOf a) = c0 (R.faceOf a) := by
    change c0 (R.faceOf a) + componentValue R b.fst k (R.faceOf a) = _
    rw [componentValue_faceOf, ite_eq_right hba, add_zero]
  have hc1b : c1 (R.faceOf b) = c0 (R.faceOf a) := by
    change c0 (R.faceOf b) + componentValue R b.fst k (R.faceOf b) = _
    rw [componentValue_faceOf, ite_eq_left (SimpleGraph.Reachable.refl _)]
    change c0 (R.faceOf b) + (c0 (R.faceOf a) + c0 (R.faceOf b)) = c0 (R.faceOf a)
    rw [add_comm (c0 (R.faceOf a)), ← add_assoc, zmod2_add_self'', zero_add]
  have hagree : c1 (R.faceOf a) = c1 (R.faceOf b) := hc1a.trans hc1b.symm
  have hc1 : ∀ d0 : G.Dart, restrictSplit G a b hfst hadj φ (edgeOfDart d0) =
      c1 (R.faceOf d0) + c1 (R.faceOf d0.symm) := by
    intro d0
    rw [hc0 d0]
    change c0 (R.faceOf d0) + c0 (R.faceOf d0.symm) =
      (c0 (R.faceOf d0) + componentValue R b.fst k (R.faceOf d0)) +
        (c0 (R.faceOf d0.symm) + componentValue R b.fst k (R.faceOf d0.symm))
    rw [componentValue_faceOf, componentValue_faceOf]
    have hiff : G.Reachable b.fst d0.fst ↔ G.Reachable b.fst d0.symm.fst :=
      ⟨fun h => h.trans d0.adj.reachable, fun h => h.trans d0.adj.symm.reachable⟩
    by_cases hd : G.Reachable b.fst d0.fst
    · rw [ite_eq_left hd, ite_eq_left (hiff.1 hd)]
      rw [add_add_add_comm, zmod2_add_self'', add_zero]
    · rw [ite_eq_right hd, ite_eq_right (fun h => hd (hiff.2 h)), add_zero, add_zero]
  refine ⟨splitFaceFunction R a b hfst hadj c1 hagree, ?_⟩
  intro d
  obtain ⟨x, rfl⟩ := (splitDartEquiv a.fst b.fst hfst hadj).surjective d
  cases x with
  | inl d0 =>
    change φ (edgeOfDart (splitOld a.fst b.fst hfst d0)) =
      splitFaceFunction R a b hfst hadj c1 hagree
          ((split R a b hfst hadj).faceOf (splitOld a.fst b.fst hfst d0)) +
        splitFaceFunction R a b hfst hadj c1 hagree
          ((split R a b hfst hadj).faceOf (splitOld a.fst b.fst hfst d0).symm)
    rw [split_old_symm, split_face_function_old, split_face_function_old,
      split_old_edge G a b hfst hadj d0]
    exact hc1 d0
  | inr t =>
    cases t with
    | false =>
      change φ (edgeOfDart (splitOut (G := G) a.fst b.fst hfst)) =
        splitFaceFunction R a b hfst hadj c1 hagree
            ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst)) +
          splitFaceFunction R a b hfst hadj c1 hagree
            ((split R a b hfst hadj).faceOf (splitBack (G := G) a.fst b.fst hfst))
      rw [split_out_edge G a b hfst hadj, h0, split_face_function_out,
        split_face_function_back, hagree, zmod2_add_self'']
    | true =>
      change φ (edgeOfDart (splitBack (G := G) a.fst b.fst hfst)) =
        splitFaceFunction R a b hfst hadj c1 hagree
            ((split R a b hfst hadj).faceOf (splitBack (G := G) a.fst b.fst hfst)) +
          splitFaceFunction R a b hfst hadj c1 hagree
            ((split R a b hfst hadj).faceOf (splitOut (G := G) a.fst b.fst hfst))
      rw [split_back_edge G a b hfst hadj, h0, split_face_function_out,
        split_face_function_back, hagree, zmod2_add_self'']

end RotationSystem

namespace SphericalMap
variable {n : ℕ}

/-- Joining two components of a spherical map by a bridge yields a spherical map. -/
theorem exists_spherical_bridge (M : SphericalMap n) (a b : M.Dart)
    (hsep : ¬ M.graph.Reachable a.fst b.fst) :
    ∃ (N : SphericalMap n) (huv : a.fst ≠ b.fst),
      ¬ M.Adj a.fst b.fst ∧ N.graph = splitGraph M.graph a.fst b.fst huv := by
  have hfst : a.fst ≠ b.fst := fun h => hsep (h ▸ SimpleGraph.Reachable.refl _)
  have hadj : ¬ M.Adj a.fst b.fst := fun h => hsep h.reachable
  exact ⟨⟨_, split M.rotation a b hfst hadj,
    RotationSystem.split_fills_bridge M.rotation M.fills a b hfst hadj hsep⟩, hfst, hadj, rfl⟩

end SphericalMap
end SimpleGraph
