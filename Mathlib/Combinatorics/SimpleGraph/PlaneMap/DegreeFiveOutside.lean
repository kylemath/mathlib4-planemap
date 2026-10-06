/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalSmallOrder
/-!
# Degree-five vertices outside an anchor

In a spherical graph of minimum positive degree five, every nonisolated anchor
has at least six degree-five vertices outside its closed neighbourhood. The
anchor and its neighbours account for their own degree deficit; Euler sparsity
forces the remaining six units of deficit outside that neighbourhood.

This guarantees eligible roots exist. It does not prove that any eligible root
permits a Kempe escape, and it supplies no colouring progress rank.
-/

@[expose] public section
namespace SimpleGraph.SphericalMap
open scoped BigOperators
variable {n : ℕ} (M : SphericalMap n)

private theorem degree_le_one_of_next_fixed_outside (d : M.Dart)
    (hd : M.rotation.next d = d) : M.graph.degree d.fst ≤ 1 := by
  classical
  have hiter : ∀ k : ℕ, (⇑M.rotation.next)^[k] d = d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hd]
  have hsub : M.graph.neighborFinset d.fst ⊆ {d.snd} := by
    intro y hy
    let e : M.Dart := ⟨(d.fst, y), (M.graph.mem_neighborFinset _ _).mp hy⟩
    obtain ⟨k, hk⟩ := M.rotation.cyclic d e rfl
    have he : e = d := hk.symm.trans (hiter k)
    exact Finset.mem_singleton.mpr (congrArg (fun e : M.Dart => e.snd) he)
  simpa using Finset.card_le_card hsub

private theorem face_length_three_of_high_degree_outside (d : M.Dart)
    (hdeg : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x) :
    3 ≤ M.rotation.faceLength (M.faceOf d) := by
  have hpos := M.rotation.face_length_pos d
  change 0 < M.rotation.faceLength (M.faceOf d) at hpos
  by_contra hlen
  change ¬ 3 ≤ M.rotation.faceLength (M.faceOf d) at hlen
  have hsmall : M.rotation.faceLength (M.faceOf d) = 1 ∨
      M.rotation.faceLength (M.faceOf d) = 2 := by omega
  have hperiod := M.rotation.face_next_iterate_length d
  rcases hsmall with hsmall | hsmall
  · rw [hsmall] at hperiod
    have hh := congrArg (fun e : M.Dart => e.fst) hperiod
    simp only [Function.iterate_one, RotationSystem.face_next_fst] at hh
    exact d.fst_ne_snd hh.symm
  · rw [hsmall] at hperiod
    have hp : M.rotation.faceNext (M.rotation.faceNext d) = d := hperiod
    have he : M.rotation.faceNext d = d.symm := by
      apply Dart.ext
      apply Prod.ext
      · exact M.rotation.face_next_fst d
      · have hh := congrArg (fun e : M.Dart => e.fst) hp
        change (M.rotation.faceNext d).snd = d.fst
        simpa only [RotationSystem.face_next_fst] using hh
    have hfixed : M.rotation.next d = d := by
      simpa only [he, RotationSystem.face_next_apply, Dart.symm_symm] using hp
    have hlo := degree_le_one_of_next_fixed_outside M d hfixed
    have hhi := hdeg d.fst d.adj.mem_support_left
    omega

/-- Minimum positive degree five forces the usual spherical edge bound. -/
theorem twice_edges_add_twelve_le_six_support (d : M.Dart)
    (hdeg : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x) :
    2 * Fintype.card M.graph.edgeSet + 12 ≤ 6 * Nat.card M.graph.support := by
  classical
  have hfaces : ∀ f : M.Face, 3 ≤ M.rotation.faceLength f := by
    intro f
    cases f with
    | inl f =>
      refine Quotient.inductionOn f ?_
      intro e
      exact face_length_three_of_high_degree_outside M e hdeg
    | inr f => exact (f.property.false d).elim
  have hf : 3 * Fintype.card M.Face ≤ 2 * Fintype.card M.graph.edgeSet := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun f _ => hfaces f)
    have hs := M.rotation.sum_face_lengths_eq_twice_card_edges
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      edgeFinset_card, Nat.mul_comm] using hh.trans_eq hs
  have he := edge_card_bound_two M d
  omega

/-- Degree-five vertices outside an anchor's closed neighbourhood. -/
noncomputable def degreeFiveOutside (a : Fin n) : Finset (Fin n) := by
  classical
  exact (M.graph.support.toFinset.erase a).filter
    (fun x => ¬ M.graph.Adj a x ∧ M.graph.degree x = 5)

/-- At least six degree-five vertices avoid the closed star of every
nonisolated anchor. This is an availability theorem, not a Kempe escape rule. -/
theorem six_le_degreeFiveOutside (a : Fin n) (ha : a ∈ M.graph.support)
    (hdeg : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x) :
    6 ≤ (degreeFiveOutside M a).card := by
  classical
  let S := M.graph.support.toFinset
  let T := S.erase a
  have haS : a ∈ S := Set.mem_toFinset.mpr ha
  have hT : T.card + 1 = S.card := by
    dsimp [T]
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨a,haS⟩
    rw [Finset.card_erase_of_mem haS]
    omega
  have hneigh : T.filter (fun x => M.graph.Adj a x) = M.graph.neighborFinset a := by
    ext x
    simp only [T, Finset.mem_filter, Finset.mem_erase, M.graph.mem_neighborFinset]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨h.ne.symm, Set.mem_toFinset.mpr h.mem_support_right⟩, h⟩
  have hp : ∀ x ∈ T,
      6 ≤ M.graph.degree x +
        (if ¬ M.graph.Adj a x ∧ M.graph.degree x = 5 then 1 else 0) +
        (if M.graph.Adj a x then 1 else 0) := by
    intro x hx
    have hxS : x ∈ M.graph.support := Set.mem_toFinset.mp (Finset.mem_erase.mp hx).2
    have hd := hdeg x hxS
    by_cases hn : M.graph.Adj a x
    · simp only [hn, not_true_eq_false, false_and, ite_false, ite_true]
      omega
    · by_cases he : M.graph.degree x = 5
      · simp [hn,he]
      · simp only [hn, not_false_eq_true, he, and_false, ite_false]
        omega
  have hsum := Finset.sum_le_sum (s := T) hp
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_boole, Nat.cast_id] at hsum
  have hsumdeg := Finset.sum_erase_add S (fun x => M.graph.degree x) haS
  have hhand := M.graph.sum_degrees_support_eq_twice_card_edges
  have hcardneigh : (T.filter (fun x => M.graph.Adj a x)).card = M.graph.degree a := by
    rw [hneigh]
    rfl
  have hQ : (T.filter (fun x => ¬ M.graph.Adj a x ∧ M.graph.degree x = 5)).card =
      (degreeFiveOutside M a).card := rfl
  rw [hcardneigh, hQ] at hsum
  obtain ⟨b,hb⟩ := M.graph.mem_support.mp ha
  have he := twice_edges_add_twelve_le_six_support M ⟨(a,b),hb⟩ hdeg
  have hs : S.card = Nat.card M.graph.support := by
    simp only [S, Set.toFinset_card, Nat.card_eq_fintype_card]
  rw [← edgeFinset_card] at he
  change (∑ x ∈ S, M.graph.degree x) = _ at hhand
  change (∑ x ∈ T, M.graph.degree x) + M.graph.degree a = _ at hsumdeg
  omega

/-- There is a degree-five vertex distinct from and nonadjacent to the anchor. -/
theorem exists_degree_five_outside (a : Fin n) (ha : a ∈ M.graph.support)
    (hdeg : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x) :
    ∃ x, x ≠ a ∧ ¬ M.graph.Adj a x ∧ M.graph.degree x = 5 := by
  classical
  have hpos : 0 < (degreeFiveOutside M a).card := by
    have h := six_le_degreeFiveOutside M a ha hdeg
    omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hpos
  change x ∈ (M.graph.support.toFinset.erase a).filter
    (fun x => ¬ M.graph.Adj a x ∧ M.graph.degree x = 5) at hx
  have hm := Finset.mem_filter.mp hx
  exact ⟨x,(Finset.mem_erase.mp hm.1).1,hm.2⟩

end SimpleGraph.SphericalMap
