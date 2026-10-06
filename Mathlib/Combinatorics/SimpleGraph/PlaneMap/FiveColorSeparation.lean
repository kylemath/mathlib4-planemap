/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.JordanWalkParity

/-!
# Separation of alternating bichromatic walks

Face coefficients of a closed walk are constant along walks disjoint from it.
At a vertex, crossing an edge used an odd number of times changes the face
coefficient. This proves the Heawood separation needed for five colouring
without a global Jordan partition or a connected-cycle-cut constructor.
-/

@[expose] public section

namespace SimpleGraph.PlaneMap

variable {n : ℕ} {M : PlaneMap n}

private theorem eq_of_sum_zero (a b : ZMod 2) (h : a + b = 0) : a = b := by
  have hb : b + b = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
  calc
    a = a + (b + b) := by rw [hb, add_zero]
    _ = (a + b) + b := (add_assoc _ _ _).symm
    _ = b := by rw [h, zero_add]

/-- The two face coefficients adjacent to a walk-unused edge agree. -/
theorem face_coeff_eq_of_walkEdgeCoeff_zero {u : Fin n}
    (p : M.graph.Walk u u) (c : M.Face → ZMod 2)
    (hc : ∀ e, walkEdgeCoeff p e = faceSum M c e) (d : M.Dart)
    (hd : walkEdgeCoeff p (RotationSystem.edgeOfDart d) = 0) :
    c (M.faceOf d) = c (M.faceOf d.symm) := by
  apply eq_of_sum_zero
  rw [← cycle_faceSum_edgeOfDart, ← hc, hd]

/-- All outgoing darts at an unvisited vertex have the same face coefficient. -/
theorem face_coeff_eq_at_unvisited_vertex {u : Fin n}
    (p : M.graph.Walk u u) (c : M.Face → ZMod 2)
    (hc : ∀ e, walkEdgeCoeff p e = faceSum M c e)
    {x : Fin n} (hx : x ∉ p.support) (d e : M.Dart)
    (hd : d.fst = x) (he : e.fst = x) :
    c (M.faceOf d) = c (M.faceOf e) := by
  have step (a : M.Dart) (ha : a.fst = x) :
      c (M.faceOf a) = c (M.faceOf (M.rotation.next a)) := by
    calc
      _ = c (M.faceOf a.symm) := face_coeff_eq_of_walkEdgeCoeff_zero p c hc a
        (walkEdgeCoeff_zero_of_not_mem_support p x hx _
          ((mem_edgeOfDart_iff a x).2 (Or.inl ha)))
      _ = _ := by simpa using congrArg c (M.rotation.face_of_face_next a.symm).symm
  obtain ⟨k, hk⟩ := M.rotation.cyclic d e (hd.trans he.symm)
  have hi : ∀ k, (((M.rotation.next : M.Dart → M.Dart)^[k]) d).fst = x ∧
      c (M.faceOf d) = c (M.faceOf (((M.rotation.next : M.Dart → M.Dart)^[k]) d)) := by
    intro k
    induction k with
    | zero => simp [hd]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨(M.rotation.next_fst _).trans ih.1, ih.2.trans (step _ ih.1)⟩
  simpa [hk] using (hi k).2

/-- A walk avoiding a closed walk preserves its face coefficient. -/
theorem face_coeff_eq_along_disjoint_walk {u x y : Fin n}
    (p : M.graph.Walk u u) (c : M.Face → ZMod 2)
    (hc : ∀ e, walkEdgeCoeff p e = faceSum M c e)
    (q : M.graph.Walk x y) (hq : ∀ z ∈ q.support, z ∉ p.support)
    (d e : M.Dart) (hd : d.fst = x) (he : e.fst = y) :
    c (M.faceOf d) = c (M.faceOf e) := by
  induction q generalizing d with
  | nil =>
      exact face_coeff_eq_at_unvisited_vertex p c hc
        (hq _ (Walk.start_mem_support _)) d e hd he
  | @cons x y z h q ih =>
    let a : M.Dart := ⟨(x, y), h⟩
    have hx := hq x (Walk.start_mem_support _)
    have hq' : ∀ t ∈ q.support, t ∉ p.support := fun t ht =>
      hq t (by simp only [Walk.support_cons, List.mem_cons]; exact Or.inr ht)
    calc
      _ = c (M.faceOf a) := face_coeff_eq_at_unvisited_vertex p c hc hx d a hd rfl
      _ = c (M.faceOf a.symm) := face_coeff_eq_of_walkEdgeCoeff_zero p c hc a
        (walkEdgeCoeff_zero_of_not_mem_support p x hx _
          ((mem_edgeOfDart_iff a x).2 (Or.inl rfl)))
      _ = c (M.faceOf e) := ih hq' a.symm rfl he

/-- An odd edge between two even edges in the rotation separates their heads
for walks avoiding the closed walk. -/
theorem closed_walk_separates {u : Fin n} (p : M.graph.Walk u u)
    (d1 d2 d3 : M.Dart)
    (h12 : M.rotation.next d1 = d2) (h23 : M.rotation.next d2 = d3)
        (h2 : walkEdgeCoeff p (RotationSystem.edgeOfDart d2) = 1)
    (q : M.graph.Walk d1.snd d3.snd)
    (hq : ∀ z ∈ q.support, z ∉ p.support) : False := by
  obtain ⟨c, hc⟩ := walkEdgeCoeff_is_face_sum p
  have hface12 : c (M.faceOf d1.symm) = c (M.faceOf d2) := by
    simpa [← h12] using congrArg c (M.rotation.face_of_face_next d1.symm).symm
  have hface23 : c (M.faceOf d2.symm) = c (M.faceOf d3) := by
    simpa [← h23] using congrArg c (M.rotation.face_of_face_next d2.symm).symm
  have hright := face_coeff_eq_of_walkEdgeCoeff_zero p c hc d3
    (walkEdgeCoeff_zero_of_not_mem_support p d3.snd
      (hq _ (Walk.end_mem_support q)) _ ((mem_edgeOfDart_iff d3 _).2 (Or.inr rfl)))
  have hwalk := face_coeff_eq_along_disjoint_walk p c hc q hq d1.symm d3.symm rfl rfl
  have heq : c (M.faceOf d2) = c (M.faceOf d2.symm) :=
    hface12.symm.trans (hwalk.trans (hright.symm.trans hface23.symm))
  have hsum : c (M.faceOf d2) + c (M.faceOf d2.symm) = 1 := by
    rw [← cycle_faceSum_edgeOfDart, ← hc, h2]
  rw [← heq, ← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2,
    zero_mul] at hsum
  exact zero_ne_one hsum

/-- Walks through alternating neighbours must meet if both avoid the centre. -/
theorem alternating_walks_intersect
    {x v0 v1 v2 v3 : Fin n}
    (h0 : M.Adj x v0) (h1 : M.Adj x v1)
    (h2 : M.Adj x v2) (h3 : M.Adj x v3)
    (h02 : v0 ≠ v2)
    (h12 : M.rotation.next ⟨(x, v1), h1⟩ = ⟨(x, v2), h2⟩)
    (h23 : M.rotation.next ⟨(x, v2), h2⟩ = ⟨(x, v3), h3⟩)
    (p : M.graph.Walk v0 v2) (hp : x ∉ p.support)
    (q : M.graph.Walk v1 v3) (hq : x ∉ q.support) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  classical
  by_contra hdis
  have hdis' : ∀ z ∈ q.support, z ∉ p.support := by
    intro z hz hpz
    exact hdis ⟨z, hpz, hz⟩
  let d0 : M.Dart := ⟨(x, v0), h0⟩
  let d2 : M.Dart := ⟨(x, v2), h2⟩
  let loop : M.graph.Walk x x := .cons h0 (p.append h2.symm.toWalk)
  have he02 : RotationSystem.edgeOfDart d0 ≠ RotationSystem.edgeOfDart d2 := by
    intro hh
    rcases (RotationSystem.edge_of_dart_eq_iff d0 d2).1 hh with hh | hh
    · exact h02 (congrArg (fun d : M.Dart => d.snd) hh)
    · exact h2.ne (congrArg (fun d : M.Dart => d.fst) hh)
  have hpzero := walkEdgeCoeff_zero_of_not_mem_support p x hp
    (RotationSystem.edgeOfDart d2) ((mem_edgeOfDart_iff d2 x).2 (Or.inl rfl))
  have hodd : walkEdgeCoeff loop (RotationSystem.edgeOfDart d2) = 1 := by
    simp only [loop, walkEdgeCoeff_cons, walkEdgeCoeff_append]
    change (if RotationSystem.edgeOfDart d0 = RotationSystem.edgeOfDart d2 then
      (1 : ZMod 2) else 0) + (walkEdgeCoeff p (RotationSystem.edgeOfDart d2) +
      ((if RotationSystem.edgeOfDart d2.symm = RotationSystem.edgeOfDart d2 then
        1 else 0) + 0)) = 1
    simp [he02, hpzero, RotationSystem.edge_of_dart_symm]
  apply closed_walk_separates loop ⟨(x, v1), h1⟩ d2 ⟨(x, v3), h3⟩ h12 h23 hodd q
  intro z hz
  simp only [loop, Walk.support_cons, List.mem_cons, Walk.mem_support_append_iff,
    Adj.toWalk, Walk.support_nil, List.not_mem_nil, or_false]
  rintro (rfl | hpz | rfl | rfl)
  · exact hq hz
  · exact hdis' z hz hpz
  · exact hdis' _ hz (Walk.end_mem_support p)
  · exact hq hz

/-- Degree five supplies a cyclic enumeration of all five neighbours, without
assuming that the map is a triangulation. -/
theorem degree_five_neighbour_rotation (x : Fin n) (hdeg : M.graph.degree x = 5) :
    ∃ e : Fin 5 ≃ M.graph.neighborSet x, ∀ i : Fin 5,
      M.rotation.next (M.graph.dartOfNeighborSet x (e i)) =
        M.graph.dartOfNeighborSet x (e (i + 1)) := by
  classical
  have hn : Nonempty (M.graph.neighborSet x) := by
    apply Fintype.card_pos_iff.1
    rw [card_neighborSet_eq_degree, hdeg]
    decide
  obtain ⟨w⟩ := hn
  let σ := M.rotation.neighborRotation x
  let P := Function.minimalPeriod (⇑σ) w
  have hP : P = 5 := (M.rotation.neighbor_period_eq_degree x w).trans hdeg
  let e : Fin 5 ≃ M.graph.neighborSet x :=
    (finCongr hP.symm).trans (M.rotation.neighborOrbitEquiv x w)
  have he (i : Fin 5) : e i = (⇑σ)^[i.val] w := rfl
  have hnext (i : Fin 5) : σ (e i) = e (i + 1) := by
    rw [he, he]
    have hm : (i.val + 1) % 5 = (i.val + 1) % P := by rw [hP]
    simp only [Fin.val_add, Fin.val_one]
    rw [hm]
    exact (Function.iterate_mod_minimalPeriod_eq.trans
      (Function.iterate_succ_apply' _ _ _)).symm
  refine ⟨e, fun i => ?_⟩
  rw [← M.rotation.neighbor_rotation_dart, hnext]

/-- Heawood separation for two pairs of differently coloured neighbours.
The reachability relations are in the actual bichromatic induced subgraphs of
`M.graph` with the centre deleted. Properness is not needed for separation. -/
theorem heawood_hopposite {α : Type*} (c : Fin n → α) (x : Fin n)
    (v : Fin 5 → Fin n) (hadj : ∀ i, M.Adj x (v i))
    (hrot : ∀ i : Fin 5,
      M.rotation.next ⟨(x, v i), hadj i⟩ = ⟨(x, v (i + 1)), hadj (i + 1)⟩)
    (hcolors : Function.Injective (fun i => c (v i))) :
    let B := fun i j : Fin 5 =>
      M.graph.induce {z | z ≠ x ∧ (c z = c (v i) ∨ c z = c (v j))}
    (B 0 2).Reachable ⟨v 0, (hadj 0).ne.symm, Or.inl rfl⟩
      ⟨v 2, (hadj 2).ne.symm, Or.inr rfl⟩ →
    ¬ (B 1 3).Reachable ⟨v 1, (hadj 1).ne.symm, Or.inl rfl⟩
      ⟨v 3, (hadj 3).ne.symm, Or.inr rfl⟩ := by
  dsimp only
  rintro ⟨p⟩ ⟨q⟩
  let p' := p.map (Embedding.induce _).toHom
  let q' := q.map (Embedding.induce _).toHom
  have hp' : ∀ z ∈ p'.support, z ≠ x ∧ (c z = c (v 0) ∨ c z = c (v 2)) := by
    intro z hz
    simp only [p', Walk.support_map, List.mem_map] at hz
    obtain ⟨a, _, ha⟩ := hz
    change a.val = z at ha
    exact ha ▸ a.property
  have hq' : ∀ z ∈ q'.support, z ≠ x ∧ (c z = c (v 1) ∨ c z = c (v 3)) := by
    intro z hz
    simp only [q', Walk.support_map, List.mem_map] at hz
    obtain ⟨a, _, ha⟩ := hz
    change a.val = z at ha
    exact ha ▸ a.property
  have hv02 : v 0 ≠ v 2 := by
    intro hh
    have := hcolors (congrArg c hh)
    norm_num at this
  obtain ⟨z, hpz, hqz⟩ := alternating_walks_intersect
    (hadj 0) (hadj 1) (hadj 2) (hadj 3) hv02
    (by simpa using hrot 1) (by simpa using hrot 2)
    p' (fun hh => (hp' x hh).1 rfl) q' (fun hh => (hq' x hh).1 rfl)
  rcases (hp' z hpz).2 with h0 | h2 <;>
    rcases (hq' z hqz).2 with h1 | h3
  · have := hcolors (h0.symm.trans h1); norm_num at this
  · have := hcolors (h0.symm.trans h3); norm_num at this
  · have := hcolors (h2.symm.trans h1); norm_num at this
  · have := hcolors (h2.symm.trans h3); norm_num at this

end SimpleGraph.PlaneMap
