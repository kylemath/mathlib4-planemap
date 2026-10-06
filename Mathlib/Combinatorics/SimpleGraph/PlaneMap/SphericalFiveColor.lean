/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalMap
public import Mathlib.Combinatorics.SimpleGraph.Coloring.FiveColorExtension

/-!
# Five-colour extension for algebraic spherical maps

The closed-walk separation and Kempe extension proofs only use rotation and
face-sum filling. They therefore apply to the deletion-stable carrier, with
no connectedness or construction-history hypotheses.
-/

@[expose] public section

namespace SimpleGraph.SphericalMap

open scoped BigOperators

variable {n : ℕ} {M : SphericalMap n}

/-- Edge multiplicities of a walk, reduced modulo two. -/
noncomputable def walkEdgeCoeff {u v : Fin n} (p : M.graph.Walk u v)
    (e : M.graph.edgeSet) : ZMod 2 := by
  classical
  exact (p.edges.count e.val : ZMod 2)

@[simp] theorem walkEdgeCoeff_nil (u : Fin n) (e : M.graph.edgeSet) :
    walkEdgeCoeff (M := M) (.nil (u := u)) e = 0 := by
  simp [walkEdgeCoeff]

@[simp] theorem walkEdgeCoeff_cons {u v w : Fin n} (h : M.Adj u v)
    (p : M.graph.Walk v w) (e : M.graph.edgeSet) :
    walkEdgeCoeff (.cons h p) e =
      (if RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart) = e then 1 else 0) +
        walkEdgeCoeff p e := by
  classical
  change ((s(u, v) :: p.edges).count e.val : ZMod 2) = _
  by_cases he : RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart) = e
  · have hv : s(u, v) = e.val := congrArg Subtype.val he
    simp [hv, he, walkEdgeCoeff, add_comm]
  · have hv : s(u, v) ≠ e.val := fun hh => he (Subtype.ext hh)
    simp [hv, he, walkEdgeCoeff]

private theorem double_eq_zero (a : ZMod 2) : a + a = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

/-- The incidence boundary of a walk is its pair of endpoints, modulo two. -/
theorem incidentSum_walkEdgeCoeff {u v : Fin n} (p : M.graph.Walk u v)
    (x : Fin n) :
    incidentSum M (walkEdgeCoeff p) x =
      (if x = u then 1 else 0) + (if x = v then 1 else 0) := by
  classical
  induction p with
  | nil => simp [incidentSum, edgeIncidence, double_eq_zero]
  | @cons u v w h p ih =>
    have hsingle :
        (∑ e : M.graph.edgeSet, if x ∈ e.val then
          (if RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart) = e then
            (1 : ZMod 2) else 0) else 0) =
          (if x = u then 1 else 0) + (if x = v then 1 else 0) := by
      rw [Finset.sum_eq_single (RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart))]
      · simp only [mem_edgeOfDart_iff, ite_true]
        by_cases hu : x = u <;> by_cases hv : x = v <;> simp_all [h.ne, eq_comm]
      · intro e _ he
        simp [Ne.symm he]
      · simp
    have hsplit : incidentSum M (walkEdgeCoeff (.cons h p)) x =
        (∑ e : M.graph.edgeSet, if x ∈ e.val then
          (if RotationSystem.edgeOfDart (⟨(u, v), h⟩ : M.Dart) = e then
            (1 : ZMod 2) else 0) else 0) + incidentSum M (walkEdgeCoeff p) x := by
      unfold incidentSum edgeIncidence
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rw [walkEdgeCoeff_cons]
      split_ifs <;> simp
    rw [hsplit, hsingle, ih]
    have hh := double_eq_zero (if x = v then 1 else 0)
    simpa only [add_assoc, add_zero] using
      congrArg (fun z : ZMod 2 =>
        (if x = u then 1 else 0) + z + (if x = w then 1 else 0)) hh

/-- Every closed walk determines an even edge combination. -/
theorem walkEdgeCoeff_even {u : Fin n} (p : M.graph.Walk u u) :
    IsEven M (walkEdgeCoeff p) := by
  intro x
  rw [incidentSum_walkEdgeCoeff, double_eq_zero]

/-- A closed walk is a mod-two sum of face boundaries. -/
theorem walkEdgeCoeff_is_face_sum {u : Fin n} (p : M.graph.Walk u u) :
    ∃ c : M.Face → ZMod 2, ∀ e, walkEdgeCoeff p e = faceSum M c e :=
  even_is_face_sum M _ (walkEdgeCoeff_even p)

@[simp] theorem walkEdgeCoeff_append {u v w : Fin n}
    (p : M.graph.Walk u v) (q : M.graph.Walk v w) (e : M.graph.edgeSet) :
    walkEdgeCoeff (p.append q) e = walkEdgeCoeff p e + walkEdgeCoeff q e := by
  classical
  simp [walkEdgeCoeff, Walk.edges_append, List.count_append]

/-- An edge incident to an unvisited vertex has zero walk coefficient. -/
theorem walkEdgeCoeff_zero_of_not_mem_support {u v : Fin n}
    (p : M.graph.Walk u v) (x : Fin n) (hx : x ∉ p.support)
    (e : M.graph.edgeSet) (he : x ∈ e.val) : walkEdgeCoeff p e = 0 := by
  classical
  unfold walkEdgeCoeff
  suffices e.val ∉ p.edges by simp [List.count_eq_zero.mpr this]
  intro hm
  exact hx (Walk.mem_support_of_mem_edges hm he)

end SimpleGraph.SphericalMap

namespace SimpleGraph.SphericalMap

variable {n : ℕ} {M : SphericalMap n}

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

end SimpleGraph.SphericalMap

namespace SimpleGraph.SphericalMap

variable {n : ℕ} {M : SphericalMap n}

private theorem kempe_reachable_away (x : Fin n) (c : Fin n → Fin 5) (a b : Fin 5)
    {u v : {z : Fin n // z ≠ x}}
    (hu : c u.val = a ∨ c u.val = b) (hv : c v.val = a ∨ c v.val = b)
    (h : (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
      (fun z => c z.val) a b).Reachable u v) :
    (M.graph.induce {z | z ≠ x ∧ (c z = a ∨ c z = b)}).Reachable
      ⟨u.val, u.property, hu⟩ ⟨v.val, v.property, hv⟩ := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons u v w h p ih =>
    obtain ⟨q⟩ := ih h.2.2 hv
    refine ⟨.cons (v := ⟨v.val, v.property, h.2.2⟩) ?_ q⟩
    exact h.1

/-- The difficult degree-five case: distinct neighbour colours can be reduced
by a Kempe swap, using separation proved from the plane map. -/
theorem five_color_degree_five_distinct (x : Fin n) (c : Fin n → Fin 5)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (hdeg : M.graph.degree x = 5)
    (hinj : Set.InjOn c (M.graph.neighborSet x)) : M.graph.Colorable 5 := by
  classical
  obtain ⟨e, he⟩ := degree_five_neighbour_rotation x hdeg
  let v : Fin 5 → Fin n := fun i => (e i).val
  have hadj (i : Fin 5) : M.Adj x (v i) := (e i).property
  have hrot (i : Fin 5) : M.rotation.next ⟨(x, v i), hadj i⟩ =
      ⟨(x, v (i + 1)), hadj (i + 1)⟩ := he i
  have hcolors : Function.Injective (fun i => c (v i)) := by
    intro i j hij
    exact e.injective (Subtype.ext (hinj (e i).property (e j).property hij))
  have hne (i j : Fin 5) (hij : i ≠ j) : c (v i) ≠ c (v j) := hcolors.ne hij
  have hopposite :
      (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
        (fun z => c z.val) (c (v 0)) (c (v 2))).Reachable
          ⟨v 0, (hadj 0).ne.symm⟩ ⟨v 2, (hadj 2).ne.symm⟩ →
      ¬ (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
        (fun z => c z.val) (c (v 1)) (c (v 3))).Reachable
          ⟨v 1, (hadj 1).ne.symm⟩ ⟨v 3, (hadj 3).ne.symm⟩ := by
    intro h02 h13
    exact heawood_hopposite c x v hadj hrot hcolors
      (kempe_reachable_away (M := M) x c (c (v 0)) (c (v 2)) (Or.inl rfl) (Or.inr rfl) h02)
      (kempe_reachable_away (M := M) x c (c (v 1)) (c (v 3)) (Or.inl rfl) (Or.inr rfl) h13)
  obtain ⟨full, hfull⟩ := Kempe.five_color_degree_five M.graph x
    (v 0) (v 1) (v 2) (v 3) (v 4) c hproper hdeg
    (hadj 0) (hadj 1) (hadj 2) (hadj 3) (hadj 4)
    (hadj 0).ne.symm (hadj 1).ne.symm (hadj 2).ne.symm
    (hadj 3).ne.symm (hadj 4).ne.symm
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 0 4 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide))
    (hne 1 4 (by decide)) (hne 2 3 (by decide)) (hne 2 4 (by decide))
    (hne 3 4 (by decide)) hopposite
  exact ⟨Coloring.mk full (fun h => hfull _ _ h)⟩

/-- A five-colouring of the deleted graph gives a five-colouring of the whole
plane map whenever the deleted vertex has degree at most five. The resulting
colouring may recolour a Kempe component. -/
theorem five_color_extension (x : Fin n) (hdeg : M.graph.degree x ≤ 5)
    (hcolour : (M.graph.induce {z | z ≠ x}).Colorable 5) :
    M.graph.Colorable 5 := by
  classical
  obtain ⟨colour⟩ := hcolour
  let c : Fin n → Fin 5 := fun z => if hz : z = x then 0 else colour ⟨z, hz⟩
  have hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val) := by
    intro u v huv
    have hu : u.val ≠ x := u.property
    have hv : v.val ≠ x := v.property
    simpa [c, hu, hv] using colour.valid huv
  by_cases hsmall : ((M.graph.neighborFinset x).image c).card ≤ 4
  · obtain ⟨full, hfull, _⟩ := Kempe.five_color_degree_at_most_four
      M.graph x c hproper (Or.inr hsmall)
    exact ⟨Coloring.mk full (fun h => hfull _ _ h)⟩
  · have himage : ((M.graph.neighborFinset x).image c).card ≤ M.graph.degree x :=
      Finset.card_image_le
    have hfive : M.graph.degree x = 5 := by omega
    have hcard : ((M.graph.neighborFinset x).image c).card =
        (M.graph.neighborFinset x).card := by
      rw [card_neighborFinset_eq_degree]
      omega
    have hinj := Finset.injOn_of_card_image_eq hcard
    apply five_color_degree_five_distinct x c hproper hfive
    simpa only [coe_neighborFinset] using hinj

end SimpleGraph.SphericalMap
