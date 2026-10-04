/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap
public import Mathlib.Data.ZMod.Basic

/-!
# Even edge sets

`boundary` counts, modulo 2, how many darts of a face lie on an edge. A bridge
contributes both of its darts, so its coefficient is `0`. `IsEven` says every
vertex meets the edge set in even degree. The one-vertex map, which has no
edges, is the base of the induction that writes every even set as a sum of
face boundaries. A leaf edge added by `grow` is a bridge and cannot appear in
an even set.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators
open PlaneMapConstruction

namespace PlaneMap

open Classical

variable {n : ℕ}

/-- The coefficient of an edge on a face: the number of boundary darts, modulo 2.
A bridge contributes both of its darts, hence coefficient `0`. -/
noncomputable def boundary (M : PlaneMap n) (f : M.Face) (e : M.graph.edgeSet) : ZMod 2 :=
  (Fintype.card {d : M.Dart // M.faceOf d = f ∧ RotationSystem.edgeOfDart d = e} : ZMod 2)

theorem boundary_eq (M : PlaneMap n) (f : M.Face) (e : M.graph.edgeSet) :
    M.boundary f e =
      (Fintype.card {d : M.Dart // M.faceOf d = f ∧ RotationSystem.edgeOfDart d = e} : ZMod 2) :=
  rfl

/-- The sum of the coefficients of the edges incident to `v`. -/
noncomputable def incidentSum (M : PlaneMap n) (φ : M.graph.edgeSet → ZMod 2) (v : Fin n) :
    ZMod 2 :=
  ∑ e : M.graph.edgeSet, if v ∈ e.val then φ e else 0

/-- Every vertex has even degree in the support of `φ`. -/
def IsEven (M : PlaneMap n) (φ : M.graph.edgeSet → ZMod 2) : Prop :=
  ∀ v, incidentSum M φ v = 0

/-- The one-vertex map has no edges, so the zero combination is the only even set. -/
public theorem even_boundary_vertex (φ : vertex.graph.edgeSet → ZMod 2) :
    ∃ c : vertex.Face → ZMod 2, ∀ e, φ e = ∑ f, c f * vertex.boundary f e := by
  refine ⟨fun _ => 0, ?_⟩
  intro e
  obtain ⟨s, hs⟩ := e
  rw [vertex_graph] at hs
  simp at hs

/-- The new edge of a one-leaf extension. -/
def growNewEdge {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n) :
    (growGraph H u).edgeSet :=
  ⟨s(u.castSucc, Fin.last n), (grow_graph_adj_last u u).2 rfl⟩

/-- The new edge, as an edge of the grown plane map. -/
def growLeafEdge {n : ℕ} (M : PlaneMap n) (u : Fin n) (c : M.rotation.Corner u) :
    (M.grow u c).graph.edgeSet :=
  ⟨s(u.castSucc, Fin.last n), by
    change (growGraph M.graph u).Adj _ _
    exact (grow_graph_adj_last (H := M.graph) u u).2 rfl⟩

@[simp]
theorem growLeafEdge_val {n : ℕ} (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) :
    (growLeafEdge M u c).val = (growNewEdge M.graph u).val :=
  rfl

@[simp]
theorem grow_out_edge {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n) :
    RotationSystem.edgeOfDart (growOut (H := H) u) = growNewEdge H u := by
  apply Subtype.ext
  rfl

@[simp]
theorem grow_back_edge {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n) :
    RotationSystem.edgeOfDart (growBack (H := H) u) = growNewEdge H u := by
  rw [growBack, RotationSystem.edge_of_dart_symm, grow_out_edge]

theorem grow_new_edge_darts {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n)
    (d : (growGraph H u).Dart)
    (h : RotationSystem.edgeOfDart d = growNewEdge H u) :
    d = growOut (H := H) u ∨ d = growBack (H := H) u :=
  (RotationSystem.edge_of_dart_eq_iff d (growOut (H := H) u)).1
    (h.trans (grow_out_edge H u).symm)

theorem grow_edge_of_last {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n)
    (e : (growGraph H u).edgeSet) (h : Fin.last n ∈ e.val) :
    e = growNewEdge H u := by
  rcases e with ⟨e, he⟩
  revert he h
  refine Sym2.inductionOn e ?_
  intro x y hxy hmem
  have hlast : x = Fin.last n ∨ y = Fin.last n := by
    simpa [Sym2.mem_iff, eq_comm] using hmem
  have hadj : (growGraph H u).Adj x y := hxy
  rcases hlast with hx | hy
  · subst hx
    have hyu : y = u.castSucc := by
      rcases hadj with ⟨v, w, _, hv, hw⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact (Fin.castSucc_ne_last v hv).elim
      · exact (Fin.castSucc_ne_last u hx.symm).elim
      · exact hy
    subst hyu
    apply Subtype.ext
    exact Sym2.eq_swap
  · subst hy
    have hxu : x = u.castSucc := by
      rcases hadj with ⟨v, w, _, hv, hw⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact (Fin.castSucc_ne_last w hw).elim
      · exact hx
      · exact (Fin.castSucc_ne_last u hy.symm).elim
    subst hxu
    rfl

theorem incident_sum_grow_last {n : ℕ} (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) (φ : (M.grow u c).graph.edgeSet → ZMod 2) :
    incidentSum (M.grow u c) φ (Fin.last n) =
      φ (growLeafEdge M u c) := by
  classical
  unfold incidentSum
  have hsupport : ∀ e : (M.grow u c).graph.edgeSet,
      (Fin.last n ∈ e.val) ↔ e = growLeafEdge M u c := by
    intro e
    constructor
    · intro h
      apply Subtype.ext
      have hmem : e.val ∈ (growGraph M.graph u).edgeSet := e.property
      have huniq := grow_edge_of_last M.graph u ⟨e.val, hmem⟩ h
      simpa [growNewEdge, growLeafEdge] using congrArg Subtype.val huniq
    · intro he
      subst e
      simp [growLeafEdge, Sym2.mem_iff]
  refine (Finset.sum_eq_single (growLeafEdge M u c) ?_ ?_).trans ?_
  · intro e _ hne
    have : Fin.last n ∉ e.val := fun h => hne ((hsupport e).1 h)
    simp [this]
  · intro h
    exact (h (Finset.mem_univ _)).elim
  · simp [growLeafEdge, Sym2.mem_iff]

/-- A leaf has degree one, so an even combination vanishes on the new edge. -/
theorem even_grow_new_zero {n : ℕ} (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) (φ : (M.grow u c).graph.edgeSet → ZMod 2)
    (hφ : IsEven (M.grow u c) φ) :
    φ (growLeafEdge M u c) = 0 := by
  simpa [incident_sum_grow_last] using hφ (Fin.last n)

theorem grow_before_new_same_face {n : ℕ} {H : SimpleGraph (Fin n)}
    (R : RotationSystem H) (u : Fin n) (a : H.Dart) (ha : a.fst = u) :
    (growBefore u R a ha).faceOf (growOut u) =
      (growBefore u R a ha).faceOf (growBack u) := by
  rw [← RotationSystem.face_of_face_next, grow_before_face_out]

theorem grow_isolated_new_same_face {n : ℕ} {H : SimpleGraph (Fin n)}
    (u : Fin n) (hconn : H.Connected) (hiso : ∀ w, ¬ H.Adj u w) :
    (growIsolated u hconn hiso).faceOf (growOut u) =
      (growIsolated u hconn hiso).faceOf (growBack u) := by
  rw [← RotationSystem.face_of_face_next, grow_isolated_face_out]

theorem grow_new_same_face {n : ℕ} (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) :
    (M.grow u c).faceOf (growOut (H := M.graph) u) =
      (M.grow u c).faceOf (growBack (H := M.graph) u) := by
  cases c with
  | before a ha =>
    simpa [grow, PlaneMapData.grow, PlaneMapConstruction.grow] using
      grow_before_new_same_face M.rotation u a ha
  | isolated hiso =>
    simpa [grow, PlaneMapData.grow, PlaneMapConstruction.grow] using
      grow_isolated_new_same_face u M.connected hiso

theorem boundary_grow_new {n : ℕ} (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) (f : (M.grow u c).Face) :
    (M.grow u c).boundary f (growLeafEdge M u c) = 0 := by
  classical
  let d0 : (M.grow u c).Dart :=
    ⟨(u.castSucc, Fin.last n), (growLeafEdge M u c).property⟩
  have h0 : RotationSystem.edgeOfDart d0 = growLeafEdge M u c := by
    apply Subtype.ext
    rfl
  have hd0 : d0 = growOut (H := M.graph) u := by
    apply Dart.ext
    rfl
  have hsame : (M.grow u c).faceOf d0 = (M.grow u c).faceOf d0.symm := by
    have h := grow_new_same_face M u c
    rw [hd0]
    exact h
  let S := {d : (M.grow u c).Dart //
    RotationSystem.edgeOfDart d = growLeafEdge M u c}
  let T := {d : (M.grow u c).Dart //
    (M.grow u c).faceOf d = f ∧
      RotationSystem.edgeOfDart d = growLeafEdge M u c}
  have hequiv : S ≃ Bool :=
    RotationSystem.edgeFiberBoolEquiv (growLeafEdge M u c) d0 h0
  have hcardS : Fintype.card S = 2 :=
    (Fintype.card_congr hequiv).trans Fintype.card_bool
  have hpair : ∀ d : S, d.val = d0 ∨ d.val = d0.symm :=
    fun d => (RotationSystem.edge_of_dart_eq_iff d.val d0).1
      (d.property.trans h0.symm)
  rw [boundary_eq]
  by_cases hf : (M.grow u c).faceOf d0 = f
  · have hT : ∀ d : S, (M.grow u c).faceOf d.val = f := by
      intro d
      rcases hpair d with hd | hd
      · rwa [hd]
      · rwa [hd, ← hsame]
    let e : T ≃ S :=
      { toFun := fun d => ⟨d.val, d.property.2⟩
        invFun := fun d => ⟨d.val, And.intro (hT d) d.property⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
    have hcard : Fintype.card T = 2 := (Fintype.card_congr e).trans hcardS
    rw [hcard]
    decide
  · have : IsEmpty T := ⟨fun d => by
      rcases hpair ⟨d.val, d.property.2⟩ with hd | hd
      · exact hf (hd ▸ d.property.1)
      · exact hf (hsame ▸ hd ▸ d.property.1)⟩
    have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
    rw [hcard]
    decide

/-- Transport an old edge into a one-leaf extension. -/
def growOldEdge {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n)
    (e : H.edgeSet) : (growGraph H u).edgeSet :=
  ⟨Sym2.map Fin.castSucc e.val, by
    revert e
    intro e
    rcases e with ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro x y h
    change (growGraph H u).Adj x.castSucc y.castSucc
    exact (grow_graph_adj_cast u x y).2 h⟩

theorem grow_old_edge_dart {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n)
    (d : H.Dart) :
    RotationSystem.edgeOfDart (growOld u d) =
      growOldEdge H u (RotationSystem.edgeOfDart d) := by
  apply Subtype.ext
  change s(d.fst.castSucc, d.snd.castSucc) = Sym2.map Fin.castSucc s(d.fst, d.snd)
  rw [Sym2.map_mk]

theorem grow_isolated_unique_edge {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n)
    (hconn : H.Connected) (hiso : ∀ w, ¬ H.Adj u w)
    (e : (growGraph H u).edgeSet) : e = growNewEdge H u := by
  let : IsEmpty H.Dart := RotationSystem.is_empty_dart_of_isolated hconn hiso
  rcases e with ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro x y h
  rcases h with hold | hnew | hrev
  · obtain ⟨v, w, hvw, _, _⟩ := hold
    exact isEmptyElim (⟨(v, w), hvw⟩ : H.Dart)
  · apply Subtype.ext
    change s(x, y) = s(u.castSucc, Fin.last n)
    have hxy : (x, y) = (u.castSucc, Fin.last n) := Prod.ext hnew.1 hnew.2
    simp [hxy]
  · apply Subtype.ext
    change s(x, y) = s(u.castSucc, Fin.last n)
    have hxy : (x, y) = (Fin.last n, u.castSucc) := Prod.ext hrev.1 hrev.2
    simp [hxy]

/-- An even combination on a leaf grown at an isolated corner is a face-boundary sum. -/
theorem even_boundary_grow_isolated {n : ℕ} (M : PlaneMap n) (u : Fin n)
    (hiso : ∀ w, ¬ M.graph.Adj u w)
    (φ : (M.grow u (.isolated hiso)).graph.edgeSet → ZMod 2)
    (hφ : IsEven (M.grow u (.isolated hiso)) φ) :
    ∃ c : (M.grow u (.isolated hiso)).Face → ZMod 2,
      ∀ e, φ e = ∑ f, c f * (M.grow u (.isolated hiso)).boundary f e := by
  refine ⟨fun _ => 0, ?_⟩
  intro e
  have he : e = growLeafEdge M u (.isolated hiso) := by
    apply Subtype.ext
    have huniq := grow_isolated_unique_edge M.graph u M.connected hiso
      ⟨e.val, e.property⟩
    simpa [growNewEdge, growLeafEdge] using congrArg Subtype.val huniq
  rw [he, even_grow_new_zero M u (.isolated hiso) φ hφ]
  simp [boundary_grow_new]

theorem mem_growOldEdge {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n)
    (e : H.edgeSet) (x : Fin n) :
    x.castSucc ∈ (growOldEdge H u e).val ↔ x ∈ e.val := by
  rcases e with ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro a b _
  simp only [growOldEdge, Sym2.map_mk, Sym2.mem_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (Fin.castSucc_injective n h)
    · exact Or.inr (Fin.castSucc_injective n h)
  · intro h
    rcases h with h | h <;> simp [h]

theorem last_not_mem_growOldEdge {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n)
    (e : H.edgeSet) : Fin.last n ∉ (growOldEdge H u e).val := by
  rcases e with ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro a b _
  simp only [growOldEdge, Sym2.map_mk, Sym2.mem_iff, not_or]
  exact ⟨fun h => Fin.castSucc_ne_last a h.symm,
    fun h => Fin.castSucc_ne_last b h.symm⟩

theorem growOldEdge_injective {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n) :
    Function.Injective (growOldEdge H u) := by
  intro e₁ e₂ h
  apply Subtype.ext
  have hm := congrArg Subtype.val h
  exact (Function.Embedding.sym2Map
    ⟨Fin.castSucc, Fin.castSucc_injective n⟩).injective hm

theorem grow_edge_dichotomy {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n)
    (e : (growGraph H u).edgeSet) :
    e = growNewEdge H u ∨ ∃ e0, e = growOldEdge H u e0 := by
  rcases e with ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro x y h
  rcases h with hold | hnew | hrev
  · obtain ⟨v, w, hvw, hx, hy⟩ := hold
    refine Or.inr ⟨⟨s(v, w), hvw⟩, ?_⟩
    apply Subtype.ext
    change s(x, y) = Sym2.map Fin.castSucc s(v, w)
    have hp : (x, y) = (v.castSucc, w.castSucc) :=
      Prod.ext hx.symm hy.symm
    have hs : s(x, y) = s(v.castSucc, w.castSucc) :=
      congrArg (fun p : Fin (n + 1) × Fin (n + 1) => s(p.1, p.2)) hp
    rw [hs, Sym2.map_mk]
  · refine Or.inl ?_
    apply Subtype.ext
    change s(x, y) = s(u.castSucc, Fin.last n)
    have hxy : (x, y) = (u.castSucc, Fin.last n) := Prod.ext hnew.1 hnew.2
    simp [hxy]
  · refine Or.inl ?_
    apply Subtype.ext
    change s(x, y) = s(u.castSucc, Fin.last n)
    have hxy : (x, y) = (Fin.last n, u.castSucc) := Prod.ext hrev.1 hrev.2
    simp [hxy]

/-- An old edge, viewed as an edge of the grown plane map. -/
def growMapEdge (M : PlaneMap n) (u : Fin n) (c : M.rotation.Corner u)
    (e : M.graph.edgeSet) : (M.grow u c).graph.edgeSet :=
  ⟨(growOldEdge M.graph u e).val, (growOldEdge M.graph u e).property⟩

theorem growMapEdge_val (M : PlaneMap n) (u : Fin n) (c : M.rotation.Corner u)
    (e : M.graph.edgeSet) :
    (growMapEdge M u c e).val = (growOldEdge M.graph u e).val :=
  rfl

theorem growMapEdge_injective (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) :
    Function.Injective (growMapEdge M u c) := by
  intro e₁ e₂ h
  exact growOldEdge_injective M.graph u (Subtype.ext (congrArg Subtype.val h))

theorem grow_map_edge_dichotomy (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) (e : (M.grow u c).graph.edgeSet) :
    e = growLeafEdge M u c ∨ ∃ e0, e = growMapEdge M u c e0 := by
  rcases grow_edge_dichotomy M.graph u ⟨e.val, e.property⟩ with h | h
  · refine Or.inl (Subtype.ext ?_)
    simpa [growLeafEdge, growNewEdge] using congrArg Subtype.val h
  · obtain ⟨e0, he0⟩ := h
    refine Or.inr ⟨e0, Subtype.ext ?_⟩
    simpa [growMapEdge] using congrArg Subtype.val he0

/-- Pair the new leaf edge with the transported old edges. -/
noncomputable def growEdgeEquiv (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) :
    Option M.graph.edgeSet ≃ (M.grow u c).graph.edgeSet :=
  Equiv.ofBijective
    (fun x => match x with
      | none => growLeafEdge M u c
      | some e => growMapEdge M u c e)
    ⟨fun x y h => by
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some e =>
          have hv := congrArg Subtype.val h
          have : Fin.last n ∈ (growMapEdge M u c e).val := by
            rw [← hv]
            simp [growLeafEdge, Sym2.mem_iff]
          exact (last_not_mem_growOldEdge M.graph u e this).elim
      | some e =>
        cases y with
        | none =>
          have hv := congrArg Subtype.val h
          have : Fin.last n ∈ (growMapEdge M u c e).val := by
            rw [hv]
            simp [growLeafEdge, Sym2.mem_iff]
          exact (last_not_mem_growOldEdge M.graph u e this).elim
        | some e' =>
          exact congrArg some (growMapEdge_injective M u c h),
      fun e => by
        rcases grow_map_edge_dichotomy M u c e with h | ⟨e0, h⟩
        · exact ⟨none, h.symm⟩
        · exact ⟨some e0, h.symm⟩⟩

/-- Restrict an even combination on a grown map to the old edges. -/
def restrictGrow (M : PlaneMap n) (u : Fin n) (c : M.rotation.Corner u)
    (φ : (M.grow u c).graph.edgeSet → ZMod 2) :
    M.graph.edgeSet → ZMod 2 :=
  fun e => φ (growMapEdge M u c e)

theorem sum_grow_edges (M : PlaneMap n) (u : Fin n) (c : M.rotation.Corner u)
    (f : (M.grow u c).graph.edgeSet → ZMod 2) :
    ∑ e, f e = f (growLeafEdge M u c) + ∑ e, f (growMapEdge M u c e) := by
  have h := Fintype.sum_equiv (growEdgeEquiv M u c) (fun x => f (growEdgeEquiv M u c x)) f
    (fun _ => rfl)
  have hopt : ∑ x : Option M.graph.edgeSet, f (growEdgeEquiv M u c x) =
      f (growLeafEdge M u c) + ∑ e, f (growMapEdge M u c e) := by
    rw [Fintype.sum_option]
    rfl
  exact h.symm.trans hopt

theorem incident_sum_grow_cast (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) (φ : (M.grow u c).graph.edgeSet → ZMod 2)
    (v : Fin n) :
    incidentSum (M.grow u c) φ v.castSucc =
      incidentSum M (restrictGrow M u c φ) v +
        if v = u then φ (growLeafEdge M u c) else 0 := by
  unfold incidentSum restrictGrow
  have hsum := sum_grow_edges M u c
    (fun e => if v.castSucc ∈ e.val then φ e else 0)
  have hleaf : (if v.castSucc ∈ (growLeafEdge M u c).val then
      φ (growLeafEdge M u c) else 0) =
      if v = u then φ (growLeafEdge M u c) else 0 := by
    have : v.castSucc ∈ (growLeafEdge M u c).val ↔ v = u := by
      simp only [growLeafEdge, Sym2.mem_iff]
      constructor
      · intro h
        rcases h with h | h
        · exact Fin.castSucc_injective n h
        · exact (Fin.castSucc_ne_last v h).elim
      · intro h
        exact Or.inl (congrArg Fin.castSucc h)
    by_cases hv : v = u
    · rw [if_pos (this.2 hv), if_pos hv]
    · rw [if_neg (fun h => hv (this.1 h)), if_neg hv]
  have hold : (∑ e, if v.castSucc ∈ (growMapEdge M u c e).val then
      φ (growMapEdge M u c e) else 0) =
      ∑ e, if v ∈ e.val then φ (growMapEdge M u c e) else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    simp [growMapEdge, mem_growOldEdge]
  rw [hsum, hleaf, hold]
  ac_rfl

theorem even_restrict_grow (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) (φ : (M.grow u c).graph.edgeSet → ZMod 2)
    (hφ : IsEven (M.grow u c) φ) :
    IsEven M (restrictGrow M u c φ) := by
  intro v
  have hcast := incident_sum_grow_cast M u c φ v
  have h0 := hφ v.castSucc
  have hleaf := even_grow_new_zero M u c φ hφ
  have hite : (if v = u then φ (growLeafEdge M u c) else 0) = 0 := by
    split_ifs <;> simp [hleaf]
  rw [hcast, hite, add_zero] at h0
  exact h0

/-- The linear combination of face boundaries given by coefficients `c`. -/
public noncomputable def faceSum (M : PlaneMap n) (c : M.Face → ZMod 2)
    (e : M.graph.edgeSet) : ZMod 2 :=
  ∑ f, c f * M.boundary f e

theorem grow_before_face_of_old {n : ℕ} {H : SimpleGraph (Fin n)}
    (R : RotationSystem H) (u : Fin n) (a : H.Dart) (ha : a.fst = u)
    (d : H.Dart) :
    (growBefore u R a ha).faceOf (growOld u d) =
      growBeforeFaceEquiv u R a ha (R.faceOf d) := by
  change (growBefore u R a ha).faceOf (growOld u d) =
    ((growBefore u R a ha).faceQuotientEquiv (growOut u)).symm
      (growBeforeOrbitEquiv u R a ha (R.faceQuotientEquiv a (R.faceOf d)))
  have h1 : R.faceQuotientEquiv a (R.faceOf d) = Quotient.mk R.faceSetoid d :=
    rfl
  have h2 : growBeforeOrbitEquiv u R a ha (Quotient.mk R.faceSetoid d) =
      Quotient.mk (growBefore u R a ha).faceSetoid (growOld u d) :=
    rfl
  have h3 : ((growBefore u R a ha).faceQuotientEquiv (growOut u)).symm
      (Quotient.mk (growBefore u R a ha).faceSetoid (growOld u d)) =
      (growBefore u R a ha).faceOf (growOld u d) :=
    rfl
  rw [h1, h2, h3]

theorem grow_map_is_old {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n)
    (e : H.edgeSet) (d : (growGraph H u).Dart)
    (h : RotationSystem.edgeOfDart d = growOldEdge H u e) :
    ∃ d0 : H.Dart, d = growOld u d0 := by
  obtain ⟨x, rfl⟩ := (growDartEquiv (H := H) u).surjective d
  cases x with
  | inl d0 => exact ⟨d0, rfl⟩
  | inr b =>
    have hleaf : RotationSystem.edgeOfDart (growDartEquiv (H := H) u (.inr b)) =
        growNewEdge H u := by
      cases b with
      | false => exact grow_out_edge H u
      | true => exact grow_back_edge H u
    have hne : growOldEdge H u e ≠ growNewEdge H u := by
      intro heq
      exact last_not_mem_growOldEdge H u e (by
        rw [heq]
        simp [growNewEdge, Sym2.mem_iff])
    exact (hne (h.symm.trans hleaf)).elim

theorem grow_before_rotation {n : ℕ} (M : PlaneMap n) (u : Fin n)
    (a : M.Dart) (ha : a.fst = u) :
    (M.grow u (.before a ha)).rotation = growBefore u M.rotation a ha :=
  rfl

theorem growOld_injective {n : ℕ} (H : SimpleGraph (Fin n)) (u : Fin n) :
    Function.Injective (growOld (H := H) u) :=
  fun d e h => Sum.inl.inj (grow_dart_injective u (by
    change growDart u (.inl d) = growDart u (.inl e)
    exact h))

theorem grow_old_edge_eq_map (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u) (d : M.Dart) :
    RotationSystem.edgeOfDart (growOld (H := M.graph) u d) =
      growMapEdge M u c (RotationSystem.edgeOfDart d) := by
  apply Subtype.ext
  simpa [growMapEdge] using congrArg Subtype.val (grow_old_edge_dart M.graph u d)

theorem boundary_grow_map_before (M : PlaneMap n) (u : Fin n)
    (a : M.Dart) (ha : a.fst = u) (f : M.Face) (e : M.graph.edgeSet) :
    (M.grow u (.before a ha)).boundary
      (growBeforeFaceEquiv u M.rotation a ha f)
      (growMapEdge M u (.before a ha) e) = M.boundary f e := by
  apply Eq.trans (boundary_eq _ _ _)
  apply Eq.symm
  apply Eq.trans (boundary_eq _ _ _)
  apply Eq.symm
  let S := {d : M.Dart // M.faceOf d = f ∧ RotationSystem.edgeOfDart d = e}
  let T := {d : (M.grow u (.before a ha)).Dart //
    (M.grow u (.before a ha)).faceOf d =
      growBeforeFaceEquiv u M.rotation a ha f ∧
    RotationSystem.edgeOfDart d = growMapEdge M u (.before a ha) e}
  have hfiber (d : S) : (growOld u d.val : (M.grow u (.before a ha)).Dart) ∈
      {d : (M.grow u (.before a ha)).Dart |
        (M.grow u (.before a ha)).faceOf d =
          growBeforeFaceEquiv u M.rotation a ha f ∧
        RotationSystem.edgeOfDart d = growMapEdge M u (.before a ha) e} := by
    constructor
    · change (growBefore u M.rotation a ha).faceOf (growOld u d.val) =
        growBeforeFaceEquiv u M.rotation a ha f
      rw [grow_before_face_of_old]
      exact congrArg (growBeforeFaceEquiv u M.rotation a ha) d.property.1
    · have hmap := grow_old_edge_eq_map M u (.before a ha) d.val
      rw [d.property.2] at hmap
      exact hmap
  let toT (d : S) : T := ⟨growOld u d.val, hfiber d⟩
  have hinj : Function.Injective toT :=
    fun d₁ d₂ h => Subtype.ext (growOld_injective M.graph u (congrArg Subtype.val h))
  have hsurj : Function.Surjective toT := by
    intro t
    have hedge : RotationSystem.edgeOfDart t.val = growOldEdge M.graph u e :=
      Subtype.ext (congrArg Subtype.val t.property.2)
    obtain ⟨d0, hd0⟩ := grow_map_is_old M.graph u e t.val hedge
    have hf : M.faceOf d0 = f := by
      have h := t.property.1
      rw [hd0] at h
      change (growBefore u M.rotation a ha).faceOf (growOld u d0) =
        growBeforeFaceEquiv u M.rotation a ha f at h
      rw [grow_before_face_of_old] at h
      exact (growBeforeFaceEquiv u M.rotation a ha).injective h
    have he : RotationSystem.edgeOfDart d0 = e := by
      have h := t.property.2
      rw [hd0] at h
      have hmap := grow_old_edge_eq_map M u (.before a ha) d0
      exact growMapEdge_injective M u (.before a ha) (hmap.symm.trans h)
    exact ⟨⟨d0, And.intro hf he⟩, Subtype.ext hd0.symm⟩
  exact congrArg Nat.cast
    (Fintype.card_congr (Equiv.ofBijective toT ⟨hinj, hsurj⟩)).symm

/-- Even combinations remain face-boundary sums after attaching a leaf. -/
public theorem even_boundary_grow (M : PlaneMap n) (u : Fin n)
    (c : M.rotation.Corner u)
    (hM : ∀ φ : M.graph.edgeSet → ZMod 2, IsEven M φ →
      ∃ d : M.Face → ZMod 2, ∀ e, φ e = faceSum M d e)
    (φ : (M.grow u c).graph.edgeSet → ZMod 2)
    (hφ : IsEven (M.grow u c) φ) :
    ∃ d : (M.grow u c).Face → ZMod 2,
      ∀ e, φ e = faceSum (M.grow u c) d e := by
  cases c with
  | isolated hiso =>
    exact even_boundary_grow_isolated M u hiso φ hφ
  | before a ha =>
    obtain ⟨c0, hc0⟩ := hM (restrictGrow M u (.before a ha) φ)
      (even_restrict_grow M u (.before a ha) φ hφ)
    let Φ := growBeforeFaceEquiv u M.rotation a ha
    refine ⟨fun f => c0 (Φ.symm f), ?_⟩
    intro e
    rcases grow_map_edge_dichotomy M u (.before a ha) e with he | ⟨e0, he⟩
    · rw [he, even_grow_new_zero M u (.before a ha) φ hφ]
      unfold faceSum
      simp [boundary_grow_new]
    · rw [he]
      have hφe : φ (growMapEdge M u (.before a ha) e0) = faceSum M c0 e0 :=
        hc0 e0
      rw [hφe]
      unfold faceSum
      exact Fintype.sum_equiv Φ
        (fun f0 => c0 f0 * M.boundary f0 e0)
        (fun f => c0 (Φ.symm f) *
          (M.grow u (.before a ha)).boundary f
            (growMapEdge M u (.before a ha) e0))
        (fun f0 => by
          rw [Equiv.symm_apply_apply, boundary_grow_map_before])

end PlaneMap

end SimpleGraph
