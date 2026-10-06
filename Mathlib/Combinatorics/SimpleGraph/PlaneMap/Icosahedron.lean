/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalMap
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
/-!
# The icosahedron as a spherical map

An explicit graph and rotation give twelve vertices, thirty edges, twenty
triangular faces, and degree five at every vertex. Labels agree with NetworkX's
`icosahedral_graph`: the finite tables are input data, whose properties are
checked by Lean's kernel.

The filling certificate is linear, rather than an exhaustive check of edge
combinations. `potentialCoeffs` integrates along a dual spanning tree rooted at
face zero. For each edge, `incidenceCoeffs` expresses the discrepancy as a
vertex-incidence combination. A finite coefficient identity then proves
`rotation.Fills` for every even edge combination simultaneously.

No external graph generator or solver is part of the proof. The tables need not
be trusted: invalid tables fail one of the finite certificates.
-/

@[expose] public section
namespace SimpleGraph.Icosahedron
open scoped BigOperators
set_option maxRecDepth 4096
/-- The thirty undirected edges, listed with increasing endpoints. -/
def endpoints : Fin 30 → Fin 12 × Fin 12 := ![(0, 1), (0, 5), (0, 7), (0, 8), (0, 11), (1, 2),
    (1, 5), (1, 6), (1, 8), (2, 3), (2, 6), (2, 8), (2, 9), (3, 4), (3, 6), (3, 9), (3, 10), (4,
    5), (4, 6), (4, 10), (4, 11), (5, 6), (5, 11), (7, 8), (7, 9), (7, 10), (7, 11), (8, 9), (9,
    10), (10, 11)]
def graph : SimpleGraph (Fin 12) where
  Adj u v := ∃ e : Fin 30, endpoints e = (u,v) ∨ endpoints e = (v,u)
  symm := by refine ⟨?_⟩; intro u v h; obtain ⟨e,h⟩ := h; exact ⟨e,h.symm⟩
  loopless := by
    refine ⟨?_⟩
    intro v h
    obtain ⟨e,h⟩ := h
    have hn : ∀ e : Fin 30, (endpoints e).1 ≠ (endpoints e).2 := by decide
    apply hn e
    rcases h with h | h <;> simp [h]

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (∃ e : Fin 30,
    endpoints e = (u,v) ∨ endpoints e = (v,u)))
/-- Successor and predecessor tables in the five-neighbour rotation. -/
def nextTable : Fin 12 → Fin 12 → Fin 12 := ![![0, 5, 0, 0, 0, 11, 0, 8, 1, 0, 0, 7], ![8, 0, 6,
    0, 0, 0, 5, 0, 2, 0, 0, 0], ![0, 8, 0, 6, 0, 0, 1, 0, 9, 3, 0, 0], ![0, 0, 9, 0, 6, 0, 2, 0,
    0, 10, 4, 0], ![0, 0, 0, 10, 0, 6, 3, 0, 0, 0, 11, 5], ![1, 6, 0, 0, 11, 0, 4, 0, 0, 0, 0,
    0], ![0, 2, 3, 4, 5, 1, 0, 0, 0, 0, 0, 0], ![11, 0, 0, 0, 0, 0, 0, 0, 0, 8, 9, 10], ![7, 0,
    1, 0, 0, 0, 0, 9, 0, 2, 0, 0], ![0, 0, 8, 2, 0, 0, 0, 10, 7, 0, 3, 0], ![0, 0, 0, 9, 3, 0,
    0, 11, 0, 7, 0, 4], ![5, 0, 0, 0, 10, 4, 0, 0, 0, 0, 7, 0]]
def prevTable : Fin 12 → Fin 12 → Fin 12 := ![![0, 8, 0, 0, 0, 1, 0, 11, 7, 0, 0, 5], ![5, 0, 8,
    0, 0, 6, 2, 0, 0, 0, 0, 0], ![0, 6, 0, 9, 0, 0, 3, 0, 1, 8, 0, 0], ![0, 0, 6, 0, 10, 0, 4,
    0, 0, 2, 9, 0], ![0, 0, 0, 6, 0, 11, 5, 0, 0, 0, 3, 10], ![11, 0, 0, 0, 6, 0, 1, 0, 0, 0, 0,
    4], ![0, 5, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0], ![8, 0, 0, 0, 0, 0, 0, 0, 9, 10, 11, 0], ![1, 2,
    9, 0, 0, 0, 0, 0, 0, 7, 0, 0], ![0, 0, 3, 10, 0, 0, 0, 8, 2, 0, 7, 0], ![0, 0, 0, 4, 11, 0,
    0, 9, 0, 3, 0, 7], ![7, 0, 0, 0, 5, 0, 0, 10, 0, 0, 4, 0]]
/-- Label of the oriented triangular face containing an adjacent pair. -/
def labelTable : Fin 12 → Fin 12 → Fin 20 := ![![0, 0, 0, 0, 0, 1, 0, 3, 4, 0, 0, 2], ![1, 0, 5,
    0, 0, 7, 6, 0, 0, 0, 0, 0], ![0, 6, 0, 8, 0, 0, 9, 0, 5, 10, 0, 0], ![0, 0, 9, 0, 11, 0, 12,
    0, 0, 8, 13, 0], ![0, 0, 0, 12, 0, 14, 15, 0, 0, 0, 11, 16], ![2, 1, 0, 0, 15, 0, 7, 0, 0,
    0, 0, 14], ![0, 7, 6, 9, 12, 15, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 17, 18, 19,
    3], ![0, 5, 10, 0, 0, 0, 0, 4, 0, 17, 0, 0], ![0, 0, 8, 13, 0, 0, 0, 17, 10, 0, 18, 0], ![0,
    0, 0, 11, 16, 0, 0, 18, 0, 13, 0, 19], ![3, 0, 0, 0, 14, 2, 0, 19, 0, 0, 16, 0]]
def edgeTable : Fin 12 → Fin 12 → Fin 30 := ![![0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 0, 4], ![0, 0, 5,
    0, 0, 6, 7, 0, 8, 0, 0, 0], ![0, 5, 0, 9, 0, 0, 10, 0, 11, 12, 0, 0], ![0, 0, 9, 0, 13, 0,
    14, 0, 0, 15, 16, 0], ![0, 0, 0, 13, 0, 17, 18, 0, 0, 0, 19, 20], ![1, 6, 0, 0, 17, 0, 21,
    0, 0, 0, 0, 22], ![0, 7, 10, 14, 18, 21, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 23,
    24, 25, 26], ![3, 8, 11, 0, 0, 0, 0, 23, 0, 27, 0, 0], ![0, 0, 12, 15, 0, 0, 0, 24, 27, 0,
    28, 0], ![0, 0, 0, 16, 19, 0, 0, 25, 0, 28, 0, 29], ![4, 0, 0, 0, 20, 22, 0, 26, 0, 0, 29,
    0]]
theorem next_adj : ∀ u v, graph.Adj u v → graph.Adj u (nextTable u v) := by decide
theorem prev_adj : ∀ u v, graph.Adj u v → graph.Adj u (prevTable u v) := by decide
def nextDart (d : graph.Dart) : graph.Dart := ⟨(d.fst, nextTable d.fst d.snd), next_adj _ _ d.adj⟩
def prevDart (d : graph.Dart) : graph.Dart := ⟨(d.fst, prevTable d.fst d.snd), prev_adj _ _ d.adj⟩
def rotation : RotationSystem graph where
  next := {
    toFun := nextDart
    invFun := prevDart
    left_inv := by
      have h : ∀ u v, graph.Adj u v → prevTable u (nextTable u v) = v := by decide
      intro d; apply Dart.ext; exact Prod.ext rfl (h _ _ d.adj)
    right_inv := by
      have h : ∀ u v, graph.Adj u v → nextTable u (prevTable u v) = v := by decide
      intro d; apply Dart.ext; exact Prod.ext rfl (h _ _ d.adj) }
  next_fst := fun _ => rfl
  cyclic := by
    have h : ∀ u v w, graph.Adj u v → graph.Adj u w →
      ∃ k : Fin 5, (nextTable u)^[k.val] v = w := by decide
    intro d e he
    obtain ⟨k,hk⟩ := h d.fst d.snd e.snd d.adj (by simp [he])
    refine ⟨k.val, ?_⟩
    apply Dart.ext
    have hi : ∀ k : ℕ, ((nextDart : graph.Dart → graph.Dart)^[k] d).toProd =
      (d.fst, (nextTable d.fst)^[k] d.snd) := by
      intro k; induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply']; change (_, nextTable _ _) = _
        rw [ih]; simp only [Function.iterate_succ_apply']
    change ((nextDart : graph.Dart → graph.Dart)^[k.val] d).toProd = e.toProd
    rw [hi]; exact Prod.ext he hk
def representatives : Fin 20 → graph.Dart := fun f => ⟨![(0, 1), (1, 0), (5, 0), (0, 7), (7, 0),
    (1, 2), (2, 1), (1, 5), (2, 3), (3, 2), (8, 2), (3, 4), (4, 3), (9, 3), (4, 5), (5, 4), (10,
    4), (7, 8), (7, 9), (7, 10)] f, by
  have h : ∀ f : Fin 20, graph.Adj ((![(0, 1), (1, 0), (5, 0), (0, 7), (7, 0), (1, 2), (2, 1),
      (1, 5), (2, 3), (3, 2), (8, 2), (3, 4), (4, 3), (9, 3), (4, 5), (5, 4), (10, 4), (7, 8),
      (7, 9), (7, 10)] : Fin 20 → Fin 12 × Fin 12) f).1 ((![(0, 1), (1, 0), (5, 0), (0, 7), (7,
      0), (1, 2), (2, 1), (1, 5), (2, 3), (3, 2), (8, 2), (3, 4), (4, 3), (9, 3), (4, 5), (5,
      4), (10, 4), (7, 8), (7, 9), (7, 10)] : Fin 20 → Fin 12 × Fin 12) f).2 := by decide
  exact h f⟩
/-- Linear face-potential reconstruction, rooted at face zero. -/
def potentialCoeffs : Fin 20 → Fin 30 → ZMod 2 := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]]
/-- Incidence combinations certifying each edge reconstruction identity. -/
def incidenceCoeffs : Fin 30 → Fin 12 → ZMod 2 := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0,
    0, 0, 0, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 0]]

theorem label_next (d : graph.Dart) :
    labelTable (rotation.faceNext d).fst (rotation.faceNext d).snd =
      labelTable d.fst d.snd := by
  have h : ∀ u v, graph.Adj u v → labelTable v (nextTable v u) = labelTable u v := by decide
  exact h _ _ d.adj

def faceIndex : rotation.Face → Fin 20
  | .inl q => Quotient.lift (fun d : graph.Dart => labelTable d.fst d.snd) (by
      intro d e h
      induction h with
      | refl d => rfl
      | step d => exact (label_next d).symm
      | symm h ih => exact ih.symm
      | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂) q
  | .inr h => False.elim (@IsEmpty.false graph.Dart h.property (representatives 0))

@[simp] theorem faceIndex_faceOf (d : graph.Dart) :
    faceIndex (rotation.faceOf d) = labelTable d.fst d.snd := rfl

def indexedEdge (e : Fin 30) : graph.edgeSet :=
  ⟨s((endpoints e).1, (endpoints e).2), by
    rw [mem_edgeSet]
    exact ⟨e, Or.inl (Prod.eta _)⟩⟩

theorem indexedEdge_dart (d : graph.Dart) :
    indexedEdge (edgeTable d.fst d.snd) = RotationSystem.edgeOfDart d := by
  have h : ∀ u v, graph.Adj u v →
      s((endpoints (edgeTable u v)).1, (endpoints (edgeTable u v)).2) = s(u,v) := by decide
  apply Subtype.ext
  exact h _ _ d.adj

theorem indexedEdge_injective : Function.Injective indexedEdge := by
  have h : ∀ i j : Fin 30,
    s((endpoints i).1, (endpoints i).2) = s((endpoints j).1, (endpoints j).2) → i = j := by decide
  intro i j hij
  exact h i j (congrArg Subtype.val hij)

theorem indexedEdge_surjective : Function.Surjective indexedEdge := by
  intro e
  obtain ⟨d, hd⟩ := RotationSystem.edge_of_dart_surjective e
  exact ⟨edgeTable d.fst d.snd, (indexedEdge_dart d).trans hd⟩

noncomputable def edgeEquiv : Fin 30 ≃ graph.edgeSet :=
  Equiv.ofBijective indexedEdge ⟨indexedEdge_injective, indexedEdge_surjective⟩

theorem edge_count : graph.edgeFinset.card = 30 := by
  classical
  have h := Fintype.card_congr edgeEquiv
  rw [edgeFinset_card]; simpa only [Fintype.card_fin] using h.symm

theorem degree_five (v : Fin 12) : graph.degree v = 5 := by
  have h : ∀ v : Fin 12, graph.degree v = 5 := by decide
  exact h v


def faceRepresentative (f : Fin 20) : rotation.Face := rotation.faceOf (representatives f)

@[simp] theorem faceIndex_representative (f : Fin 20) :
    faceIndex (faceRepresentative f) = f := by
  have h : ∀ f : Fin 20, labelTable (representatives f).fst (representatives f).snd = f := by decide
  exact h f

theorem representative_faceOf (d : graph.Dart) :
    faceRepresentative (labelTable d.fst d.snd) = rotation.faceOf d := by
  have h : ∀ u v, graph.Adj u v →
    ∃ k : Fin 3, ((fun p : Fin 12 × Fin 12 => (p.2, nextTable p.2 p.1))^[k.val])
      (representatives (labelTable u v)).toProd = (u,v) := by decide
  obtain ⟨k,hk⟩ := h d.fst d.snd d.adj
  have hi : ∀ j : ℕ, (rotation.faceNext^[j] (representatives (labelTable d.fst d.snd))).toProd =
    ((fun p : Fin 12 × Fin 12 => (p.2, nextTable p.2 p.1))^[j])
      (representatives (labelTable d.fst d.snd)).toProd := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [Function.iterate_succ_apply']
      change (_, nextTable _ _) = _
      change (((rotation.faceNext^[j] (representatives (labelTable d.fst d.snd))).toProd).2,
        nextTable (((rotation.faceNext^[j] (representatives (labelTable d.fst d.snd))).toProd).2)
          (((rotation.faceNext^[j] (representatives (labelTable d.fst d.snd))).toProd).1)) = _
      rw [ih]
  have he : rotation.faceNext^[k.val] (representatives (labelTable d.fst d.snd)) = d := by
    apply Dart.ext
    rw [hi, hk]
  apply congrArg Sum.inl
  apply Quotient.sound
  change rotation.FaceRelation (representatives (labelTable d.fst d.snd)) d
  have hr : ∀ j : ℕ, rotation.FaceRelation (representatives (labelTable d.fst d.snd))
      (rotation.faceNext^[j] (representatives (labelTable d.fst d.snd))) := by
      intro j
      induction j with
      | zero => exact .refl _
      | succ j ih => rw [Function.iterate_succ_apply']; exact ih.trans (.step _)
  simpa [he] using hr k.val

noncomputable def faceEquiv : rotation.Face ≃ Fin 20 where
  toFun := faceIndex
  invFun := faceRepresentative
  left_inv := by
    intro f
    cases f with
    | inl q =>
      induction q using Quotient.inductionOn with
      | h d => exact representative_faceOf d
    | inr h => exact False.elim (@IsEmpty.false graph.Dart h.property (representatives 0))
  right_inv := faceIndex_representative

theorem face_count : rotation.faceCount = 20 := by
  classical
  have h := Fintype.card_congr faceEquiv
  simpa only [RotationSystem.faceCount, Fintype.card_fin] using h

def incidenceEntry (e : Fin 30) (v : Fin 12) : ZMod 2 :=
  if v ∈ (indexedEdge e).val then 1 else 0

theorem incidence_coordinates (φ : graph.edgeSet → ZMod 2) (v : Fin 12) :
    edgeIncidence graph φ v = ∑ e : Fin 30, incidenceEntry e v * φ (indexedEdge e) := by
  classical
  let : DecidableRel graph.Adj := Classical.decRel _
  unfold edgeIncidence
  calc
    (∑ e : graph.edgeSet, if v ∈ e.val then φ e else 0) =
        ∑ e : Fin 30, if v ∈ (edgeEquiv e).val then φ (edgeEquiv e) else 0 :=
      (edgeEquiv.sum_comp (fun e : graph.edgeSet => if v ∈ e.val then φ e else 0)).symm
    _ = _ := by
      congr 1
      funext e
      change (if v ∈ (indexedEdge e).val then φ (indexedEdge e) else 0) = _
      simp only [incidenceEntry, ite_mul, one_mul, zero_mul]

def potential (φ : graph.edgeSet → ZMod 2) (f : Fin 20) : ZMod 2 :=
  ∑ e : Fin 30, potentialCoeffs f e * φ (indexedEdge e)

set_option maxHeartbeats 2000000 in
-- Checking the fixed incidence certificate requires more reduction than ordinary symbolic proofs.
/-- A 30 by 30 finite coefficient identity certifies filling. The incidence
combination cancels for every even edge combination, leaving a face potential. -/
theorem coefficient_certificate : ∀ u v, graph.Adj u v → ∀ e : Fin 30,
    (if edgeTable u v = e then (1 : ZMod 2) else 0) +
      ∑ x : Fin 12, incidenceCoeffs (edgeTable u v) x * incidenceEntry e x =
      potentialCoeffs (labelTable u v) e + potentialCoeffs (labelTable v u) e := by decide

theorem fills : rotation.Fills := by
  intro φ hφ
  refine ⟨fun f => potential φ (faceIndex f), ?_⟩
  intro d
  have hc := coefficient_certificate d.fst d.snd d.adj
  have hs := congrArg (fun c : Fin 30 → ZMod 2 => ∑ e : Fin 30, c e * φ (indexedEdge e))
    (funext hc)
  simp only [add_mul, Finset.sum_add_distrib,
    Finset.sum_mul] at hs
  have hzero : (∑ e : Fin 30, ∑ x : Fin 12,
      (incidenceCoeffs (edgeTable d.fst d.snd) x * incidenceEntry e x) *
        φ (indexedEdge e)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, ← incidence_coordinates]
    simp [hφ]
  rw [hzero, add_zero] at hs
  simpa [potential, ite_mul, indexedEdge_dart, Dart.symm] using hs

theorem face_length_three (f : rotation.Face) : rotation.faceLength f = 3 := by
  have hp : ∀ u v, graph.Adj u v →
      (fun p : Fin 12 × Fin 12 => (p.2, nextTable p.2 p.1))^[3] (u,v) = (u,v) := by decide
  have hperiod (d : graph.Dart) : rotation.faceNext^[3] d = d := by
    apply Dart.ext
    exact hp _ _ d.adj
  have hfix (d : graph.Dart) : rotation.faceNext d ≠ d := by
    intro he
    exact d.adj.ne (congrArg (fun a : graph.Dart => a.fst) he).symm
  rw [← faceEquiv.left_inv f]
  change rotation.faceLength (rotation.faceOf (representatives (faceIndex f))) = 3
  rw [rotation.face_length_eq_period]
  exact Function.minimalPeriod_eq_prime (hperiod _) (hfix _)

/-- The twelve-vertex icosahedron with its triangular spherical rotation. -/
def sphericalMap : SphericalMap 12 where
  graph := graph
  rotation := rotation
  fills := fills

theorem sphericalMap_degree (v : Fin 12) : sphericalMap.graph.degree v = 5 := by
  have h := degree_five v
  rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
  exact h

theorem sphericalMap_edges : sphericalMap.graph.edgeFinset.card = 30 := by
  have h := edge_count
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card] at h ⊢
  exact h

theorem sphericalMap_triangular (f : sphericalMap.Face) :
    sphericalMap.rotation.faceLength f = 3 := by
  classical
  have h := face_length_three f
  unfold RotationSystem.faceLength at h ⊢
  rw [← Nat.card_eq_fintype_card] at h ⊢
  exact h

/-- Every vertex is nonisolated, so the support threshold is attained at twelve. -/
theorem support_all : graph.support = Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true]
  have h : ∀ v : Fin 12, ∃ w, graph.Adj v w := by decide
  obtain ⟨w, hw⟩ := h v
  exact hw.mem_support_left

theorem support_count : Nat.card graph.support = 12 := by
  rw [support_all]
  simp

end SimpleGraph.Icosahedron
