/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalChordInsert
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationBridgeFills

/-!
# Triangulation completion of a spherical map

On a nonempty carrier, a spherical map in which every vertex has degree at least
two is contained, on the same labels, in a connected spherical map all of whose
faces are triangles. Each step either joins two components by a bridge or
inserts a chord into a face of length at least four. Both preserve filling.
Minimum positive degree two excludes faces shorter than three, and the number
of missing vertex pairs strictly decreases.

The carrier is assumed nonempty: on `Fin 0` the degree hypothesis is vacuous,
while a connected graph needs a vertex.
-/

@[expose] public section
namespace SimpleGraph
open PlaneMapConstruction
namespace SphericalMap
variable {n : ℕ}

/-- Every dart-face of `M` is a triangle. -/
def Triangulated (M : SphericalMap n) : Prop :=
  ∀ d : M.Dart, M.rotation.faceLength (M.faceOf d) = 3

theorem natCard_edgeSet_split (G : SimpleGraph (Fin n)) (u v : Fin n) (huv : u ≠ v)
    (hmiss : ¬ G.Adj u v) :
    Nat.card (splitGraph G u v huv).edgeSet = Nat.card G.edgeSet + 1 := by
  classical
  have h := split_card_edges (G := G) u v huv hmiss
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card,
    ← edgeFinset_card]
  convert h

theorem natCard_edgeSet_le (G : SimpleGraph (Fin n)) :
    Nat.card G.edgeSet ≤ n.choose 2 := by
  classical
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  simpa using G.card_edgeFinset_le_card_choose_two

theorem le_splitGraph (G : SimpleGraph (Fin n)) (u v : Fin n) (huv : u ≠ v) :
    G ≤ splitGraph G u v huv := fun _ _ h => Or.inl h

/-- **Triangulation completion.** On a nonempty carrier, a spherical map whose
vertices all have degree at least two embeds, on the same labels, in a connected
spherical map whose faces are all triangles. -/
theorem exists_triangulated_completion (hn : 0 < n) (M : SphericalMap n)
    (hdeg : ∀ x, 2 ≤ M.graph.degree x) :
    ∃ T : SphericalMap n, M.graph ≤ T.graph ∧ T.graph.Connected ∧ T.Triangulated := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- strong induction on the number of missing vertex pairs
  suffices H : ∀ m : ℕ, ∀ M : SphericalMap n, n.choose 2 - Nat.card M.graph.edgeSet = m →
      (∀ x, 2 ≤ M.graph.degree x) →
      ∃ T : SphericalMap n, M.graph ≤ T.graph ∧ T.graph.Connected ∧ T.Triangulated from
    H _ M rfl hdeg
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro M hm hdeg
  -- one insertion step, given the new map and its edge relation
  have step : ∀ (N : SphericalMap n) (u v : Fin n) (huv : u ≠ v), ¬ M.Adj u v →
      N.graph = splitGraph M.graph u v huv →
      ∃ T : SphericalMap n, M.graph ≤ T.graph ∧ T.graph.Connected ∧ T.Triangulated := by
    intro N u v huv hmiss hN
    have hcard : Nat.card N.graph.edgeSet = Nat.card M.graph.edgeSet + 1 := by
      rw [hN]; exact natCard_edgeSet_split M.graph u v huv hmiss
    have hle : M.graph ≤ N.graph := hN ▸ le_splitGraph M.graph u v huv
    have hbound := natCard_edgeSet_le N.graph
    have hlt : n.choose 2 - Nat.card N.graph.edgeSet < m := by omega
    have hdegN : ∀ x, 2 ≤ N.graph.degree x := fun x =>
      (hdeg x).trans (degree_le_of_le hle)
    obtain ⟨T, hT, hconn, htri⟩ := ih _ hlt N rfl hdegN
    exact ⟨T, hle.trans hT, hconn, htri⟩
  by_cases hconn : M.graph.Connected
  · by_cases htri : M.Triangulated
    · exact ⟨M, le_rfl, hconn, htri⟩
    · obtain ⟨d, hd⟩ : ∃ d : M.Dart, M.rotation.faceLength (M.faceOf d) ≠ 3 := by
        by_contra h
        push Not at h
        exact htri h
      have hsupp : ∀ x ∈ M.graph.support, 2 ≤ M.graph.degree x := fun x _ => hdeg x
      have h3 := M.rotation.three_le_face_length_of_min_degree_two hsupp d
      have hlen : 4 ≤ M.rotation.faceLength (M.faceOf d) :=
        Nat.lt_of_le_of_ne h3 (fun h => hd h.symm)
      obtain ⟨N, u, v, huv, hmiss, hN⟩ := M.exists_spherical_chord hsupp d hlen
      exact step N u v huv hmiss hN
  · have hpre : ¬ M.graph.Preconnected := fun h => hconn ⟨h⟩
    obtain ⟨x, y, hxy⟩ : ∃ x y, ¬ M.graph.Reachable x y := by
      by_contra h
      push Not at h
      exact hpre h
    obtain ⟨x', hx'⟩ := M.graph.degree_pos_iff_exists_adj x |>.1 (by have := hdeg x; omega)
    obtain ⟨y', hy'⟩ := M.graph.degree_pos_iff_exists_adj y |>.1 (by have := hdeg y; omega)
    let a : M.Dart := ⟨(x, x'), hx'⟩
    let b : M.Dart := ⟨(y, y'), hy'⟩
    obtain ⟨N, huv, hmiss, hN⟩ := M.exists_spherical_bridge a b hxy
    exact step N a.fst b.fst huv hmiss hN

/-- **Completion into the Gate-D class.** On a nonempty carrier, a spherical map
of minimum degree at least five embeds, on the same labels, in a connected
spherical triangulation of minimum degree at least five. -/
theorem exists_triangulated_completion_min_five (hn : 0 < n) (M : SphericalMap n)
    (hdeg : ∀ x, 5 ≤ M.graph.degree x) :
    ∃ T : SphericalMap n, M.graph ≤ T.graph ∧ T.graph.Connected ∧ T.Triangulated ∧
      ∀ x, 5 ≤ T.graph.degree x := by
  classical
  obtain ⟨T, hle, hconn, htri⟩ :=
    exists_triangulated_completion hn M (fun x => (by omega : 2 ≤ 5).trans (hdeg x))
  exact ⟨T, hle, hconn, htri, fun x => (hdeg x).trans (degree_le_of_le hle)⟩

end SphericalMap
end SimpleGraph
