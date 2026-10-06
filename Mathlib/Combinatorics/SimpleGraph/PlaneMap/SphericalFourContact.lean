/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalCompletion
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SupportTransport
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FourColorExtension

/-!
# A conditional four-colour contact theorem

Support-cardinality induction composes isolation, support relabelling and
triangulation completion. The degree-five extension hypothesis is explicit
and unproved. No Kempe components are transported across completion.
-/

@[expose] public section
namespace SimpleGraph.SphericalMap

/-- The remaining extension obligation, restricted to connected spherical
triangulations of minimum degree five. The root is chosen before a colouring. -/
def TriangulatedFiveExtension : Prop :=
  ∀ (n : ℕ) (T : SphericalMap n), 0 < n → T.graph.Connected → T.Triangulated →
    (∀ x, 5 ≤ T.graph.degree x) →
    ∃ r, T.graph.degree r = 5 ∧
      ((T.graph.induce {z | z ≠ r}).Colorable 4 → T.graph.Colorable 4)

/-- If the degree-five triangulated extension obligation holds, every spherical
map is four-colourable. This is a conditional assembly theorem, not Gate D. -/
theorem four_color_of_triangulated_five_extension (hgate : TriangulatedFiveExtension)
    {n : ℕ} (M : SphericalMap n) : M.graph.Colorable 4 := by
  classical
  suffices H : ∀ k, ∀ (n : ℕ) (M : SphericalMap n), Nat.card M.graph.support = k →
      M.graph.Colorable 4 from H _ n M rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro n M hk
    by_cases hd : Nonempty M.Dart
    · obtain ⟨d⟩ := hd
      by_cases hlow : ∃ x ∈ M.graph.support, M.graph.degree x ≤ 4
      · obtain ⟨x, hx, hdeg⟩ := hlow
        have hxpos := (M.graph.degree_pos_iff_mem_support x).mpr hx
        obtain ⟨N, hN, _⟩ := M.isolate_closed x hxpos
        have hlt : Nat.card N.graph.support < k := by
          rw [hN, ← hk]
          exact M.isolate_support_card_lt x hx
        obtain ⟨c⟩ := ih _ hlt n N rfl
        apply M.four_color_extension x hdeg
        exact ⟨SimpleGraph.Coloring.mk (fun z => c z.val) (fun {u v} huv =>
          c.valid (by rw [hN]; exact ⟨huv, u.property, v.property⟩))⟩
      · have hmin : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x := by
          intro x hx
          by_contra h
          exact hlow ⟨x, hx, by omega⟩
        let s := Nat.card M.graph.support
        let i := M.supportEquivFin
        let S := M.supportTransport i
        have hs : 0 < s := by
          exact Nat.card_pos_iff.mpr ⟨⟨⟨d.fst, d.adj.mem_support_left⟩⟩, inferInstance⟩
        have hS : ∀ x, 5 ≤ S.graph.degree x := M.support_min_degree i 5 hmin
        obtain ⟨T, hST, hconn, htri, hT⟩ := S.exists_triangulated_completion_min_five hs hS
        obtain ⟨r, hr, hext⟩ := hgate s T hs hconn htri hT
        have hsupport : T.graph.support = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact (T.graph.degree_pos_iff_mem_support x).mp (by have := hT x; omega)
        have hcard : Nat.card T.graph.support = s := by
          rw [hsupport]
          simp
        have hrpos : 0 < T.graph.degree r := by omega
        obtain ⟨N, hN, _⟩ := T.isolate_closed r hrpos
        have hlt : Nat.card N.graph.support < k := by
          have ht := T.isolate_support_card_lt r
            ((T.graph.degree_pos_iff_mem_support r).mp hrpos)
          rw [← hN, hcard] at ht
          exact hk ▸ ht
        obtain ⟨c⟩ := ih _ hlt s N rfl
        have hcT : T.graph.Colorable 4 := hext ⟨SimpleGraph.Coloring.mk
          (fun z => c z.val) (fun {u v} huv =>
            c.valid (by rw [hN]; exact ⟨huv, u.property, v.property⟩))⟩
        obtain ⟨cS⟩ := hcT.mono_left hST
        exact ⟨M.extendSupportColoring i (0 : Fin 4) cS⟩
    · exact ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 4)) (fun {u v} huv =>
        (hd ⟨⟨(u, v), huv⟩⟩).elim)⟩

end SimpleGraph.SphericalMap
