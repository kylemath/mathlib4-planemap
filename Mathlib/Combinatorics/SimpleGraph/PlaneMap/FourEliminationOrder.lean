module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FourColorSmallOrder

/-!
# Spherical four-elimination certificates

A certificate lists vertices to isolate, the corresponding spherical carriers,
and strict decreases in edge count. Its finite length is executable; witness
existence and colouring soundness are separate mathematical theorems.
-/

@[expose] public section
namespace SimpleGraph.SphericalMap
variable {n : ℕ}

/-- A finite spherical vertex-elimination certificate. Isolated vertex labels
are retained, and each step removes a positive-degree vertex of degree at most
four. The carrier equality identifies the exact graph transformation. -/
inductive FourEliminationOrder : SphericalMap n → Type
  | done (M : SphericalMap n) (hedgeless : ∀ u v, ¬ M.Adj u v) : FourEliminationOrder M
  | step (M : SphericalMap n) (x : Fin n) (N : SphericalMap n)
      (hgraph : N.graph = M.isolateGraph x)
      (hpositive : 0 < M.graph.degree x) (hdegree : M.graph.degree x ≤ 4)
      (hdecrease : Fintype.card N.graph.edgeSet < Fintype.card M.graph.edgeSet)
      (tail : FourEliminationOrder N) : FourEliminationOrder M

namespace FourEliminationOrder

/-- Number of vertex-isolation steps in a certificate. -/
def length {M : SphericalMap n} : FourEliminationOrder M → ℕ
  | .done _ _ => 0
  | .step _ _ _ _ _ _ _ tail => tail.length + 1

/-- The recorded decreases bound certificate length by the initial edge count. -/
theorem length_le_edges {M : SphericalMap n} (order : FourEliminationOrder M) :
    order.length ≤ Fintype.card M.graph.edgeSet := by
  induction order with
  | done M h => exact Nat.zero_le _
  | step M x N hgraph hpos hdeg hlt tail ih =>
    change tail.length + 1 ≤ _
    omega

/-- Certificate soundness uses the spherical degree-four extension rule. -/
theorem colorable {M : SphericalMap n} (order : FourEliminationOrder M) :
    M.graph.Colorable 4 := by
  induction order with
  | done M hedge =>
    exact ⟨Coloring.mk (fun _ => (0 : Fin 4)) (fun {u v} h => (hedge u v h).elim)⟩
  | step M x N hgraph hpos hdeg hlt tail ih =>
    have hc : (M.isolateGraph x).Colorable 4 := hgraph ▸ ih
    obtain ⟨c⟩ := hc
    apply four_color_extension x hdeg
    exact ⟨Coloring.mk (fun z => c z.val) (fun {u v} huv =>
      c.valid ⟨huv, u.property, v.property⟩)⟩

end FourEliminationOrder

/-- The graph elimination condition supplies a finite spherical certificate.
This is an existence theorem; computing the carriers and choosing the vertices
requires a separate executable implementation. -/
theorem exists_fourEliminationOrder (M : SphericalMap n)
    (helim : M.graph.HasFourElimination) : Nonempty (FourEliminationOrder M) := by
  classical
  generalize hk : Fintype.card M.graph.edgeSet = k
  induction k using Nat.strong_induction_on generalizing M with
  | h k ih =>
    by_cases hd : Nonempty M.Dart
    · obtain ⟨d⟩ := hd
      obtain ⟨x, hxpos, hxdeg⟩ := helim M.graph le_rfl d
      obtain ⟨N, hN, hlt⟩ := M.isolate_closed x hxpos
      have hsub : N.graph ≤ M.graph := by
        rw [hN]
        exact fun _ _ h => h.1
      have helimN : N.graph.HasFourElimination :=
        fun H hH d => helim H (hH.trans hsub) d
      obtain ⟨tail⟩ := ih _ (by omega) N helimN rfl
      exact ⟨.step M x N hN hxpos hxdeg hlt tail⟩
    · exact ⟨.done M (fun u v h => hd ⟨⟨(u, v), h⟩⟩)⟩

/-- Small spherical maps admit explicit finite elimination certificates. -/
theorem exists_fourEliminationOrder_of_order_le_eleven (M : SphericalMap n)
    (hn : n ≤ 11) : Nonempty (FourEliminationOrder M) :=
  M.exists_fourEliminationOrder (M.hasFourElimination_of_order_le_eleven hn)

end SimpleGraph.SphericalMap
