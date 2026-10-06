/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationInsert
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationBoundary

/-!
# Edge coefficients under insertion into a raw rotation carrier

Adding a missing edge identifies the new edge set with the old edge set plus one
edge. An even combination that vanishes on the inserted edge restricts to an
even old combination. None of these statements assumes generated construction
history, face agreement, connectedness, or filling.
-/

@[expose] public section
namespace SimpleGraph
open scoped BigOperators
open PlaneMapConstruction
namespace RotationSystem
open Classical
variable {n : ℕ}

/-- The inserted edge, independently of the faces of the chosen corners. -/
def splitNewEdge (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (_hadj : ¬ G.Adj a.fst b.fst) :
    (splitGraph G a.fst b.fst hfst).edgeSet :=
  ⟨s(a.fst, b.fst), by
    change (splitGraph G a.fst b.fst hfst).Adj a.fst b.fst
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

@[simp]
theorem splitNewEdge_val (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    (splitNewEdge G a b hfst hadj).val = s(a.fst, b.fst) :=
  rfl

@[simp]
theorem split_out_edge (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    RotationSystem.edgeOfDart (splitOut (G := G) a.fst b.fst hfst) =
      splitNewEdge G a b hfst hadj := by
  apply Subtype.ext
  rfl

@[simp]
theorem split_back_edge (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    RotationSystem.edgeOfDart (splitBack (G := G) a.fst b.fst hfst) =
      splitNewEdge G a b hfst hadj := by
  rw [splitBack, RotationSystem.edge_of_dart_symm, split_out_edge]

/-- An old edge, viewed as an edge of the enlarged graph. -/
def splitMapEdge (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (_hadj : ¬ G.Adj a.fst b.fst) (e : G.edgeSet) :
    (splitGraph G a.fst b.fst hfst).edgeSet :=
  ⟨e.val, by
    rcases e with ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro x y h
    change (splitGraph G a.fst b.fst hfst).Adj x y
    exact Or.inl h⟩

theorem splitMapEdge_val (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) (e : G.edgeSet) :
    (splitMapEdge G a b hfst hadj e).val = e.val :=
  rfl

@[simp]
theorem split_old_edge (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst) (hadj : ¬ G.Adj a.fst b.fst) (d : G.Dart) :
    edgeOfDart (splitOld a.fst b.fst hfst d) =
      splitMapEdge G a b hfst hadj (edgeOfDart d) := by
  apply Subtype.ext
  rfl

theorem splitMapEdge_injective (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    Function.Injective (splitMapEdge G a b hfst hadj) := by
  intro e₁ e₂ h
  exact Subtype.ext
    (congrArg (fun e : (splitGraph G a.fst b.fst hfst).edgeSet => e.val) h)

theorem splitMapEdge_ne_new (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) (e : G.edgeSet) :
    splitMapEdge G a b hfst hadj e ≠
      splitNewEdge G a b hfst hadj := by
  intro h
  have hv : e.val = s(a.fst, b.fst) := congrArg Subtype.val h
  have he : e.val ∈ G.edgeSet := e.property
  rw [hv] at he
  exact hadj he

theorem split_edge_dichotomy (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst)
    (e : (splitGraph G a.fst b.fst hfst).edgeSet) :
    e = splitNewEdge G a b hfst hadj ∨
      ∃ e0, e = splitMapEdge G a b hfst hadj e0 := by
  rcases e with ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro x y h
  rcases h with hold | hnew | hrev
  · refine Or.inr ⟨⟨s(x, y), hold⟩, ?_⟩
    apply Subtype.ext
    rfl
  · refine Or.inl ?_
    apply Subtype.ext
    change s(x, y) = s(a.fst, b.fst)
    have hx : x = a.fst := hnew.1
    have hy : y = b.fst := hnew.2
    subst hx; subst hy
    rfl
  · refine Or.inl ?_
    apply Subtype.ext
    change s(x, y) = s(a.fst, b.fst)
    have hx : x = b.fst := hrev.1
    have hy : y = a.fst := hrev.2
    subst hx; subst hy
    exact Sym2.eq_swap

/-- Pair the new chord with the transported old edges. -/
noncomputable def splitEdgeToFun (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    Option G.edgeSet → (splitGraph G a.fst b.fst hfst).edgeSet
  | none => splitNewEdge G a b hfst hadj
  | some e => splitMapEdge G a b hfst hadj e

theorem splitEdgeToFun_none (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    splitEdgeToFun G a b hfst hadj none =
      splitNewEdge G a b hfst hadj :=
  rfl

theorem splitEdgeToFun_some (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) (e : G.edgeSet) :
    splitEdgeToFun G a b hfst hadj (some e) =
      splitMapEdge G a b hfst hadj e :=
  rfl

theorem splitEdgeToFun_bijective (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    Function.Bijective (splitEdgeToFun G a b hfst hadj) := by
  refine ⟨?inj, ?surj⟩
  · intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some e =>
        exact (splitMapEdge_ne_new G a b hfst hadj e hxy.symm).elim
    | some e =>
      cases y with
      | none => exact (splitMapEdge_ne_new G a b hfst hadj e hxy).elim
      | some e' =>
        exact congrArg (Option.some (α := G.edgeSet))
          (splitMapEdge_injective G a b hfst hadj hxy)
  · intro e
    rcases split_edge_dichotomy G a b hfst hadj e with h | ⟨e0, h⟩
    · exact ⟨none, h.symm⟩
    · exact ⟨some e0, h.symm⟩

noncomputable def splitEdgeEquiv (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) :
    Option G.edgeSet ≃ (splitGraph G a.fst b.fst hfst).edgeSet :=
  Equiv.ofBijective (splitEdgeToFun G a b hfst hadj)
    (splitEdgeToFun_bijective G a b hfst hadj)

/-- Restrict a split combination to the old edges. -/
def restrictSplit (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst)
    (φ : (splitGraph G a.fst b.fst hfst).edgeSet → ZMod 2) :
    G.edgeSet → ZMod 2 :=
  fun e => φ (splitMapEdge G a b hfst hadj e)

theorem split_new_edge_darts (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst)
    (d : (splitGraph G a.fst b.fst hfst).Dart)
    (h : RotationSystem.edgeOfDart d = splitNewEdge G a b hfst hadj) :
    d = splitOut (G := G) a.fst b.fst hfst ∨
      d = splitBack (G := G) a.fst b.fst hfst :=
  (RotationSystem.edge_of_dart_eq_iff d
    (splitOut (G := G) a.fst b.fst hfst)).1
    (h.trans (split_out_edge G a b hfst hadj).symm)

theorem split_out_ne_back (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (_hadj : ¬ G.Adj a.fst b.fst) :
    splitOut (G := G) a.fst b.fst hfst ≠
      splitBack (G := G) a.fst b.fst hfst := by
  intro h
  exact hfst (congrArg (fun d : (splitGraph G a.fst b.fst hfst).Dart => d.fst) h)

theorem sum_split_edges (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst)
    (g : (splitGraph G a.fst b.fst hfst).edgeSet → ZMod 2) :
    ∑ e, g e = g (splitNewEdge G a b hfst hadj) +
      ∑ e, g (splitMapEdge G a b hfst hadj e) := by
  have h := Fintype.sum_equiv (splitEdgeEquiv G a b hfst hadj)
    (fun x => g (splitEdgeEquiv G a b hfst hadj x)) g
    (fun _ => rfl)
  have hopt : ∑ x : Option G.edgeSet,
      g (splitEdgeEquiv G a b hfst hadj x) =
      g (splitNewEdge G a b hfst hadj) +
        ∑ e, g (splitMapEdge G a b hfst hadj e) := by
    rw [Fintype.sum_option]
    simp only [splitEdgeEquiv, Equiv.ofBijective_apply]
    rw [splitEdgeToFun_none]
    refine congrArg (fun t => g (splitNewEdge G a b hfst hadj) + t) ?_
    exact Finset.sum_congr rfl (fun e _ =>
      congrArg g (splitEdgeToFun_some G a b hfst hadj e))
  exact h.symm.trans hopt

theorem mem_splitNewEdge (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst) (v : Fin n) :
    v ∈ (splitNewEdge G a b hfst hadj).val ↔
      v = a.fst ∨ v = b.fst := by
  simp [splitNewEdge, Sym2.mem_iff]

theorem incident_sum_split (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst)
    (φ : (splitGraph G a.fst b.fst hfst).edgeSet → ZMod 2) (v : Fin n) :
    edgeIncidence (splitGraph G a.fst b.fst hfst) φ v =
      edgeIncidence G (restrictSplit G a b hfst hadj φ) v +
        if v = a.fst ∨ v = b.fst then
          φ (splitNewEdge G a b hfst hadj) else 0 := by
  unfold edgeIncidence restrictSplit
  have hsum := sum_split_edges G a b hfst hadj
    (fun e => if v ∈ e.val then φ e else 0)
  have hnew : (if v ∈ (splitNewEdge G a b hfst hadj).val then
      φ (splitNewEdge G a b hfst hadj) else 0) =
      if v = a.fst ∨ v = b.fst then
        φ (splitNewEdge G a b hfst hadj) else 0 := by
    simp
  have hold : (∑ e, if v ∈ (splitMapEdge G a b hfst hadj e).val then
      φ (splitMapEdge G a b hfst hadj e) else 0) =
      ∑ e, if v ∈ e.val then
        φ (splitMapEdge G a b hfst hadj e) else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    rfl
  rw [hsum, hnew, hold]
  ac_rfl

theorem even_restrict_split (G : SimpleGraph (Fin n)) (a b : G.Dart)
    (hfst : a.fst ≠ b.fst)
    (hadj : ¬ G.Adj a.fst b.fst)
    (φ : (splitGraph G a.fst b.fst hfst).edgeSet → ZMod 2)
    (hφ : FaceEven (G := splitGraph G a.fst b.fst hfst) φ)
    (h0 : φ (splitNewEdge G a b hfst hadj) = 0) :
    FaceEven (G := G) (restrictSplit G a b hfst hadj φ) := by
  intro v
  have hv := hφ v
  have h := incident_sum_split G a b hfst hadj φ v
  have hite : (if v = a.fst ∨ v = b.fst then
      φ (splitNewEdge G a b hfst hadj) else 0) = 0 := by
    split_ifs <;> simp [h0]
  rw [h, hite, add_zero] at hv
  exact hv

end RotationSystem
end SimpleGraph
