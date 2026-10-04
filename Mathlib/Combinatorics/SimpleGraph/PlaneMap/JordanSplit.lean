/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Jordan
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.JordanFace

/-!
# Even sets under same-face edge insertion

The new chord of a `split` meets each of the two new faces in one dart.
An even combination either vanishes on the chord and restricts, or differs
from a restriction by one of the two new face boundaries.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators
open PlaneMapConstruction

namespace PlaneMap

open Classical

variable {n : ℕ}

/-- The new chord of a same-face split. -/
def splitNewEdge (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    (M.split a b hface hfst hadj).graph.edgeSet :=
  ⟨s(a.fst, b.fst), by
    change (splitGraph M.graph a.fst b.fst hfst).Adj a.fst b.fst
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

@[simp]
theorem splitNewEdge_val (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    (splitNewEdge M a b hface hfst hadj).val = s(a.fst, b.fst) :=
  rfl

@[simp]
theorem split_out_edge (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    RotationSystem.edgeOfDart (splitOut (G := M.graph) a.fst b.fst hfst) =
      splitNewEdge M a b hface hfst hadj := by
  apply Subtype.ext
  rfl

@[simp]
theorem split_back_edge (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    RotationSystem.edgeOfDart (splitBack (G := M.graph) a.fst b.fst hfst) =
      splitNewEdge M a b hface hfst hadj := by
  rw [splitBack, RotationSystem.edge_of_dart_symm, split_out_edge]

/-- An old edge, viewed as an edge of the split map. -/
def splitMapEdge (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (e : M.graph.edgeSet) :
    (M.split a b hface hfst hadj).graph.edgeSet :=
  ⟨e.val, by
    rcases e with ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro x y h
    change (splitGraph M.graph a.fst b.fst hfst).Adj x y
    exact Or.inl h⟩

theorem splitMapEdge_val (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (e : M.graph.edgeSet) :
    (splitMapEdge M a b hface hfst hadj e).val = e.val :=
  rfl

theorem splitMapEdge_injective (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    Function.Injective (splitMapEdge M a b hface hfst hadj) := by
  intro e₁ e₂ h
  exact Subtype.ext
    (congrArg (fun e : (M.split a b hface hfst hadj).graph.edgeSet => e.val) h)

theorem splitMapEdge_ne_new (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (e : M.graph.edgeSet) :
    splitMapEdge M a b hface hfst hadj e ≠
      splitNewEdge M a b hface hfst hadj := by
  intro h
  have hv : e.val = s(a.fst, b.fst) := congrArg Subtype.val h
  have he : e.val ∈ M.graph.edgeSet := e.property
  rw [hv] at he
  exact hadj he

theorem split_edge_dichotomy (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (e : (M.split a b hface hfst hadj).graph.edgeSet) :
    e = splitNewEdge M a b hface hfst hadj ∨
      ∃ e0, e = splitMapEdge M a b hface hfst hadj e0 := by
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
noncomputable def splitEdgeToFun (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    Option M.graph.edgeSet → (M.split a b hface hfst hadj).graph.edgeSet
  | none => splitNewEdge M a b hface hfst hadj
  | some e => splitMapEdge M a b hface hfst hadj e

theorem splitEdgeToFun_none (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    splitEdgeToFun M a b hface hfst hadj none =
      splitNewEdge M a b hface hfst hadj :=
  rfl

theorem splitEdgeToFun_some (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (e : M.graph.edgeSet) :
    splitEdgeToFun M a b hface hfst hadj (some e) =
      splitMapEdge M a b hface hfst hadj e :=
  rfl

theorem splitEdgeToFun_bijective (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    Function.Bijective (splitEdgeToFun M a b hface hfst hadj) := by
  refine ⟨?inj, ?surj⟩
  · intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some e =>
        exact (splitMapEdge_ne_new M a b hface hfst hadj e hxy.symm).elim
    | some e =>
      cases y with
      | none => exact (splitMapEdge_ne_new M a b hface hfst hadj e hxy).elim
      | some e' =>
        exact congrArg (Option.some (α := M.graph.edgeSet))
          (splitMapEdge_injective M a b hface hfst hadj hxy)
  · intro e
    rcases split_edge_dichotomy M a b hface hfst hadj e with h | ⟨e0, h⟩
    · exact ⟨none, h.symm⟩
    · exact ⟨some e0, h.symm⟩

noncomputable def splitEdgeEquiv (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    Option M.graph.edgeSet ≃ (M.split a b hface hfst hadj).graph.edgeSet :=
  Equiv.ofBijective (splitEdgeToFun M a b hface hfst hadj)
    (splitEdgeToFun_bijective M a b hface hfst hadj)

/-- Restrict a split combination to the old edges. -/
def restrictSplit (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (φ : (M.split a b hface hfst hadj).graph.edgeSet → ZMod 2) :
    M.graph.edgeSet → ZMod 2 :=
  fun e => φ (splitMapEdge M a b hface hfst hadj e)

theorem split_rotation (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    (M.split a b hface hfst hadj).rotation =
      PlaneMapConstruction.split M.rotation a b hfst hadj :=
  rfl

theorem split_new_edge_darts (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (d : (M.split a b hface hfst hadj).Dart)
    (h : RotationSystem.edgeOfDart d = splitNewEdge M a b hface hfst hadj) :
    d = splitOut (G := M.graph) a.fst b.fst hfst ∨
      d = splitBack (G := M.graph) a.fst b.fst hfst :=
  (RotationSystem.edge_of_dart_eq_iff d
    (splitOut (G := M.graph) a.fst b.fst hfst)).1
    (h.trans (split_out_edge M a b hface hfst hadj).symm)

theorem split_out_ne_back (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    splitOut (G := M.graph) a.fst b.fst hfst ≠
      splitBack (G := M.graph) a.fst b.fst hfst := by
  intro h
  exact hfst (congrArg (fun d : (M.split a b hface hfst hadj).Dart => d.fst) h)

theorem split_out_ne_back_face (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    (M.split a b hface hfst hadj).faceOf
        (splitOut (G := M.graph) a.fst b.fst hfst) ≠
      (M.split a b hface hfst hadj).faceOf
        (splitBack (G := M.graph) a.fst b.fst hfst) := by
  intro h
  have hr : (PlaneMapConstruction.split M.rotation a b hfst hadj).FaceRelation
      (splitOut (G := M.graph) a.fst b.fst hfst)
      (splitBack (G := M.graph) a.fst b.fst hfst) :=
    ((PlaneMapConstruction.split M.rotation a b hfst hadj).face_of_eq_iff _ _).1 h
  have hl := split_label_relation M.rotation a b hfst hadj hface hr
  simp [split_label_out, split_label_back] at hl

theorem boundary_split_new (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (f : (M.split a b hface hfst hadj).Face) :
    (M.split a b hface hfst hadj).boundary f
      (splitNewEdge M a b hface hfst hadj) =
      if f = (M.split a b hface hfst hadj).faceOf
          (splitOut (G := M.graph) a.fst b.fst hfst) ∨
        f = (M.split a b hface hfst hadj).faceOf
          (splitBack (G := M.graph) a.fst b.fst hfst)
      then 1 else 0 := by
  classical
  let d0 : (M.split a b hface hfst hadj).Dart :=
    splitOut (G := M.graph) a.fst b.fst hfst
  let d1 : (M.split a b hface hfst hadj).Dart :=
    splitBack (G := M.graph) a.fst b.fst hfst
  have h0 : RotationSystem.edgeOfDart d0 =
      splitNewEdge M a b hface hfst hadj :=
    split_out_edge M a b hface hfst hadj
  have h1 : RotationSystem.edgeOfDart d1 =
      splitNewEdge M a b hface hfst hadj :=
    split_back_edge M a b hface hfst hadj
  have hnf : (M.split a b hface hfst hadj).faceOf d0 ≠
      (M.split a b hface hfst hadj).faceOf d1 :=
    split_out_ne_back_face M a b hface hfst hadj
  let T := {d : (M.split a b hface hfst hadj).Dart //
    (M.split a b hface hfst hadj).faceOf d = f ∧
      RotationSystem.edgeOfDart d = splitNewEdge M a b hface hfst hadj}
  have hpair : ∀ d : T, d.val = d0 ∨ d.val = d1 :=
    fun d => split_new_edge_darts M a b hface hfst hadj d.val d.property.2
  rw [boundary_eq]
  by_cases hout : (M.split a b hface hfst hadj).faceOf d0 = f
  · have : Fintype.card T = 1 := by
      let e : T ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => ⟨d0, And.intro hout h0⟩
          left_inv := fun d => by
            apply Subtype.ext
            rcases hpair d with hd | hd
            · exact hd.symm
            · have hf : (M.split a b hface hfst hadj).faceOf d1 = f := by
                rw [← hd]; exact d.property.1
              exact (hnf (hout.trans hf.symm)).elim
          right_inv := fun _ => rfl }
      exact (Fintype.card_congr e).trans Fintype.card_unit
    have hite : (f = (M.split a b hface hfst hadj).faceOf d0 ∨
        f = (M.split a b hface hfst hadj).faceOf d1) := Or.inl hout.symm
    rw [this, ite_eq_left hite]
    decide
  · by_cases hback : (M.split a b hface hfst hadj).faceOf d1 = f
    · have : Fintype.card T = 1 := by
        let e : T ≃ Unit :=
          { toFun := fun _ => ()
            invFun := fun _ => ⟨d1, And.intro hback h1⟩
            left_inv := fun d => by
              apply Subtype.ext
              rcases hpair d with hd | hd
              · have hf : (M.split a b hface hfst hadj).faceOf d0 = f := by
                  rw [← hd]; exact d.property.1
                exact (hnf (hf.trans hback.symm)).elim
              · exact hd.symm
            right_inv := fun _ => rfl }
        exact (Fintype.card_congr e).trans Fintype.card_unit
      have hite : (f = (M.split a b hface hfst hadj).faceOf d0 ∨
          f = (M.split a b hface hfst hadj).faceOf d1) := Or.inr hback.symm
      rw [this, ite_eq_left hite]
      decide
    · have : IsEmpty T := ⟨fun d => by
        rcases hpair d with hd | hd
        · have hf : (M.split a b hface hfst hadj).faceOf d0 = f := by
            rw [← hd]; exact d.property.1
          exact hout hf
        · have hf : (M.split a b hface hfst hadj).faceOf d1 = f := by
            rw [← hd]; exact d.property.1
          exact hback hf⟩
      have hcard : Fintype.card T = 0 := Fintype.card_eq_zero
      have hite : ¬ (f = (M.split a b hface hfst hadj).faceOf d0 ∨
          f = (M.split a b hface hfst hadj).faceOf d1) := by
        intro h
        rcases h with h | h
        · exact hout h.symm
        · exact hback h.symm
      rw [hcard, ite_eq_right hite]
      decide

theorem sum_split_edges (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (g : (M.split a b hface hfst hadj).graph.edgeSet → ZMod 2) :
    ∑ e, g e = g (splitNewEdge M a b hface hfst hadj) +
      ∑ e, g (splitMapEdge M a b hface hfst hadj e) := by
  have h := Fintype.sum_equiv (splitEdgeEquiv M a b hface hfst hadj)
    (fun x => g (splitEdgeEquiv M a b hface hfst hadj x)) g
    (fun _ => rfl)
  have hopt : ∑ x : Option M.graph.edgeSet,
      g (splitEdgeEquiv M a b hface hfst hadj x) =
      g (splitNewEdge M a b hface hfst hadj) +
        ∑ e, g (splitMapEdge M a b hface hfst hadj e) := by
    rw [Fintype.sum_option]
    simp only [splitEdgeEquiv, Equiv.ofBijective_apply]
    rw [splitEdgeToFun_none]
    refine congrArg (fun t => g (splitNewEdge M a b hface hfst hadj) + t) ?_
    exact Finset.sum_congr rfl (fun e _ =>
      congrArg g (splitEdgeToFun_some M a b hface hfst hadj e))
  exact h.symm.trans hopt

theorem mem_splitNewEdge (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (v : Fin n) :
    v ∈ (splitNewEdge M a b hface hfst hadj).val ↔
      v = a.fst ∨ v = b.fst := by
  simp [splitNewEdge, Sym2.mem_iff]

theorem incident_sum_split (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (φ : (M.split a b hface hfst hadj).graph.edgeSet → ZMod 2) (v : Fin n) :
    incidentSum (M.split a b hface hfst hadj) φ v =
      incidentSum M (restrictSplit M a b hface hfst hadj φ) v +
        if v = a.fst ∨ v = b.fst then
          φ (splitNewEdge M a b hface hfst hadj) else 0 := by
  unfold incidentSum restrictSplit
  have hsum := sum_split_edges M a b hface hfst hadj
    (fun e => if v ∈ e.val then φ e else 0)
  have hnew : (if v ∈ (splitNewEdge M a b hface hfst hadj).val then
      φ (splitNewEdge M a b hface hfst hadj) else 0) =
      if v = a.fst ∨ v = b.fst then
        φ (splitNewEdge M a b hface hfst hadj) else 0 := by
    simp
  have hold : (∑ e, if v ∈ (splitMapEdge M a b hface hfst hadj e).val then
      φ (splitMapEdge M a b hface hfst hadj e) else 0) =
      ∑ e, if v ∈ e.val then
        φ (splitMapEdge M a b hface hfst hadj e) else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    rfl
  rw [hsum, hnew, hold]
  ac_rfl

theorem even_restrict_split (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (φ : (M.split a b hface hfst hadj).graph.edgeSet → ZMod 2)
    (hφ : IsEven (M.split a b hface hfst hadj) φ)
    (h0 : φ (splitNewEdge M a b hface hfst hadj) = 0) :
    IsEven M (restrictSplit M a b hface hfst hadj φ) := by
  intro v
  have hv := hφ v
  have h := incident_sum_split M a b hface hfst hadj φ v
  have hite : (if v = a.fst ∨ v = b.fst then
      φ (splitNewEdge M a b hface hfst hadj) else 0) = 0 := by
    split_ifs <;> simp [h0]
  rw [h, hite, add_zero] at hv
  exact hv

end PlaneMap

end SimpleGraph
