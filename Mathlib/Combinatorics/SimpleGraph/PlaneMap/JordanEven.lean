/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Jordan
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.JordanSplit
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.JordanFace
public import Mathlib.Data.Fintype.BigOperators

/-!
# Even combinations are face-boundary sums

Constructor induction: the vertex map has no edges; `grow` is
`even_boundary_grow`; `split` restricts after killing the new chord
by adding at most one new face boundary.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators
open PlaneMapConstruction

namespace PlaneMap

open Classical

variable {n : ℕ}

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

theorem splitFaceEquiv_label (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (d : (M.split a b hface hfst hadj).Dart) :
    splitFaceEquiv M.rotation a b hfst hadj hface
      ((M.split a b hface hfst hadj).faceOf d) =
      splitFaceLabel M.rotation a b hfst hadj d := by
  change (splitOrbitEquiv M.rotation a b hfst hadj hface
      ((PlaneMapConstruction.split M.rotation a b hfst hadj).faceQuotientEquiv
        (splitOut (G := M.graph) a.fst b.fst hfst)
        (Sum.inl (Quotient.mk _ d)))) =
    splitFaceLabel M.rotation a b hfst hadj d
  simp only [RotationSystem.faceQuotientEquiv]
  rfl

/-- Both halves of the split face receive the old face's coefficient. -/
noncomputable def liftSplitCoeffs (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (c0 : M.Face → ZMod 2) :
    (M.split a b hface hfst hadj).Face → ZMod 2 :=
  fun F =>
    match splitFaceEquiv M.rotation a b hfst hadj hface F with
    | .inl f => c0 f
    | .inr _ => c0 (M.faceOf a)

theorem lift_split_old (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (c0 : M.Face → ZMod 2) (d : M.Dart) :
    liftSplitCoeffs M a b hface hfst hadj c0
      ((M.split a b hface hfst hadj).faceOf
        (splitOld a.fst b.fst hfst d :
          (M.split a b hface hfst hadj).Dart)) = c0 (M.faceOf d) := by
  let d' : (M.split a b hface hfst hadj).Dart :=
    splitOld a.fst b.fst hfst d
  have hΦ := splitFaceEquiv_label M a b hface hfst hadj d'
  change (match splitFaceEquiv M.rotation a b hfst hadj hface
      ((M.split a b hface hfst hadj).faceOf d') with
    | Sum.inl f => c0 f
    | Sum.inr _ => c0 (M.faceOf a)) = c0 (M.faceOf d)
  rw [hΦ]
  change (match splitFaceLabel M.rotation a b hfst hadj
      (splitOld a.fst b.fst hfst d) with
    | Sum.inl f => c0 f
    | Sum.inr _ => c0 (M.faceOf a)) = c0 (M.faceOf d)
  rw [split_label_old]
  unfold splitOldLabel
  split_ifs with h
  · exact congrArg c0 h.1.symm
  · rfl

theorem lift_split_out (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (c0 : M.Face → ZMod 2) :
    liftSplitCoeffs M a b hface hfst hadj c0
      ((M.split a b hface hfst hadj).faceOf
        (splitOut (G := M.graph) a.fst b.fst hfst :
          (M.split a b hface hfst hadj).Dart)) =
      c0 (M.faceOf a) := by
  let d' : (M.split a b hface hfst hadj).Dart :=
    splitOut (G := M.graph) a.fst b.fst hfst
  have hΦ := splitFaceEquiv_label M a b hface hfst hadj d'
  change (match splitFaceEquiv M.rotation a b hfst hadj hface
      ((M.split a b hface hfst hadj).faceOf d') with
    | Sum.inl f => c0 f
    | Sum.inr _ => c0 (M.faceOf a)) = c0 (M.faceOf a)
  rw [hΦ]
  change (match splitFaceLabel M.rotation a b hfst hadj
      (splitOut (G := M.graph) a.fst b.fst hfst) with
    | Sum.inl f => c0 f
    | Sum.inr _ => c0 (M.faceOf a)) = c0 (M.faceOf a)
  rw [split_label_out]

theorem lift_split_back (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (c0 : M.Face → ZMod 2) :
    liftSplitCoeffs M a b hface hfst hadj c0
      ((M.split a b hface hfst hadj).faceOf
        (splitBack (G := M.graph) a.fst b.fst hfst :
          (M.split a b hface hfst hadj).Dart)) =
      c0 (M.faceOf a) := by
  let d' : (M.split a b hface hfst hadj).Dart :=
    splitBack (G := M.graph) a.fst b.fst hfst
  have hΦ := splitFaceEquiv_label M a b hface hfst hadj d'
  change (match splitFaceEquiv M.rotation a b hfst hadj hface
      ((M.split a b hface hfst hadj).faceOf d') with
    | Sum.inl f => c0 f
    | Sum.inr _ => c0 (M.faceOf a)) = c0 (M.faceOf a)
  rw [hΦ]
  change (match splitFaceLabel M.rotation a b hfst hadj
      (splitBack (G := M.graph) a.fst b.fst hfst) with
    | Sum.inl f => c0 f
    | Sum.inr _ => c0 (M.faceOf a)) = c0 (M.faceOf a)
  rw [split_label_back]

theorem split_old_map_edge (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (d : M.Dart) :
    RotationSystem.edgeOfDart (splitOld a.fst b.fst hfst d) =
      splitMapEdge M a b hface hfst hadj (RotationSystem.edgeOfDart d) := by
  apply Subtype.ext
  rfl

theorem split_map_is_old (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (e : M.graph.edgeSet)
    (d : (M.split a b hface hfst hadj).Dart)
    (h : RotationSystem.edgeOfDart d =
      splitMapEdge M a b hface hfst hadj e) :
    ∃ d0 : M.Dart, d = splitOld a.fst b.fst hfst d0 := by
  obtain ⟨x, rfl⟩ :=
    (splitDartEquiv (G := M.graph) a.fst b.fst hfst hadj).surjective d
  cases x with
  | inl d0 => exact ⟨d0, rfl⟩
  | inr bit =>
    have hnew : RotationSystem.edgeOfDart
        (splitDart (G := M.graph) a.fst b.fst hfst (.inr bit)) =
        splitNewEdge M a b hface hfst hadj := by
      cases bit with
      | false => exact split_out_edge M a b hface hfst hadj
      | true => exact split_back_edge M a b hface hfst hadj
    exact (splitMapEdge_ne_new M a b hface hfst hadj e
      (h.symm.trans hnew)).elim

theorem splitOld_injective (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) :
    Function.Injective (splitOld (G := M.graph) a.fst b.fst hfst) :=
  fun d e hde =>
    Sum.inl.inj (split_dart_injective a.fst b.fst hfst hadj hde)

theorem split_old_fiber_to (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) {e : M.graph.edgeSet} {d : M.Dart}
    (hd : RotationSystem.edgeOfDart d = e) :
    RotationSystem.edgeOfDart
        (splitOld a.fst b.fst hfst d :
          (M.split a b hface hfst hadj).Dart) =
      splitMapEdge M a b hface hfst hadj e := by
  change RotationSystem.edgeOfDart (splitOld a.fst b.fst hfst d) =
    splitMapEdge M a b hface hfst hadj e
  exact (split_old_map_edge M a b hface hfst hadj d).trans
    (congrArg (splitMapEdge M a b hface hfst hadj) hd)

theorem split_old_fiber_from (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) {e : M.graph.edgeSet}
    {d : (M.split a b hface hfst hadj).Dart}
    (h : RotationSystem.edgeOfDart d =
      splitMapEdge M a b hface hfst hadj e) :
    RotationSystem.edgeOfDart
        (Classical.choose (split_map_is_old M a b hface hfst hadj e d h)) =
      e := by
  set d0 := Classical.choose (split_map_is_old M a b hface hfst hadj e d h)
  have hd : d = splitOld a.fst b.fst hfst d0 :=
    Classical.choose_spec (split_map_is_old M a b hface hfst hadj e d h)
  have he := split_old_map_edge M a b hface hfst hadj d0
  have : splitMapEdge M a b hface hfst hadj
      (RotationSystem.edgeOfDart d0) =
      splitMapEdge M a b hface hfst hadj e := by
    rw [← he, ← hd]
    exact h
  exact splitMapEdge_injective M a b hface hfst hadj this

noncomputable def splitOldEdgeFiberEquiv (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst) (e : M.graph.edgeSet) :
    {d : M.Dart // RotationSystem.edgeOfDart d = e} ≃
      {d : (M.split a b hface hfst hadj).Dart //
        RotationSystem.edgeOfDart d =
          splitMapEdge M a b hface hfst hadj e} where
  toFun d :=
    ⟨(splitOld a.fst b.fst hfst d.val :
        (M.split a b hface hfst hadj).Dart),
      split_old_fiber_to M a b hface hfst hadj d.property⟩
  invFun d :=
    ⟨Classical.choose
        (split_map_is_old M a b hface hfst hadj e d.val d.property),
      split_old_fiber_from M a b hface hfst hadj d.property⟩
  left_inv d := by
    apply Subtype.ext
    have hprop := split_old_fiber_to M a b hface hfst hadj d.property
    have hd := Classical.choose_spec
      (split_map_is_old M a b hface hfst hadj e
        (splitOld a.fst b.fst hfst d.val :
          (M.split a b hface hfst hadj).Dart) hprop)
    exact splitOld_injective M a b hface hfst hadj (by
      apply Dart.ext
      exact congrArg Dart.toProd hd.symm)
  right_inv d := Subtype.ext
    (Classical.choose_spec
      (split_map_is_old M a b hface hfst hadj e d.val d.property)).symm

theorem faceSum_eq_dart_sum (M : PlaneMap n) (c : M.Face → ZMod 2)
    (e : M.graph.edgeSet) :
    _root_.SimpleGraph.PlaneMap.faceSum M c e =
      ∑ d : {d : M.Dart // RotationSystem.edgeOfDart d = e},
        c (M.faceOf d.val) := by
  classical
  let S (f : M.Face) :=
    {d : M.Dart // M.faceOf d = f ∧ RotationSystem.edgeOfDart d = e}
  let T := {d : M.Dart // RotationSystem.edgeOfDart d = e}
  let hσ : (Σ f : M.Face, S f) ≃ T :=
    { toFun := fun p => ⟨p.2.val, p.2.property.2⟩
      invFun := fun d => ⟨M.faceOf d.val, ⟨d.val, And.intro rfl d.property⟩⟩
      left_inv := fun p => by
        rcases p with ⟨f, d, hf, he⟩
        subst hf
        rfl
      right_inv := fun _ => Subtype.ext rfl }
  have hsum : (∑ f, c f * M.boundary f e) =
      ∑ f, ∑ _d : S f, c f := by
    apply Finset.sum_congr rfl
    intro f _
    have : ∑ _d : S f, c f = (Fintype.card (S f) : ZMod 2) * c f := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [boundary_eq, this, mul_comm]
  have hconst : (∑ f, ∑ d : S f, c f) =
      ∑ f, ∑ d : S f, c (M.faceOf d.val) := by
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro d _
    exact congrArg c d.property.1.symm
  have hsigma :
      (∑ f, ∑ d : S f, c (M.faceOf d.val)) =
        ∑ p : Σ f : M.Face, S f, c (M.faceOf p.2.val) :=
    (Fintype.sum_sigma (ι := M.Face) (α := S)
      (fun p => c (M.faceOf p.2.val))).symm
  change (∑ f, c f * M.boundary f e) = _
  exact (hsum.trans hconst).trans
    (hsigma.trans (Fintype.sum_equiv hσ
      (fun p => c (M.faceOf p.2.val))
      (fun d => c (M.faceOf d.val))
      (fun p => by dsimp [hσ])))

theorem even_boundary_split_zero (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (hM : ∀ φ : M.graph.edgeSet → ZMod 2, IsEven M φ →
      ∃ d : M.Face → ZMod 2, ∀ e,
        φ e = _root_.SimpleGraph.PlaneMap.faceSum M d e)
    (φ : (M.split a b hface hfst hadj).graph.edgeSet → ZMod 2)
    (hφ : IsEven (M.split a b hface hfst hadj) φ)
    (h0 : φ (splitNewEdge M a b hface hfst hadj) = 0) :
    ∃ d : (M.split a b hface hfst hadj).Face → ZMod 2,
      ∀ e, φ e = _root_.SimpleGraph.PlaneMap.faceSum
        (M.split a b hface hfst hadj) d e := by
  classical
  obtain ⟨c0, hc0⟩ := hM (restrictSplit M a b hface hfst hadj φ)
    (even_restrict_split M a b hface hfst hadj φ hφ h0)
  let c := liftSplitCoeffs M a b hface hfst hadj c0
  refine ⟨c, ?_⟩
  intro e
  rcases split_edge_dichotomy M a b hface hfst hadj e with he | ⟨e0, he⟩
  · rw [he, h0, eq_comm]
    let dOut : (M.split a b hface hfst hadj).Dart :=
      splitOut (G := M.graph) a.fst b.fst hfst
    let dBack : (M.split a b hface hfst hadj).Dart :=
      splitBack (G := M.graph) a.fst b.fst hfst
    let F0 := (M.split a b hface hfst hadj).faceOf dOut
    let F1 := (M.split a b hface hfst hadj).faceOf dBack
    have hF0 : c F0 = c0 (M.faceOf a) :=
      lift_split_out M a b hface hfst hadj c0
    have hF1 : c F1 = c0 (M.faceOf a) :=
      lift_split_back M a b hface hfst hadj c0
    have hne := split_out_ne_back_face M a b hface hfst hadj
    change ∑ F, c F * (M.split a b hface hfst hadj).boundary F
        (splitNewEdge M a b hface hfst hadj) = 0
    have hterm (F : (M.split a b hface hfst hadj).Face) :
        c F * (M.split a b hface hfst hadj).boundary F
          (splitNewEdge M a b hface hfst hadj) =
        if F = F0 ∨ F = F1 then c0 (M.faceOf a) else 0 := by
      have hb := boundary_split_new M a b hface hfst hadj F
      by_cases hF : F = F0 ∨ F = F1
      · rw [ite_eq_left hF]
        have hb1 : (M.split a b hface hfst hadj).boundary F
            (splitNewEdge M a b hface hfst hadj) = 1 := by
          rw [hb]
          refine ite_eq_left ?_
          simpa [F0, F1] using hF
        rw [hb1, mul_one]
        rcases hF with hF | hF
        · rw [hF, hF0]
        · rw [hF, hF1]
      · rw [ite_eq_right hF]
        have hb0 : (M.split a b hface hfst hadj).boundary F
            (splitNewEdge M a b hface hfst hadj) = 0 := by
          rw [hb]
          refine ite_eq_right ?_
          simpa [F0, F1] using hF
        rw [hb0, mul_zero]
    refine (Finset.sum_congr rfl (fun F _ => hterm F)).trans ?_
    have hsum :
        (∑ F, if F = F0 ∨ F = F1 then c0 (M.faceOf a) else 0) =
          c0 (M.faceOf a) + c0 (M.faceOf a) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.univ.filter
          (fun F => F = F0 ∨ F = F1)).card = 2 := by
        have : Finset.univ.filter (fun F => F = F0 ∨ F = F1) =
            {F0, F1} := by
          ext F; simp [F0, F1]
        have hmem : F0 ∉ ({F1} : Finset _) := by
          simpa [F0, F1, dOut, dBack] using hne
        rw [this, Finset.card_insert_of_notMem hmem, Finset.card_singleton]
      simp [hcard, two_mul]
    rw [hsum, zmod2_add_self]
  · rw [he]
    have hφe : φ (splitMapEdge M a b hface hfst hadj e0) =
        _root_.SimpleGraph.PlaneMap.faceSum M c0 e0 := hc0 e0
    rw [hφe, faceSum_eq_dart_sum, faceSum_eq_dart_sum]
    exact (Fintype.sum_equiv
      (splitOldEdgeFiberEquiv M a b hface hfst hadj e0)
      (fun d0 => c0 (M.faceOf d0.val))
      (fun d => c ((M.split a b hface hfst hadj).faceOf d.val))
      (fun d0 => by
        change c0 (M.faceOf d0.val) =
          liftSplitCoeffs M a b hface hfst hadj c0
            ((M.split a b hface hfst hadj).faceOf
              (splitOld a.fst b.fst hfst d0.val :
                (M.split a b hface hfst hadj).Dart))
        exact (lift_split_old M a b hface hfst hadj c0 d0.val).symm))

theorem even_boundary_split (M : PlaneMap n) (a b : M.Dart)
    (hface : M.faceOf a = M.faceOf b) (hfst : a.fst ≠ b.fst)
    (hadj : ¬ M.Adj a.fst b.fst)
    (hM : ∀ φ : M.graph.edgeSet → ZMod 2, IsEven M φ →
      ∃ d : M.Face → ZMod 2, ∀ e,
        φ e = _root_.SimpleGraph.PlaneMap.faceSum M d e)
    (φ : (M.split a b hface hfst hadj).graph.edgeSet → ZMod 2)
    (hφ : IsEven (M.split a b hface hfst hadj) φ) :
    ∃ d : (M.split a b hface hfst hadj).Face → ZMod 2,
      ∀ e, φ e = _root_.SimpleGraph.PlaneMap.faceSum
        (M.split a b hface hfst hadj) d e := by
  classical
  by_cases h0 : φ (splitNewEdge M a b hface hfst hadj) = 0
  · exact even_boundary_split_zero M a b hface hfst hadj hM φ hφ h0
  · have h1 : φ (splitNewEdge M a b hface hfst hadj) = 1 := by
      generalize hx : φ (splitNewEdge M a b hface hfst hadj) = x
      revert h0
      rw [hx]
      intro h0
      fin_cases x
      · exact (h0 rfl).elim
      · rfl
    let Fnew := (M.split a b hface hfst hadj).faceOf
      (splitOut (G := M.graph) a.fst b.fst hfst)
    let ψ : (M.split a b hface hfst hadj).graph.edgeSet → ZMod 2 :=
      fun e => φ e + (M.split a b hface hfst hadj).boundary Fnew e
    have hψeven : IsEven (M.split a b hface hfst hadj) ψ :=
      even_add_face (M.split a b hface hfst hadj) φ hφ Fnew
    have hψ0 : ψ (splitNewEdge M a b hface hfst hadj) = 0 := by
      change φ (splitNewEdge M a b hface hfst hadj) +
          (M.split a b hface hfst hadj).boundary Fnew
            (splitNewEdge M a b hface hfst hadj) = 0
      have hb := boundary_split_new M a b hface hfst hadj Fnew
      have hite : Fnew = (M.split a b hface hfst hadj).faceOf
          (splitOut (G := M.graph) a.fst b.fst hfst) ∨
        Fnew = (M.split a b hface hfst hadj).faceOf
          (splitBack (G := M.graph) a.fst b.fst hfst) := Or.inl rfl
      rw [h1, hb, ite_eq_left hite]
      decide
    obtain ⟨c, hc⟩ :=
      even_boundary_split_zero M a b hface hfst hadj hM ψ hψeven hψ0
    refine ⟨fun F => c F + if F = Fnew then 1 else 0, ?_⟩
    intro e
    have hφe : φ e = ψ e +
        (M.split a b hface hfst hadj).boundary Fnew e := by
      change φ e = (φ e +
          (M.split a b hface hfst hadj).boundary Fnew e) +
        (M.split a b hface hfst hadj).boundary Fnew e
      rw [add_assoc, zmod2_add_self, add_zero]
    rw [hφe, hc e]
    change ∑ F, c F * (M.split a b hface hfst hadj).boundary F e +
        (M.split a b hface hfst hadj).boundary Fnew e =
      ∑ F, (c F + if F = Fnew then 1 else 0) *
        (M.split a b hface hfst hadj).boundary F e
    refine Eq.symm ?_
    have hterm : ∀ F,
        (c F + if F = Fnew then 1 else 0) *
          (M.split a b hface hfst hadj).boundary F e =
        c F * (M.split a b hface hfst hadj).boundary F e +
          if F = Fnew then (M.split a b hface hfst hadj).boundary F e
          else 0 := by
      intro F
      by_cases hF : F = Fnew
      · rw [hF]
        simp [add_mul]
      · simp [hF]
    refine (Finset.sum_congr rfl (fun F _ => hterm F)).trans ?_
    rw [Finset.sum_add_distrib]
    have hsingle :
        (∑ F, if F = Fnew then
          (M.split a b hface hfst hadj).boundary F e else 0) =
        (M.split a b hface hfst hadj).boundary Fnew e := by
      simp [Finset.sum_ite_eq']
    rw [hsingle]

/-- Every even edge combination on a generated plane map is a sum of
face boundaries. -/
public theorem even_is_face_sum {n : ℕ} (M : PlaneMap n)
    (φ : M.graph.edgeSet → ZMod 2) (hφ : IsEven M φ) :
    ∃ c : M.Face → ZMod 2, ∀ e,
      φ e = _root_.SimpleGraph.PlaneMap.faceSum M c e := by
  rcases M with ⟨D, h⟩
  induction h with
  | vertex => exact even_boundary_vertex φ
  | @grow n D h u c ih =>
    exact even_boundary_grow (PlaneMap.mk D h) u c ih φ hφ
  | @split n D h a b hface hfst hadj ih =>
    exact even_boundary_split (PlaneMap.mk D h) a b hface hfst hadj ih φ hφ

end PlaneMap

end SimpleGraph
