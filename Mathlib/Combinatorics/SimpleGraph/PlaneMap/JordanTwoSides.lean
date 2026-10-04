module
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.JordanCycle
/-!
# Face-sum sides of a cycle cut
A `CycleCut` may be disconnected, so no global reachability partition is claimed.
The face-sum coefficients nevertheless separate adjacent off-cycle vertices.
-/

@[expose] public section
namespace SimpleGraph.PlaneMap
variable {n : ℕ}
noncomputable def sideCoeff (M : PlaneMap n) (C : CycleCut M) :
    M.Face → ZMod 2 :=
  Classical.choose (cycleEdgeCoeff_is_face_sum M C)

theorem sideCoeff_spec (M : PlaneMap n) (C : CycleCut M) (e) :
    cycleEdgeCoeff M C e = faceSum M (sideCoeff M C) e :=
  Classical.choose_spec (cycleEdgeCoeff_is_face_sum M C) e
def OnLeftSum {M : PlaneMap n} (C : CycleCut M) (x : Fin n) : Prop :=
  x ∉ C.verts ∧ ∃ d : M.Dart,
    d.fst = x ∧ sideCoeff M C (M.faceOf d) = 1

def OnRightSum {M : PlaneMap n} (C : CycleCut M) (x : Fin n) : Prop :=
  x ∉ C.verts ∧ (∃ d : M.Dart, d.fst = x) ∧
    ∀ d : M.Dart, d.fst = x → sideCoeff M C (M.faceOf d) = 0
private theorem coeff_zero_of_fst {M : PlaneMap n} (C : CycleCut M)
    (d : M.Dart) (h : d.fst ∉ C.verts) :
    cycleEdgeCoeff M C (RotationSystem.edgeOfDart d) = 0 := by
  apply (cycleEdgeCoeff_eq_zero_iff M C _).2
  intro hex
  exact h (cycleEdgeCoeff_closed M C _ ((cycleEdgeCoeff_eq_one_iff M C _).2 hex)
    d.fst ((mem_edgeOfDart_iff d d.fst).2 (Or.inl rfl)))
private theorem sideCoeff_eq_of_fst {M : PlaneMap n} (C : CycleCut M)
    {x : Fin n} (hx : x ∉ C.verts) (d e : M.Dart)
    (hd : d.fst = x) (he : e.fst = x) :
    sideCoeff M C (M.faceOf d) = sideCoeff M C (M.faceOf e) := by
  have step (a : M.Dart) (ha : a.fst = x) :
      sideCoeff M C (M.faceOf a) =
        sideCoeff M C (M.faceOf (M.rotation.next a)) := by
    calc
      _ = sideCoeff M C (M.faceOf a.symm) :=
        face_coeff_eq_of_cycleEdgeCoeff_zero M C _ (sideCoeff_spec M C) a
          (coeff_zero_of_fst C a (ha ▸ hx))
      _ = _ := by simpa using (congrArg (sideCoeff M C)
        ((M.rotation.face_of_face_next a.symm).symm))
  obtain ⟨k, hk⟩ := M.rotation.cyclic d e (hd.trans he.symm)
  have hi : ∀ k, (((M.rotation.next : M.Dart → M.Dart)^[k]) d).fst = x ∧
      sideCoeff M C (M.faceOf d) =
        sideCoeff M C (M.faceOf (((M.rotation.next : M.Dart → M.Dart)^[k]) d)) := by
    intro k
    induction k with
    | zero => simp [hd]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨(M.rotation.next_fst _).trans ih.1, ih.2.trans (step _ ih.1)⟩
  simpa [hk] using (hi k).2
theorem not_both_sum_sides {M : PlaneMap n} (C : CycleCut M) (x : Fin n) :
    ¬ (OnLeftSum C x ∧ OnRightSum C x) := by
  rintro ⟨⟨_, d, hd, h1⟩, _, _, h0⟩
  have := h0 d hd
  exact one_ne_zero (h1.symm.trans this)
private theorem adjacent_stays_on_sum_side {M : PlaneMap n} (C : CycleCut M)
    {x y : Fin n} (hxy : M.Adj x y) (hx : x ∉ C.verts) (hy : y ∉ C.verts) :
    (OnLeftSum C x → OnLeftSum C y) ∧
      (OnRightSum C x → OnRightSum C y) := by
  let d : M.Dart := ⟨(x, y), hxy⟩
  have hedge := face_coeff_eq_of_cycleEdgeCoeff_zero M C _ (sideCoeff_spec M C)
    d (coeff_zero_of_fst C d hx)
  constructor
  · rintro ⟨_, a, ha, h1⟩
    exact ⟨hy, d.symm, rfl, hedge.symm.trans
      ((sideCoeff_eq_of_fst C hx d a rfl ha).trans h1)⟩
  · rintro ⟨_, ⟨a, ha⟩, h0⟩
    refine ⟨hy, ⟨d.symm, rfl⟩, fun b hb => ?_⟩
    exact (sideCoeff_eq_of_fst C hy b d.symm hb rfl).trans
      (hedge.symm.trans (h0 d rfl))
theorem no_cross_edge_sum_sides {M : PlaneMap n} (C : CycleCut M) :
    ∀ x y, ¬ (OnLeftSum C x ∧ OnRightSum C y ∧ M.Adj x y) := by
  rintro x y ⟨hl, hr, hxy⟩
  exact not_both_sum_sides C y
    ⟨(adjacent_stays_on_sum_side C hxy hl.1 hr.1).1 hl, hr⟩
theorem walk_stays_on_sum_side {M : PlaneMap n} (C : CycleCut M)
    {x y : Fin n} (q : M.graph.Walk x y) (hq : AvoidsVerts q C.verts) :
    (OnLeftSum C x → OnLeftSum C y) ∧
      (OnRightSum C x → OnRightSum C y) := by
  induction q with
  | nil => exact ⟨id, id⟩
  | @cons u v w h p ih =>
    have hu := hq u (Walk.start_mem_support _)
    have hp : AvoidsVerts p C.verts := fun z hz =>
      hq z (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    exact ⟨(ih hp).1 ∘ (adjacent_stays_on_sum_side C h hu
      (hp v (Walk.start_mem_support p))).1,
      (ih hp).2 ∘ (adjacent_stays_on_sum_side C h hu
        (hp v (Walk.start_mem_support p))).2⟩
end SimpleGraph.PlaneMap
