/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationSystem

/-!
# Rotation-system surgery

Attaching a new leaf preserves connectedness and the face count, adds one edge,
and makes that edge a bridge. The isolated-corner case has one face of length two.
Inserting a missing edge at two different vertices of one face preserves
connectedness and adds one edge and one face. Explicit orbit correspondences
prove both face-count statements.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace PlaneMapConstruction

/-- Attach the new last vertex to `u`, retaining all old edges under `Fin.castSucc`. -/
def growGraph {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    SimpleGraph (Fin (n + 1)) where
  Adj x y :=
    (∃ v w, G.Adj v w ∧ v.castSucc = x ∧ w.castSucc = y) ∨
      (x = u.castSucc ∧ y = Fin.last n) ∨ (x = Fin.last n ∧ y = u.castSucc)
  symm := by
    refine ⟨?_⟩
    intro x y h
    rcases h with ⟨v, w, h, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨w, v, h.symm, rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  loopless := by
    refine ⟨?_⟩
    intro x h
    rcases h with ⟨v, w, h, hv, hw⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact h.ne (Fin.castSucc_injective n (hv.trans hw.symm))
    · exact Fin.castSucc_ne_last u (hx.symm.trans hy)
    · exact Fin.castSucc_ne_last u (hy.symm.trans hx)

variable {n : ℕ} {H : SimpleGraph (Fin n)} (u : Fin n)

@[simp]
theorem grow_graph_adj_cast (v w : Fin n) :
    (growGraph H u).Adj v.castSucc w.castSucc ↔ H.Adj v w := by
  simp [growGraph]

@[simp]
theorem grow_graph_adj_last (v : Fin n) :
    (growGraph H u).Adj v.castSucc (Fin.last n) ↔ v = u := by
  simp [growGraph]

/-- The old graph embeds in its one-leaf extension. -/
def growEmbedding : H ↪g growGraph H u where
  toFun := Fin.castSucc
  inj' := Fin.castSucc_injective n
  map_rel_iff' := grow_graph_adj_cast u _ _

/-- Transport an old dart into the one-leaf extension. -/
def growOld (d : H.Dart) : (growGraph H u).Dart :=
  ⟨(d.fst.castSucc, d.snd.castSucc), (grow_graph_adj_cast u _ _).2 d.adj⟩

/-- The new dart directed towards the leaf. -/
def growOut : (growGraph H u).Dart :=
  ⟨(u.castSucc, Fin.last n), (grow_graph_adj_last u u).2 rfl⟩

/-- The new dart directed away from the leaf. -/
def growBack : (growGraph H u).Dart := (growOut (H := H) u).symm

/-- Enumerate the old darts and the two new darts in the leaf extension. -/
def growDart (d : H.Dart ⊕ Bool) : (growGraph H u).Dart :=
  match d with
  | .inl d => growOld u d
  | .inr false => growOut u
  | .inr true => growBack u

theorem grow_dart_injective : Function.Injective (growDart (H := H) u) := by
  intro x y h
  have hf := congrArg (fun d : (growGraph H u).Dart => d.fst) h
  have hs := congrArg (fun d : (growGraph H u).Dart => d.snd) h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      congr 1
      apply Dart.ext
      exact Prod.ext (Fin.castSucc_injective n hf) (Fin.castSucc_injective n hs)
    | inr y => cases y <;> simp [growDart, growOld, growOut, growBack, eq_comm] at hf hs
  | inr x =>
    cases y with
    | inl y => cases x <;> simp [growDart, growOld, growOut, growBack, eq_comm] at hf hs
    | inr y =>
      cases x <;> cases y <;> simp_all [growDart, growOut, growBack]

theorem grow_dart_surjective : Function.Surjective (growDart (H := H) u) := by
  intro d
  rcases d.adj with ⟨v, w, h, hv, hw⟩ | ⟨hv, hw⟩ | ⟨hv, hw⟩
  · refine ⟨.inl ⟨(v, w), h⟩, Dart.ext _ _ ?_⟩
    exact Prod.ext hv hw
  · refine ⟨.inr false, Dart.ext _ _ ?_⟩
    exact Prod.ext hv.symm hw.symm
  · refine ⟨.inr true, Dart.ext _ _ ?_⟩
    exact Prod.ext hv.symm hw.symm

/-- The dart correspondence for adding one leaf. -/
noncomputable def growDartEquiv : H.Dart ⊕ Bool ≃ (growGraph H u).Dart :=
  Equiv.ofBijective (growDart u) ⟨grow_dart_injective u, grow_dart_surjective u⟩

@[simp]
theorem grow_dart_equiv_apply (d : H.Dart ⊕ Bool) : growDartEquiv u d = growDart u d := rfl

theorem grow_graph_connected (h : H.Connected) : (growGraph H u).Connected := by
  apply (connected_iff_exists_forall_reachable _).2
  refine ⟨u.castSucc, ?_⟩
  intro v
  refine Fin.lastCases ?_ (fun w => ?_) v
  · exact ((grow_graph_adj_last u u).2 rfl).reachable
  · exact (h.preconnected u w).map (growEmbedding u).toHom

theorem grow_card_darts [DecidableRel H.Adj] [DecidableRel (growGraph H u).Adj] :
    Fintype.card (growGraph H u).Dart = Fintype.card H.Dart + 2 := by
  simpa using (Fintype.card_congr (growDartEquiv (H := H) u)).symm

theorem grow_card_edges [DecidableRel H.Adj] [DecidableRel (growGraph H u).Adj] :
    (growGraph H u).edgeFinset.card = H.edgeFinset.card + 1 := by
  have h := grow_card_darts (H := H) u
  rw [card_dart_eq_twice_card_edges, card_dart_eq_twice_card_edges] at h
  omega

/-- A finite forward path in a successor function. -/
def Reaches {α : Type*} (σ : α → α) (x y : α) : Prop := ∃ k : ℕ, σ^[k] x = y

namespace Reaches

variable {α : Type*} {σ : α → α} {x y z : α}

theorem refl (x : α) : Reaches σ x x := ⟨0, rfl⟩

theorem step (x : α) : Reaches σ x (σ x) := ⟨1, rfl⟩

theorem trans (h : Reaches σ x y) (h' : Reaches σ y z) : Reaches σ x z := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := h'
  exact ⟨l + k, by rw [Function.iterate_add_apply, hk, hl]⟩

theorem lift {β : Type*} {τ : β → β} (f : α → β)
    (hf : ∀ x, Reaches τ (f x) (f (σ x))) (h : Reaches σ x y) :
    Reaches τ (f x) (f y) := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => exact refl _
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (hf _)

end Reaches

variable (R : RotationSystem H) (a : H.Dart)

/-- Insert a new outgoing dart immediately before `a`, fixing the leaf's outgoing dart. -/
noncomputable def growBeforeNext : Equiv.Perm (H.Dart ⊕ Bool) := by
  classical
  exact (Equiv.sumCongr R.next (Equiv.refl Bool)).trans
    (Equiv.swap (.inl a) (.inr false))

@[simp]
theorem grow_before_next_old (d : H.Dart) :
    growBeforeNext R a (.inl d) =
      if R.next d = a then .inr false else .inl (R.next d) := by
  classical
  by_cases h : R.next d = a <;> simp [growBeforeNext, h, Equiv.swap_apply_def]

@[simp]
theorem grow_before_next_out : growBeforeNext R a (.inr false) = .inl a := by
  simp [growBeforeNext]

@[simp]
theorem grow_before_next_back : growBeforeNext R a (.inr true) = .inr true := by
  simp [growBeforeNext, Equiv.swap_apply_def]

theorem grow_before_reaches_old (d e : H.Dart) (h : Reaches R.next d e) :
    Reaches (growBeforeNext R a) (.inl d) (.inl e) := by
  classical
  apply Reaches.lift Sum.inl _ h
  intro x
  by_cases hx : R.next x = a
  · refine ⟨2, ?_⟩
    simp [Function.iterate_succ_apply, hx]
  · refine ⟨1, ?_⟩
    simp [hx]

/-- The rotation obtained by attaching a leaf before an existing outgoing dart. -/
noncomputable def growBefore (ha : a.fst = u) : RotationSystem (growGraph H u) where
  next := (growDartEquiv u).symm.trans ((growBeforeNext R a).trans (growDartEquiv u))
  next_fst := by
    classical
    intro d
    obtain ⟨x, rfl⟩ := (growDartEquiv (H := H) u).surjective d
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    change (growDartEquiv u (growBeforeNext R a x)).fst = (growDartEquiv u x).fst
    cases x with
    | inl x =>
      by_cases hx : R.next x = a
      · have hu : u = x.fst := ha.symm.trans ((congrArg (fun d : H.Dart => d.fst)
          hx).symm.trans (R.next_fst x))
        simp [grow_dart_equiv_apply, growDart, growOld, growOut, hx, hu]
      · simp [grow_dart_equiv_apply, growDart, growOld, hx, R.next_fst]
    | inr x => cases x <;>
        simp [grow_dart_equiv_apply, growDart, growOld, growOut, growBack, ha]
  cyclic := by
    classical
    intro d e h
    obtain ⟨x, rfl⟩ := (growDartEquiv (H := H) u).surjective d
    obtain ⟨y, rfl⟩ := (growDartEquiv (H := H) u).surjective e
    have transport (hxy : Reaches (growBeforeNext R a) x y) :
        ∃ k, (⇑((growDartEquiv u).symm.trans
          ((growBeforeNext R a).trans (growDartEquiv u))))^[k]
            (growDartEquiv u x) = growDartEquiv u y := by
      apply Reaches.lift (growDartEquiv u) _ hxy
      intro z
      exact ⟨1, by simp only [Function.iterate_one, Equiv.trans_apply,
        Equiv.symm_apply_apply]⟩
    apply transport
    have ha' : (R.next.symm a).fst = u := by
      have h := R.next_fst (R.next.symm a)
      simpa [ha] using h.symm
    have toOut : Reaches (growBeforeNext R a) (.inl (R.next.symm a)) (.inr false) :=
      ⟨1, by simp⟩
    have fromOut : Reaches (growBeforeNext R a) (.inr false) (.inl a) := ⟨1, by simp⟩
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply grow_before_reaches_old R a x y
        apply R.cyclic
        exact Fin.castSucc_injective n h
      | inr y =>
        cases y with
        | false =>
          have hx : x.fst = u := Fin.castSucc_injective n h
          exact (grow_before_reaches_old R a x (R.next.symm a)
            (R.cyclic _ _ (hx.trans ha'.symm))).trans toOut
        | true => exact (Fin.castSucc_ne_last x.fst h).elim
    | inr x =>
      cases y with
      | inl y =>
        cases x with
        | false =>
          have hy : u = y.fst := Fin.castSucc_injective n h
          exact fromOut.trans (grow_before_reaches_old R a a y (R.cyclic _ _ (ha.trans hy)))
        | true => exact (Fin.castSucc_ne_last y.fst h.symm).elim
      | inr y =>
        cases x <;> cases y
        · exact Reaches.refl _
        · exact (Fin.castSucc_ne_last u h).elim
        · exact (Fin.castSucc_ne_last u h.symm).elim
        · exact Reaches.refl _

@[simp]
theorem grow_before_next_apply (ha : a.fst = u) (x : H.Dart ⊕ Bool) :
    (growBefore u R a ha).next (growDartEquiv u x) =
      growDartEquiv u (growBeforeNext R a x) := by
  simp only [growBefore, Equiv.trans_apply, Equiv.symm_apply_apply]

@[simp]
theorem grow_old_symm (d : H.Dart) : (growOld u d).symm = growOld u d.symm := by
  apply Dart.ext
  rfl

@[simp]
theorem grow_before_face_old (ha : a.fst = u) (d : H.Dart) :
    (growBefore u R a ha).faceNext (growOld u d) =
      if R.faceNext d = a then growOut u else growOld u (R.faceNext d) := by
  classical
  change (growBefore u R a ha).next (growOld u d).symm = _
  rw [grow_old_symm]
  change (growBefore u R a ha).next (growDartEquiv u (.inl d.symm)) = _
  rw [grow_before_next_apply, grow_before_next_old]
  split <;> simp_all [RotationSystem.face_next_apply, growDart]

@[simp]
theorem grow_before_face_out (ha : a.fst = u) :
    (growBefore u R a ha).faceNext (growOut u) = growBack u := by
  change (growBefore u R a ha).next (growDartEquiv u (.inr true)) = _
  rw [grow_before_next_apply, grow_before_next_back]
  rfl

@[simp]
theorem grow_before_face_back (ha : a.fst = u) :
    (growBefore u R a ha).faceNext (growBack u) = growOld u a := by
  change (growBefore u R a ha).next (growOut u).symm.symm = _
  rw [Dart.symm_symm]
  change (growBefore u R a ha).next (growDartEquiv u (.inr false)) = _
  rw [grow_before_next_apply, grow_before_next_out]
  rfl

variable (ha : a.fst = u)

theorem grow_old_relation {d e : H.Dart} (h : R.FaceRelation d e) :
    (growBefore u R a ha).FaceRelation (growOld u d) (growOld u e) := by
  classical
  apply RotationSystem.FaceRelation.map (growOld u) _ h
  intro x
  have h₁ := RotationSystem.FaceRelation.step (R := growBefore u R a ha) (growOld u x)
  have h₂ := RotationSystem.FaceRelation.step (R := growBefore u R a ha) (growOut u)
  have h₃ := RotationSystem.FaceRelation.step (R := growBefore u R a ha) (growBack u)
  rw [grow_before_face_old] at h₁
  rw [grow_before_face_out] at h₂
  rw [grow_before_face_back] at h₃
  split_ifs at h₁ with hx
  · rw [hx]
    exact .trans h₁ (.trans h₂ h₃)
  · exact h₁

/-- Collapse the two new boundary darts to the old dart before which they were inserted. -/
noncomputable def growForget (d : (growGraph H u).Dart) : H.Dart :=
  Sum.elim id (fun _ => a) ((growDartEquiv u).symm d)

@[simp]
theorem grow_forget_old (d : H.Dart) : growForget u a (growOld u d) = d := by
  change Sum.elim id (fun _ => a) ((growDartEquiv u).symm (growDartEquiv u (.inl d))) = d
  rw [Equiv.symm_apply_apply]
  rfl

@[simp]
theorem grow_forget_out : growForget u a (growOut u) = a := by
  change Sum.elim id (fun _ => a) ((growDartEquiv u).symm (growDartEquiv u (.inr false))) = a
  rw [Equiv.symm_apply_apply]
  rfl

@[simp]
theorem grow_forget_back : growForget u a (growBack u) = a := by
  change Sum.elim id (fun _ => a) ((growDartEquiv u).symm (growDartEquiv u (.inr true))) = a
  rw [Equiv.symm_apply_apply]
  rfl

theorem grow_forget_relation {d e : (growGraph H u).Dart}
    (h : (growBefore u R a ha).FaceRelation d e) :
    R.FaceRelation (growForget u a d) (growForget u a e) := by
  classical
  apply RotationSystem.FaceRelation.map (growForget u a) _ h
  intro x
  obtain ⟨x, rfl⟩ := (growDartEquiv (H := H) u).surjective x
  cases x with
  | inl d =>
    change R.FaceRelation (growForget u a (growOld u d))
      (growForget u a ((growBefore u R a ha).faceNext (growOld u d)))
    rw [grow_before_face_old, grow_forget_old]
    split_ifs with hd
    · rw [grow_forget_out, ← hd]
      exact .step d
    · rw [grow_forget_old]
      exact .step d
  | inr b =>
    cases b
    · change R.FaceRelation (growForget u a (growOut u))
        (growForget u a ((growBefore u R a ha).faceNext (growOut u)))
      rw [grow_before_face_out, grow_forget_out, grow_forget_back]
      exact .refl a
    · change R.FaceRelation (growForget u a (growBack u))
        (growForget u a ((growBefore u R a ha).faceNext (growBack u)))
      rw [grow_before_face_back, grow_forget_back, grow_forget_old]
      exact .refl a

theorem grow_relation_forget (d : (growGraph H u).Dart) :
    (growBefore u R a ha).FaceRelation d (growOld u (growForget u a d)) := by
  obtain ⟨x, rfl⟩ := (growDartEquiv (H := H) u).surjective d
  cases x with
  | inl x =>
    change (growBefore u R a ha).FaceRelation (growOld u x)
      (growOld u (growForget u a (growOld u x)))
    rw [grow_forget_old]
    exact .refl _
  | inr x =>
    have h₁ := RotationSystem.FaceRelation.step (R := growBefore u R a ha) (growOut u)
    have h₂ := RotationSystem.FaceRelation.step (R := growBefore u R a ha) (growBack u)
    rw [grow_before_face_out] at h₁
    rw [grow_before_face_back] at h₂
    cases x
    · change (growBefore u R a ha).FaceRelation (growOut u)
        (growOld u (growForget u a (growOut u)))
      rw [grow_forget_out]
      exact .trans h₁ h₂
    · change (growBefore u R a ha).FaceRelation (growBack u)
        (growOld u (growForget u a (growBack u)))
      rw [grow_forget_back]
      exact h₂

/-- Adding a leaf at a nonempty corner gives a bijection on face orbits. -/
noncomputable def growBeforeOrbitEquiv :
    Quotient R.faceSetoid ≃ Quotient (growBefore u R a ha).faceSetoid where
  toFun := Quotient.map (growOld u) (fun _ _ => grow_old_relation u R a ha)
  invFun := Quotient.map (growForget u a) (fun _ _ => grow_forget_relation u R a ha)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ d => exact congrArg (Quotient.mk R.faceSetoid) (grow_forget_old u a d)
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ d => exact Quotient.sound (.symm (grow_relation_forget u R a ha d))

/-- The face correspondence for insertion at a nonempty corner. -/
noncomputable def growBeforeFaceEquiv : R.Face ≃ (growBefore u R a ha).Face :=
  (R.faceQuotientEquiv a).trans ((growBeforeOrbitEquiv u R a ha).trans
    ((growBefore u R a ha).faceQuotientEquiv (growOut u)).symm)

theorem grow_before_face_count [DecidableRel H.Adj] [DecidableRel (growGraph H u).Adj] :
    (growBefore u R a ha).faceCount = R.faceCount :=
  (Fintype.card_congr (growBeforeFaceEquiv u R a ha)).symm

/-- The new edge in a leaf extension is a bridge. -/
theorem grow_new_edge_bridge : (growGraph H u).IsBridge s(u.castSucc, Fin.last n) := by
  apply isBridge_iff.2
  intro h
  obtain ⟨v, hv⟩ := h.nonempty_neighborSet_right (Fin.castSucc_ne_last u)
  rw [mem_neighborSet, deleteEdges_adj] at hv
  have hvu : v = u.castSucc := by
    rcases hv.1 with ⟨x, y, hxy, hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact (Fin.castSucc_ne_last x hx).elim
    · exact (Fin.castSucc_ne_last u hx.symm).elim
    · exact hy
  subst v
  exact hv.2 (by simp [Sym2.eq_swap])

/-- At a connected isolated corner the two new outgoing rotations are singletons. -/
noncomputable def growIsolated (hconn : H.Connected) (hiso : ∀ w, ¬ H.Adj u w) :
    RotationSystem (growGraph H u) where
  next := Equiv.refl _
  next_fst _ := rfl
  cyclic := by
    let : IsEmpty H.Dart := RotationSystem.is_empty_dart_of_isolated hconn hiso
    intro d e h
    refine ⟨0, ?_⟩
    change d = e
    obtain ⟨x, rfl⟩ := (growDartEquiv (H := H) u).surjective d
    obtain ⟨y, rfl⟩ := (growDartEquiv (H := H) u).surjective e
    cases x with
    | inl x => exact isEmptyElim x
    | inr x =>
      cases y with
      | inl y => exact isEmptyElim y
      | inr y =>
        cases x <;> cases y
        · rfl
        · exact (Fin.castSucc_ne_last u h).elim
        · exact (Fin.castSucc_ne_last u h.symm).elim
        · rfl

variable (hconn : H.Connected) (hiso : ∀ w, ¬ H.Adj u w)

@[simp]
theorem grow_isolated_face_out :
    (growIsolated u hconn hiso).faceNext (growOut u) = growBack u := rfl

@[simp]
theorem grow_isolated_face_back :
    (growIsolated u hconn hiso).faceNext (growBack u) = growOut u :=
  Dart.symm_symm _

theorem grow_isolated_face_eq (f : (growIsolated u hconn hiso).Face) :
    f = (growIsolated u hconn hiso).faceOf (growOut u) := by
  let : IsEmpty H.Dart := RotationSystem.is_empty_dart_of_isolated hconn hiso
  cases f with
  | inl q =>
    induction q using Quotient.inductionOn with
    | _ d =>
      apply ((growIsolated u hconn hiso).face_of_eq_iff _ _).2
      obtain ⟨x, rfl⟩ := (growDartEquiv (H := H) u).surjective d
      cases x with
      | inl x => exact isEmptyElim x
      | inr x =>
        cases x
        · exact .refl _
        · exact .step _
  | inr h => exact (h.property.false (growOut u)).elim

theorem grow_isolated_face_count [DecidableRel (growGraph H u).Adj] :
    (growIsolated u hconn hiso).faceCount = 1 := by
  let : Unique (growIsolated u hconn hiso).Face := {
    default := (growIsolated u hconn hiso).faceOf (growOut u)
    uniq := grow_isolated_face_eq u hconn hiso }
  exact Fintype.card_unique

theorem grow_isolated_face_length [DecidableRel (growGraph H u).Adj]
    (f : (growIsolated u hconn hiso).Face) :
    (growIsolated u hconn hiso).faceLength f = 2 := by
  classical
  let : IsEmpty H.Dart := RotationSystem.is_empty_dart_of_isolated hconn hiso
  let : Unique (growIsolated u hconn hiso).Face := {
    default := f
    uniq := fun g => (grow_isolated_face_eq u hconn hiso g).trans
      (grow_isolated_face_eq u hconn hiso f).symm }
  have h := (growIsolated u hconn hiso).sum_face_lengths_eq_card_darts
  rw [grow_card_darts] at h
  simpa only [Fintype.sum_unique, Fintype.card_eq_zero, zero_add,
    show (default : (growIsolated u hconn hiso).Face) = f from Subsingleton.elim _ _] using h

/-- Attach a leaf at either kind of corner of a connected rotation system. -/
noncomputable def grow (R : RotationSystem H) (hconn : H.Connected) (c : R.Corner u) :
    RotationSystem (growGraph H u) :=
  match c with
  | .before a ha => growBefore u R a ha
  | .isolated hiso => growIsolated u hconn hiso

theorem grow_face_count [DecidableRel H.Adj] [DecidableRel (growGraph H u).Adj]
    (R : RotationSystem H) (hconn : H.Connected) (c : R.Corner u) :
    (grow u R hconn c).faceCount = R.faceCount := by
  cases c with
  | before a ha => exact grow_before_face_count u R a ha
  | isolated hiso =>
    exact (grow_isolated_face_count u hconn hiso).trans
      (R.face_count_of_isolated hconn hiso).symm

/-- Add a non-loop edge, without changing the vertex type. -/
def splitGraph (G : SimpleGraph V) (u v : V) (hne : u ≠ v) : SimpleGraph V where
  Adj x y := G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  symm := ⟨by
    intro x y h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl h.symm
    · exact .inr (.inr ⟨rfl, rfl⟩)
    · exact .inr (.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨by
    intro x h
    rcases h with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact h.ne rfl
    · exact hne (hx.symm.trans hy)
    · exact hne (hy.symm.trans hx)⟩

section Split

variable {G : SimpleGraph V} (u v : V) (hne : u ≠ v) (hmiss : ¬ G.Adj u v)

/-- Transport an existing dart when adding an edge. -/
def splitOld (d : G.Dart) : (splitGraph G u v hne).Dart := ⟨d.toProd, .inl d.adj⟩

/-- The new dart from the first endpoint to the second. -/
def splitOut : (splitGraph G u v hne).Dart := ⟨(u, v), .inr (.inl ⟨rfl, rfl⟩)⟩

/-- The reverse of the new dart. -/
def splitBack : (splitGraph G u v hne).Dart := (splitOut (G := G) u v hne).symm

/-- Enumerate the darts after inserting a missing edge. -/
def splitDart (x : G.Dart ⊕ Bool) : (splitGraph G u v hne).Dart :=
  match x with
  | .inl d => splitOld u v hne d
  | .inr false => splitOut u v hne
  | .inr true => splitBack u v hne

include hmiss in
theorem split_dart_injective : Function.Injective (splitDart (G := G) u v hne) := by
  intro x y h
  have hf := congrArg (fun d : (splitGraph G u v hne).Dart => d.fst) h
  have hs := congrArg (fun d : (splitGraph G u v hne).Dart => d.snd) h
  have notOut (d : G.Dart) (hf : d.fst = u) (hs : d.snd = v) : False :=
    hmiss (hf ▸ hs ▸ d.adj)
  have notBack (d : G.Dart) (hf : d.fst = v) (hs : d.snd = u) : False :=
    hmiss (hs ▸ hf ▸ d.adj.symm)
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Dart.ext _ _ (Prod.ext hf hs))
    | inr y =>
      cases y
      · exact (notOut x hf hs).elim
      · exact (notBack x hf hs).elim
  | inr x =>
    cases y with
    | inl y =>
      cases x
      · exact (notOut y hf.symm hs.symm).elim
      · exact (notBack y hf.symm hs.symm).elim
    | inr y =>
      cases x <;> cases y
      · rfl
      · exact (hne hf).elim
      · exact (hne hf.symm).elim
      · rfl

theorem split_dart_surjective : Function.Surjective (splitDart (G := G) u v hne) := by
  intro d
  rcases d.adj with hd | ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact ⟨.inl ⟨d.toProd, hd⟩, rfl⟩
  · exact ⟨.inr false, Dart.ext _ _ (Prod.ext hu.symm hv.symm)⟩
  · exact ⟨.inr true, Dart.ext _ _ (Prod.ext hu.symm hv.symm)⟩

/-- The dart correspondence for inserting a missing edge. -/
noncomputable def splitDartEquiv : G.Dart ⊕ Bool ≃ (splitGraph G u v hne).Dart :=
  Equiv.ofBijective (splitDart u v hne)
    ⟨split_dart_injective u v hne hmiss, split_dart_surjective u v hne⟩

theorem split_graph_connected (h : G.Connected) : (splitGraph G u v hne).Connected :=
  h.mono (fun _ _ h => .inl h)

include hmiss in
theorem split_card_darts [Fintype V] [DecidableRel G.Adj]
    [DecidableRel (splitGraph G u v hne).Adj] :
    Fintype.card (splitGraph G u v hne).Dart = Fintype.card G.Dart + 2 := by
  simpa using (Fintype.card_congr (splitDartEquiv u v hne hmiss)).symm

include hmiss in
theorem split_card_edges [Fintype V] [DecidableRel G.Adj]
    [DecidableRel (splitGraph G u v hne).Adj] :
    (splitGraph G u v hne).edgeFinset.card = G.edgeFinset.card + 1 := by
  have h := split_card_darts u v hne hmiss
  rw [card_dart_eq_twice_card_edges, card_dart_eq_twice_card_edges] at h
  omega

end Split

noncomputable section SplitRotation

local instance : DecidableEq V := Classical.decEq V

variable {G : SimpleGraph V} (R : RotationSystem G) (a b : G.Dart)

/-- Insert both orientations of a new edge in the specified vertex rotations. -/
noncomputable def splitNext : Equiv.Perm (G.Dart ⊕ Bool) := by
  classical
  exact (Equiv.sumCongr R.next (Equiv.refl Bool)).trans
    ((Equiv.swap (.inl a) (.inr false)).trans (Equiv.swap (.inl b) (.inr true)))

variable (hab : a.fst ≠ b.fst) (hmiss : ¬ G.Adj a.fst b.fst)

@[simp]
theorem split_next_old (d : G.Dart) : splitNext R a b (.inl d) =
    if R.next d = a then .inr false else if R.next d = b then .inr true
      else .inl (R.next d) := by
  classical
  by_cases h₁ : R.next d = a <;> by_cases h₂ : R.next d = b <;>
    simp_all [splitNext, Equiv.swap_apply_def]

include hab in
@[simp]
theorem split_next_out : splitNext R a b (.inr false) = .inl a := by
  have h : a ≠ b := fun h => hab (congrArg (fun d : G.Dart => d.fst) h)
  simp [splitNext, Equiv.swap_apply_def, h]

@[simp]
theorem split_next_back : splitNext R a b (.inr true) = .inl b := by
  simp [splitNext, Equiv.swap_apply_def]

include hab in
theorem split_reaches_old (d e : G.Dart) (h : Reaches R.next d e) :
    Reaches (splitNext R a b) (.inl d) (.inl e) := by
  classical
  apply Reaches.lift Sum.inl _ h
  intro x
  by_cases hx : R.next x = a
  · exact ⟨2, by simp [Function.iterate_succ_apply, hx, split_next_out R a b hab]⟩
  · by_cases hx' : R.next x = b
    · have hba : b ≠ a := fun h => hx (hx'.trans h)
      exact ⟨2, by simp [Function.iterate_succ_apply, hx', hba]⟩
    · exact ⟨1, by simp [hx, hx']⟩

/-- Add an edge with both endpoints inserted at prescribed nonempty corners. -/
noncomputable def split : RotationSystem (splitGraph G a.fst b.fst hab) where
  next := (splitDartEquiv a.fst b.fst hab hmiss).symm.trans
    ((splitNext R a b).trans (splitDartEquiv a.fst b.fst hab hmiss))
  next_fst := by
    classical
    intro d
    obtain ⟨x, rfl⟩ := (splitDartEquiv a.fst b.fst hab hmiss).surjective d
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    cases x with
    | inl x =>
      rw [split_next_old]
      split_ifs with h₁ h₂
      · exact (congrArg (fun d : G.Dart => d.fst) h₁).symm.trans (R.next_fst x)
      · exact (congrArg (fun d : G.Dart => d.fst) h₂).symm.trans (R.next_fst x)
      · exact R.next_fst x
    | inr x =>
      cases x
      · rw [split_next_out R a b hab]
        rfl
      · rw [split_next_back]
        rfl
  cyclic := by
    classical
    intro d e h
    obtain ⟨x, rfl⟩ := (splitDartEquiv a.fst b.fst hab hmiss).surjective d
    obtain ⟨y, rfl⟩ := (splitDartEquiv a.fst b.fst hab hmiss).surjective e
    apply Reaches.lift (σ := ⇑(splitNext R a b)) (splitDartEquiv a.fst b.fst hab hmiss)
      (fun z => ⟨1, by simp only [Function.iterate_one, Equiv.trans_apply,
        Equiv.symm_apply_apply]⟩)
    have hne : a ≠ b := fun h => hab (congrArg (fun d : G.Dart => d.fst) h)
    have pred_fst (d : G.Dart) : (R.next.symm d).fst = d.fst := by
      simpa using (R.next_fst (R.next.symm d)).symm
    have toOut : Reaches (splitNext R a b) (.inl (R.next.symm a)) (.inr false) :=
      ⟨1, by simp⟩
    have fromOut : Reaches (splitNext R a b) (.inr false) (.inl a) :=
      ⟨1, by simp [split_next_out R a b hab]⟩
    have toBack : Reaches (splitNext R a b) (.inl (R.next.symm b)) (.inr true) :=
      ⟨1, by simp [hne.symm]⟩
    have fromBack : Reaches (splitNext R a b) (.inr true) (.inl b) := ⟨1, by simp⟩
    cases x with
    | inl x =>
      cases y with
      | inl y => exact split_reaches_old R a b hab x y (R.cyclic _ _ h)
      | inr y =>
        cases y
        · exact (split_reaches_old R a b hab x (R.next.symm a)
            (R.cyclic _ _ (h.trans (pred_fst a).symm))).trans toOut
        · exact (split_reaches_old R a b hab x (R.next.symm b)
            (R.cyclic _ _ (h.trans (pred_fst b).symm))).trans toBack
    | inr x =>
      cases y with
      | inl y =>
        cases x
        · exact fromOut.trans (split_reaches_old R a b hab a y (R.cyclic _ _ h))
        · exact fromBack.trans (split_reaches_old R a b hab b y (R.cyclic _ _ h))
      | inr y =>
        cases x <;> cases y
        · exact Reaches.refl _
        · exact (hab h).elim
        · exact (hab h.symm).elim
        · exact Reaches.refl _

@[simp]
theorem split_next_apply (x : G.Dart ⊕ Bool) :
    (split R a b hab hmiss).next (splitDartEquiv a.fst b.fst hab hmiss x) =
      splitDartEquiv a.fst b.fst hab hmiss (splitNext R a b x) := by
  simp only [split, Equiv.trans_apply, Equiv.symm_apply_apply]

@[simp]
theorem split_old_symm (d : G.Dart) :
    (splitOld a.fst b.fst hab d).symm = splitOld a.fst b.fst hab d.symm := by
  apply Dart.ext
  rfl

@[simp]
theorem split_face_old (d : G.Dart) :
    (split R a b hab hmiss).faceNext (splitOld a.fst b.fst hab d) =
      if R.faceNext d = a then splitOut a.fst b.fst hab
      else if R.faceNext d = b then splitBack a.fst b.fst hab
      else splitOld a.fst b.fst hab (R.faceNext d) := by
  classical
  change (split R a b hab hmiss).next (splitOld a.fst b.fst hab d).symm = _
  rw [split_old_symm]
  change (split R a b hab hmiss).next (splitDartEquiv a.fst b.fst hab hmiss (.inl d.symm)) = _
  rw [split_next_apply, split_next_old]
  simp only [RotationSystem.face_next_apply]
  split_ifs <;> simp_all only [↓reduceIte] <;> rfl

@[simp]
theorem split_face_out :
    (split R a b hab hmiss).faceNext (splitOut a.fst b.fst hab) =
      splitOld a.fst b.fst hab b := by
  change (split R a b hab hmiss).next (splitDartEquiv a.fst b.fst hab hmiss (.inr true)) = _
  rw [split_next_apply, split_next_back]
  rfl

@[simp]
theorem split_face_back :
    (split R a b hab hmiss).faceNext (splitBack a.fst b.fst hab) =
      splitOld a.fst b.fst hab a := by
  change (split R a b hab hmiss).next (splitOut a.fst b.fst hab).symm.symm = _
  rw [Dart.symm_symm]
  change (split R a b hab hmiss).next (splitDartEquiv a.fst b.fst hab hmiss (.inr false)) = _
  rw [split_next_apply, split_next_out R a b hab]
  rfl

section SplitFaces

variable [Finite V] (hface : R.faceOf a = R.faceOf b)

include hab hface in
private theorem split_index_bounds :
    0 < R.facePosition a b ∧ R.facePosition a b < R.facePeriod a := by
  have hne : b ≠ a := fun h => hab (congrArg (fun d : G.Dart => d.fst) h.symm)
  exact ⟨Nat.pos_of_ne_zero (fun h => hne ((R.face_position_eq_zero a b).1 h)),
    (R.face_position_lt a b).2 hface.symm⟩

/-- Label the two portions of the selected old face separately. -/
noncomputable def splitOldLabel (d : G.Dart) : R.Face ⊕ Unit := by
  classical
  exact if R.faceOf d = R.faceOf a ∧ R.facePosition a b ≤ R.facePosition a d
    then .inr () else .inl (R.faceOf d)

/-- A label for each face after the new edge has been inserted. -/
noncomputable def splitFaceLabel (d : (splitGraph G a.fst b.fst hab).Dart) : R.Face ⊕ Unit :=
  match (splitDartEquiv a.fst b.fst hab hmiss).symm d with
  | .inl d => splitOldLabel R a b d
  | .inr false => .inr ()
  | .inr true => .inl (R.faceOf a)

@[simp]
theorem split_label_old (d : G.Dart) :
    splitFaceLabel R a b hab hmiss (splitOld a.fst b.fst hab d) = splitOldLabel R a b d := by
  unfold splitFaceLabel
  change (match (splitDartEquiv a.fst b.fst hab hmiss).symm
    (splitDartEquiv a.fst b.fst hab hmiss (.inl d)) with
    | .inl d => splitOldLabel R a b d
    | .inr false => .inr ()
    | .inr true => .inl (R.faceOf a)) = _
  rw [Equiv.symm_apply_apply]

@[simp]
theorem split_label_out :
    splitFaceLabel R a b hab hmiss (splitOut a.fst b.fst hab) = .inr () := by
  unfold splitFaceLabel
  change (match (splitDartEquiv a.fst b.fst hab hmiss).symm
    (splitDartEquiv a.fst b.fst hab hmiss (.inr false)) with
    | .inl d => splitOldLabel R a b d
    | .inr false => .inr ()
    | .inr true => .inl (R.faceOf a)) = _
  rw [Equiv.symm_apply_apply]

@[simp]
theorem split_label_back :
    splitFaceLabel R a b hab hmiss (splitBack a.fst b.fst hab) = .inl (R.faceOf a) := by
  unfold splitFaceLabel
  change (match (splitDartEquiv a.fst b.fst hab hmiss).symm
    (splitDartEquiv a.fst b.fst hab hmiss (.inr true)) with
    | .inl d => splitOldLabel R a b d
    | .inr false => .inr ()
    | .inr true => .inl (R.faceOf a)) = _
  rw [Equiv.symm_apply_apply]

include hab hface in
@[simp]
theorem split_old_label_a : splitOldLabel R a b a = .inl (R.faceOf a) := by
  have hk := (split_index_bounds R a b hab hface).1
  simp [splitOldLabel, hk.ne']

include hface in
@[simp]
theorem split_old_label_b : splitOldLabel R a b b = .inr () := by
  simp [splitOldLabel, hface]

include hab hface in
theorem split_label_next (d : (splitGraph G a.fst b.fst hab).Dart) :
    splitFaceLabel R a b hab hmiss ((split R a b hab hmiss).faceNext d) =
      splitFaceLabel R a b hab hmiss d := by
  classical
  obtain ⟨x, rfl⟩ := (splitDartEquiv a.fst b.fst hab hmiss).surjective d
  have hk := split_index_bounds R a b hab hface
  cases x with
  | inl d =>
    change splitFaceLabel R a b hab hmiss
      ((split R a b hab hmiss).faceNext (splitOld a.fst b.fst hab d)) =
        splitFaceLabel R a b hab hmiss (splitOld a.fst b.fst hab d)
    rw [split_face_old, split_label_old]
    by_cases hd : R.faceOf d = R.faceOf a
    · have hi := (R.face_position_lt a d).2 hd
      have hn := R.face_position_next a d hd
      have hstep :
          (R.facePosition a (R.faceNext d) = R.facePosition a d + 1 ∧
            R.facePosition a d + 1 < R.facePeriod a) ∨
          (R.facePosition a (R.faceNext d) = 0 ∧
            R.facePosition a d + 1 = R.facePeriod a) := by
        by_cases hlt : R.facePosition a d + 1 < R.facePeriod a
        · rw [Nat.mod_eq_of_lt hlt] at hn
          exact .inl ⟨hn, hlt⟩
        · have heq : R.facePosition a d + 1 = R.facePeriod a := by omega
          rw [heq, Nat.mod_self] at hn
          exact .inr ⟨hn, heq⟩
      have hf : R.faceOf (R.faceNext d) = R.faceOf a := (R.face_of_face_next d).trans hd
      split_ifs with h₁ h₂
      · rw [split_label_out]
        have hzero : R.facePosition a (R.faceNext d) = 0 := by simp [h₁]
        have hge : R.facePosition a b ≤ R.facePosition a d := by omega
        simp [splitOldLabel, hd, hge]
      · rw [split_label_back]
        have heq : R.facePosition a (R.faceNext d) = R.facePosition a b := by rw [h₂]
        have hlt : R.facePosition a d < R.facePosition a b := by omega
        simp [splitOldLabel, hd, Nat.not_le_of_gt hlt]
      · rw [split_label_old]
        have hzero : R.facePosition a (R.faceNext d) ≠ 0 := by
          intro h
          exact h₁ ((R.face_position_eq_zero a _).1 h)
        have hneq : R.facePosition a (R.faceNext d) ≠ R.facePosition a b := by
          intro h
          apply h₂
          rw [← R.face_position_spec a _ hf, ← R.face_position_spec a b hface.symm, h]
        have hiff : R.facePosition a b ≤ R.facePosition a (R.faceNext d) ↔
            R.facePosition a b ≤ R.facePosition a d := by omega
        simp only [splitOldLabel, hf, hd, true_and, hiff]
    · have h₁ : R.faceNext d ≠ a := by
        intro h
        exact hd ((R.face_of_face_next d).symm.trans (congrArg R.faceOf h))
      have h₂ : R.faceNext d ≠ b := by
        intro h
        exact hd (((R.face_of_face_next d).symm.trans (congrArg R.faceOf h)).trans hface.symm)
      rw [ite_eq_right h₁, ite_eq_right h₂, split_label_old]
      simp only [splitOldLabel, R.face_of_face_next, hd, false_and, ↓reduceIte]
  | inr x =>
    cases x
    · change splitFaceLabel R a b hab hmiss
        ((split R a b hab hmiss).faceNext (splitOut a.fst b.fst hab)) = _
      rw [split_face_out, split_label_old, split_old_label_b R a b hface]
      exact (split_label_out R a b hab hmiss).symm
    · change splitFaceLabel R a b hab hmiss
        ((split R a b hab hmiss).faceNext (splitBack a.fst b.fst hab)) = _
      rw [split_face_back, split_label_old, split_old_label_a R a b hab hface]
      exact (split_label_back R a b hab hmiss).symm

include hface in
theorem split_label_relation {d e : (splitGraph G a.fst b.fst hab).Dart}
    (h : (split R a b hab hmiss).FaceRelation d e) :
    splitFaceLabel R a b hab hmiss d = splitFaceLabel R a b hab hmiss e := by
  induction h with
  | refl d => rfl
  | step d => exact (split_label_next R a b hab hmiss hface d).symm
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

include hface in
theorem split_old_other_face {d e : G.Dart} (hd : R.faceOf d ≠ R.faceOf a)
    (h : R.FaceRelation d e) :
    (split R a b hab hmiss).FaceRelation (splitOld a.fst b.fst hab d)
      (splitOld a.fst b.fst hab e) := by
  classical
  obtain ⟨k, rfl⟩ := (R.face_relation_iff_iterate d e).1 h
  clear h
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    have hf : R.faceOf (R.faceNext ((⇑R.faceNext)^[k] d)) = R.faceOf d :=
      (R.face_of_face_next _).trans (R.face_of_iterate d k)
    have h₁ : R.faceNext ((⇑R.faceNext)^[k] d) ≠ a :=
      fun h => hd (hf.symm.trans (congrArg R.faceOf h))
    have h₂ : R.faceNext ((⇑R.faceNext)^[k] d) ≠ b :=
      fun h => hd ((hf.symm.trans (congrArg R.faceOf h)).trans hface.symm)
    have hs := RotationSystem.FaceRelation.step (R := split R a b hab hmiss)
      (splitOld a.fst b.fst hab ((⇑R.faceNext)^[k] d))
    rw [split_face_old, ite_eq_right h₁, ite_eq_right h₂] at hs
    simpa only [Function.iterate_succ_apply'] using ih.trans hs

theorem split_segment {i j : ℕ} (hij : i ≤ j) (hj : j < R.facePeriod a)
    (hside : j < R.facePosition a b ∨ R.facePosition a b ≤ i) :
    (split R a b hab hmiss).FaceRelation
      (splitOld a.fst b.fst hab ((⇑R.faceNext)^[i] a))
      (splitOld a.fst b.fst hab ((⇑R.faceNext)^[j] a)) := by
  classical
  induction j, hij using Nat.le_induction with
  | base => exact .refl _
  | succ j hij ih =>
    have hj' : j < R.facePeriod a := by omega
    have hs' : j < R.facePosition a b ∨ R.facePosition a b ≤ i := by omega
    have hnext : R.faceNext ((⇑R.faceNext)^[j] a) = (⇑R.faceNext)^[j + 1] a :=
      (Function.iterate_succ_apply' _ _ _).symm
    have h₁ : R.faceNext ((⇑R.faceNext)^[j] a) ≠ a := by
      intro h
      have hi := congrArg (R.facePosition a) h
      rw [hnext, R.face_position_iterate a hj, R.face_position_self] at hi
      omega
    have h₂ : R.faceNext ((⇑R.faceNext)^[j] a) ≠ b := by
      intro h
      have hi := congrArg (R.facePosition a) h
      rw [hnext, R.face_position_iterate a hj] at hi
      omega
    have hs := RotationSystem.FaceRelation.step (R := split R a b hab hmiss)
      (splitOld a.fst b.fst hab ((⇑R.faceNext)^[j] a))
    rw [split_face_old, ite_eq_right h₁, ite_eq_right h₂, hnext] at hs
    exact (ih hj' hs').trans hs

/-- Choose a new boundary dart for each old-face label and the extra face label. -/
noncomputable def splitAnchor (t : R.Face ⊕ Unit) : (splitGraph G a.fst b.fst hab).Dart := by
  classical
  exact match t with
  | .inl f => if f = R.faceOf a then splitOld a.fst b.fst hab a
      else splitOld a.fst b.fst hab (R.faceRepresentative a f)
  | .inr _ => splitOld a.fst b.fst hab b

include hface in
theorem split_relation_anchor (d : (splitGraph G a.fst b.fst hab).Dart) :
    (split R a b hab hmiss).FaceRelation d
      (splitAnchor R a b hab (splitFaceLabel R a b hab hmiss d)) := by
  classical
  obtain ⟨x, rfl⟩ := (splitDartEquiv a.fst b.fst hab hmiss).surjective d
  cases x with
  | inl d =>
    change (split R a b hab hmiss).FaceRelation (splitOld a.fst b.fst hab d)
      (splitAnchor R a b hab (splitFaceLabel R a b hab hmiss (splitOld a.fst b.fst hab d)))
    rw [split_label_old]
    by_cases hd : R.faceOf d = R.faceOf a
    · have hi := (R.face_position_lt a d).2 hd
      by_cases hge : R.facePosition a b ≤ R.facePosition a d
      · simp only [splitOldLabel, hd, hge, and_self, ↓reduceIte, splitAnchor]
        have h := split_segment R a b hab hmiss hge hi (Or.inr le_rfl)
        rw [R.face_position_spec a b hface.symm, R.face_position_spec a d hd] at h
        exact .symm h
      · simp only [splitOldLabel, hd, hge, and_false, ↓reduceIte, splitAnchor]
        have h := split_segment R a b hab hmiss (Nat.zero_le (R.facePosition a d))
          hi (Or.inl (Nat.lt_of_not_ge hge))
        rw [R.face_position_spec a d hd] at h
        exact .symm h
    · simp only [splitOldLabel, hd, false_and, ↓reduceIte, splitAnchor]
      apply split_old_other_face R a b hab hmiss hface hd
      exact (R.face_of_eq_iff _ _).1 (R.face_of_representative a (R.faceOf d)).symm
  | inr x =>
    cases x
    · change (split R a b hab hmiss).FaceRelation (splitOut a.fst b.fst hab)
        (splitAnchor R a b hab (splitFaceLabel R a b hab hmiss (splitOut a.fst b.fst hab)))
      rw [split_label_out]
      have h := RotationSystem.FaceRelation.step (R := split R a b hab hmiss)
        (splitOut a.fst b.fst hab)
      rw [split_face_out] at h
      exact h
    · change (split R a b hab hmiss).FaceRelation (splitBack a.fst b.fst hab)
        (splitAnchor R a b hab (splitFaceLabel R a b hab hmiss (splitBack a.fst b.fst hab)))
      rw [split_label_back]
      simp only [splitAnchor, ↓reduceIte]
      have h := RotationSystem.FaceRelation.step (R := split R a b hab hmiss)
        (splitBack a.fst b.fst hab)
      rw [split_face_back] at h
      exact h

include hface in
theorem split_label_anchor (t : R.Face ⊕ Unit) :
    splitFaceLabel R a b hab hmiss (splitAnchor R a b hab t) = t := by
  classical
  cases t with
  | inl f =>
    by_cases hf : f = R.faceOf a
    · subst f
      simp only [splitAnchor, ↓reduceIte, split_label_old, split_old_label_a R a b hab hface]
    · simp only [splitAnchor, hf, ↓reduceIte, split_label_old]
      simp only [splitOldLabel, R.face_of_representative, hf, false_and, ↓reduceIte]
  | inr x =>
    cases x
    exact (split_label_old R a b hab hmiss b).trans (split_old_label_b R a b hface)

/-- Splitting a face replaces one orbit by two and keeps all other orbits. -/
noncomputable def splitOrbitEquiv :
    Quotient (split R a b hab hmiss).faceSetoid ≃ R.Face ⊕ Unit where
  toFun := Quotient.lift (splitFaceLabel R a b hab hmiss)
    (fun _ _ => split_label_relation R a b hab hmiss hface)
  invFun t := Quotient.mk _ (splitAnchor R a b hab t)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ d => exact Quotient.sound (.symm (split_relation_anchor R a b hab hmiss hface d))
  right_inv := split_label_anchor R a b hab hmiss hface

/-- The face correspondence for inserting an edge within one face. -/
noncomputable def splitFaceEquiv : (split R a b hab hmiss).Face ≃ R.Face ⊕ Unit :=
  ((split R a b hab hmiss).faceQuotientEquiv (splitOut a.fst b.fst hab)).trans
    (splitOrbitEquiv R a b hab hmiss hface)

include hface in
theorem split_face_count [Fintype V] [DecidableRel G.Adj]
    [DecidableRel (splitGraph G a.fst b.fst hab).Adj] :
    (split R a b hab hmiss).faceCount = R.faceCount + 1 := by
  simpa [RotationSystem.faceCount] using Fintype.card_congr
    (splitFaceEquiv R a b hab hmiss hface)

end SplitFaces

end SplitRotation

end PlaneMapConstruction

end SimpleGraph
