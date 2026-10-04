/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Rotation systems, corners, and face orbits

A rotation system orders the outgoing darts cyclically at each vertex. Faces are
orbits of `next ∘ Dart.symm`, with one empty face when there are no darts.
Face lengths sum to the dart count, and the dart count is twice the edge count.
Face orbits are indexed by their minimal periods. A connected graph with an
isolated vertex has one vertex, no darts, and one empty face.
-/

@[expose] public section

namespace SimpleGraph

open scoped BigOperators

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A permutation of darts giving a single cyclic order at each vertex.

The orbit condition is vacuous at an isolated vertex.
-/
structure RotationSystem (G : SimpleGraph V) where
  /-- The successor in the rotation at the initial vertex. -/
  next : Equiv.Perm G.Dart
  /-- Rotation preserves the initial vertex. -/
  next_fst : ∀ d, (next d).fst = d.fst
  /-- Darts with the same initial vertex belong to one successor orbit. -/
  cyclic : ∀ d e, d.fst = e.fst →
    ∃ n : ℕ, ((next : G.Dart → G.Dart)^[n]) d = e

namespace RotationSystem

/-- An insertion position in a vertex rotation, including an empty rotation. -/
inductive Corner (R : RotationSystem G) (v : V)
  | before (a : G.Dart) (h : a.fst = v)
  | isolated (h : ∀ w, ¬ G.Adj v w)

variable (R : RotationSystem G)

/-- Reversing darts is an involutive permutation. -/
def reversal : Equiv.Perm G.Dart where
  toFun := Dart.symm
  invFun := Dart.symm
  left_inv d := Dart.symm_symm d
  right_inv d := Dart.symm_symm d

/-- The face successor reverses a dart and then takes its rotation successor. -/
def faceNext : Equiv.Perm G.Dart :=
  (reversal (G := G)).trans R.next

@[simp]
theorem face_next_apply (d : G.Dart) :
    R.faceNext d = R.next d.symm :=
  rfl

theorem face_next_fst (d : G.Dart) :
    (R.faceNext d).fst = d.snd :=
  R.next_fst d.symm

/-- The equivalence closure of the face-successor relation.

On a finite dart set, its classes are the cycles of the face permutation.
-/
inductive FaceRelation : G.Dart → G.Dart → Prop
  | refl (d : G.Dart) : FaceRelation d d
  | step (d : G.Dart) : FaceRelation d (R.faceNext d)
  | symm {d e : G.Dart} : FaceRelation d e → FaceRelation e d
  | trans {d e f : G.Dart} :
      FaceRelation d e → FaceRelation e f → FaceRelation d f

/-- The setoid whose classes are the face orbits. -/
def faceSetoid : Setoid G.Dart where
  r := R.FaceRelation
  iseqv := {
    refl := fun d => FaceRelation.refl d
    symm := fun h => FaceRelation.symm h
    trans := fun h₁ h₂ => FaceRelation.trans h₁ h₂
  }

/-- A face is a dart orbit, with one empty face exactly when there are no darts.

The second summand is empty whenever the graph has an edge.
-/
def Face :=
  Quotient R.faceSetoid ⊕ {_x : Unit // IsEmpty G.Dart}

/-- The face containing a dart. -/
def faceOf (d : G.Dart) : R.Face :=
  Sum.inl (Quotient.mk R.faceSetoid d)

theorem face_of_eq_iff (d e : G.Dart) :
    R.faceOf d = R.faceOf e ↔ R.FaceRelation d e := by
  constructor
  · intro h
    exact Quotient.exact (Sum.inl.inj h)
  · intro h
    exact congrArg Sum.inl (Quotient.sound h)

@[simp]
theorem face_of_face_next (d : G.Dart) :
    R.faceOf (R.faceNext d) = R.faceOf d := by
  apply (R.face_of_eq_iff _ _).2
  exact FaceRelation.symm (FaceRelation.step d)

/-- The permutation induced on the darts starting at a specified vertex. -/
def rotationAt (v : V) : Equiv.Perm {d : G.Dart // d.fst = v} where
  toFun d := ⟨R.next d.val, (R.next_fst d.val).trans d.property⟩
  invFun d := ⟨R.next.symm d.val, by
    have h := R.next_fst (R.next.symm d.val)
    rw [R.next.apply_symm_apply] at h
    exact h.symm.trans d.property⟩
  left_inv d := by
    apply Subtype.ext
    exact R.next.symm_apply_apply d.val
  right_inv d := by
    apply Subtype.ext
    exact R.next.apply_symm_apply d.val

@[simp]
theorem rotation_at_val (v : V) (d : {d : G.Dart // d.fst = v}) :
    (R.rotationAt v d).val = R.next d.val :=
  rfl

/-- Pairing each dart with its face gives an equivalent dart type. -/
def faceFiberEquiv :
    (Σ f : R.Face, {d : G.Dart // R.faceOf d = f}) ≃ G.Dart where
  toFun p := p.2.val
  invFun d := ⟨R.faceOf d, ⟨d, rfl⟩⟩
  left_inv := by
    intro p
    rcases p with ⟨f, d, h⟩
    cases h
    rfl
  right_inv := by
    intro d
    rfl

/-- A dartless rotation system has exactly one face, represented by `Unit`. -/
def emptyFaceEquiv [IsEmpty G.Dart] : R.Face ≃ Unit where
  toFun _ := ()
  invFun _ := Sum.inr ⟨(), inferInstance⟩
  left_inv := by
    intro f
    rcases f with q | ⟨x, h⟩
    · refine Quotient.inductionOn q ?_
      intro d
      exact isEmptyElim d
    · cases x
      rfl
  right_inv := by
    intro x
    cases x
    rfl

/-- The unoriented edge of a dart, regarded as an element of the edge set. -/
def edgeOfDart (d : G.Dart) : G.edgeSet :=
  ⟨d.edge, by
    change G.Adj d.fst d.snd
    exact d.adj⟩

theorem edge_of_dart_surjective :
    Function.Surjective (edgeOfDart (G := G)) := by
  intro e
  rcases e with ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro x y h
  change G.Adj x y at h
  exact ⟨{ toProd := (x, y), adj := h }, rfl⟩

theorem dart_ne_symm (d : G.Dart) : d ≠ d.symm := by
  intro h
  have huv : d.fst = d.snd :=
    congrArg (fun x : G.Dart => x.fst) h
  exact d.fst_ne_snd huv

@[simp]
theorem edge_of_dart_symm (d : G.Dart) :
    edgeOfDart d.symm = edgeOfDart d := by
  apply Subtype.ext
  change d.symm.edge = d.edge
  rw [dart_edge_eq_iff]
  simp

theorem edge_of_dart_eq_iff (d e : G.Dart) :
    edgeOfDart d = edgeOfDart e ↔ d = e ∨ d = e.symm := by
  constructor
  · intro h
    have he : d.edge = e.edge := congrArg Subtype.val h
    rw [dart_edge_eq_iff] at he
    exact he
  · intro h
    rcases h with h | h
    · exact congrArg edgeOfDart h
    · subst d
      exact edge_of_dart_symm e

/-- An edge fiber consists of a chosen dart and its distinct reverse. -/
noncomputable def edgeFiberBoolEquiv (e : G.edgeSet) (d : G.Dart)
    (hd : edgeOfDart d = e) :
    {x : G.Dart // edgeOfDart x = e} ≃ Bool := by
  classical
  have hs : edgeOfDart d.symm = e :=
    (edge_of_dart_symm d).trans hd
  have hne : d.symm ≠ d := Ne.symm (dart_ne_symm d)
  refine {
    toFun := fun x => decide (x.val = d)
    invFun := fun b => if b = true then ⟨d, hd⟩ else ⟨d.symm, hs⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro x
    have hx : x.val = d ∨ x.val = d.symm :=
      (edge_of_dart_eq_iff x.val d).1 (x.property.trans hd.symm)
    apply Subtype.ext
    rcases hx with hx | hx
    · simp [hx]
    · simp [hx, hne]
  · intro b
    cases b <;> simp [hne]

/-- Pairing each dart with its unoriented edge gives an equivalent dart type. -/
def edgeFiberEquiv :
    (Σ e : G.edgeSet, {d : G.Dart // edgeOfDart d = e}) ≃ G.Dart where
  toFun p := p.2.val
  invFun d := ⟨edgeOfDart d, ⟨d, rfl⟩⟩
  left_inv := by
    intro p
    rcases p with ⟨e, d, h⟩
    cases h
    rfl
  right_inv := by
    intro d
    rfl

theorem eq_of_isolated (hconn : G.Connected) {v : V}
    (hiso : ∀ w, ¬ G.Adj v w) (w : V) : v = w := by
  rcases hconn.preconnected v w with ⟨p⟩
  cases p with
  | nil => rfl
  | cons h p => exact (hiso _ h).elim

theorem is_empty_dart_of_isolated (hconn : G.Connected) {v : V}
    (hiso : ∀ w, ¬ G.Adj v w) : IsEmpty G.Dart := by
  refine ⟨?_⟩
  intro d
  have h : v = d.fst := eq_of_isolated hconn hiso d.fst
  exact hiso d.snd (h.symm ▸ d.adj)

theorem card_eq_one_of_isolated [Fintype V] (hconn : G.Connected) {v : V}
    (hiso : ∀ w, ¬ G.Adj v w) : Fintype.card V = 1 := by
  let e : V ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => v
    left_inv := fun w => eq_of_isolated hconn hiso w
    right_inv := by
      intro x
      cases x
      rfl
  }
  simpa using Fintype.card_congr e

theorem fin_eq_one_of_isolated {n : ℕ} {H : SimpleGraph (Fin n)}
    (hconn : H.Connected) {v : Fin n}
    (hiso : ∀ w, ¬ H.Adj v w) : n = 1 := by
  simpa using card_eq_one_of_isolated hconn hiso

end RotationSystem

theorem card_dart_eq_twice_card_edges [Fintype V] [DecidableRel G.Adj] :
    Fintype.card G.Dart = 2 * G.edgeFinset.card := by
  classical
  calc
    Fintype.card G.Dart =
        Fintype.card
          (Σ e : G.edgeSet,
            {d : G.Dart // RotationSystem.edgeOfDart d = e}) :=
      (Fintype.card_congr
        (RotationSystem.edgeFiberEquiv (G := G))).symm
    _ = ∑ e : G.edgeSet,
        Fintype.card {d : G.Dart // RotationSystem.edgeOfDart d = e} := by
      rw [Fintype.card_sigma]
    _ = ∑ _e : G.edgeSet, 2 := by
      apply Finset.sum_congr rfl
      intro e _
      obtain ⟨d, hd⟩ := RotationSystem.edge_of_dart_surjective e
      exact
        (Fintype.card_congr
          (RotationSystem.edgeFiberBoolEquiv e d hd)).trans (by decide)
    _ = 2 * G.edgeFinset.card := by
      simp [edgeFinset_card, Nat.mul_comm]

namespace RotationSystem

variable (R : RotationSystem G)

section Finite

variable [Fintype V] [DecidableRel G.Adj]

/-- A finite graph has finitely many faces. -/
noncomputable instance instFintypeFace : Fintype R.Face := by
  classical
  unfold Face
  exact Fintype.ofFinite _

/-- The length of a face is the number of darts in its boundary orbit.

Both orientations of an edge may contribute to the same face. The empty face
has length zero.
-/
noncomputable def faceLength (f : R.Face) : ℕ := by
  classical
  exact Fintype.card {d : G.Dart // R.faceOf d = f}

/-- The number of faces, including the empty face of a dartless graph. -/
noncomputable def faceCount : ℕ :=
  Fintype.card R.Face

theorem sum_face_lengths_eq_card_darts :
    (∑ f : R.Face, R.faceLength f) = Fintype.card G.Dart := by
  classical
  change (∑ f : R.Face, Fintype.card {d : G.Dart // R.faceOf d = f}) = _
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr R.faceFiberEquiv

theorem sum_face_lengths_eq_twice_card_edges :
    (∑ f : R.Face, R.faceLength f) = 2 * G.edgeFinset.card := by
  calc
    (∑ f : R.Face, R.faceLength f) = Fintype.card G.Dart :=
      R.sum_face_lengths_eq_card_darts
    _ = 2 * G.edgeFinset.card := card_dart_eq_twice_card_edges

theorem face_count_of_is_empty [IsEmpty G.Dart] :
    R.faceCount = 1 := by
  simpa [faceCount] using Fintype.card_congr R.emptyFaceEquiv

theorem face_length_of_is_empty [IsEmpty G.Dart] (f : R.Face) :
    R.faceLength f = 0 := by
  classical
  simp [faceLength]

theorem face_count_of_isolated (hconn : G.Connected) {v : V}
    (hiso : ∀ w, ¬ G.Adj v w) : R.faceCount = 1 := by
  let : IsEmpty G.Dart := is_empty_dart_of_isolated hconn hiso
  exact R.face_count_of_is_empty

end Finite

end RotationSystem

namespace RotationSystem

/-- With a dart present, all faces are nonempty orbit classes. -/
def faceQuotientEquiv (R : RotationSystem G) (d : G.Dart) :
    R.Face ≃ Quotient R.faceSetoid where
  toFun f := match f with
    | .inl q => q
    | .inr h => (h.property.false d).elim
  invFun := Sum.inl
  left_inv f := by
    cases f with
    | inl q => rfl
    | inr h => exact (h.property.false d).elim
  right_inv _ := rfl

theorem face_of_surjective (R : RotationSystem G) (a : G.Dart) :
    Function.Surjective R.faceOf := by
  intro f
  cases f with
  | inl q =>
    induction q using Quotient.inductionOn with
    | _ d => exact ⟨d, rfl⟩
  | inr h => exact (h.property.false a).elim

/-- Choose one boundary dart from each face when the graph has a dart. -/
noncomputable def faceRepresentative (R : RotationSystem G) (a : G.Dart) (f : R.Face) :
    G.Dart := Classical.choose (R.face_of_surjective a f)

@[simp]
theorem face_of_representative (R : RotationSystem G) (a : G.Dart) (f : R.Face) :
    R.faceOf (R.faceRepresentative a f) = f := Classical.choose_spec (R.face_of_surjective a f)

theorem FaceRelation.map {W : Type*} {K : SimpleGraph W}
    {R : RotationSystem G} {S : RotationSystem K} (f : G.Dart → K.Dart)
    (hf : ∀ d, S.FaceRelation (f d) (f (R.faceNext d)))
    {d e : G.Dart} (h : R.FaceRelation d e) : S.FaceRelation (f d) (f e) := by
  induction h with
  | refl d => exact .refl _
  | step d => exact hf d
  | symm _ ih => exact .symm ih
  | trans _ _ ih ih' => exact .trans ih ih'

section OrbitCoordinates

variable [Finite V] (R : RotationSystem G)

private theorem reverse_reaches {d e : G.Dart}
    (h : ∃ k : ℕ, (⇑R.faceNext)^[k] d = e) :
    ∃ k : ℕ, (⇑R.faceNext)^[k] e = d := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let σ := R.faceNext
  let p := Function.minimalPeriod (⇑σ) d
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts
    (σ.injective.mem_periodicPts d)
  obtain ⟨k, hk⟩ := h
  have hk' : (⇑σ)^[k % p] d = e := Function.iterate_mod_minimalPeriod_eq.trans hk
  refine ⟨p - k % p, ?_⟩
  rw [← hk', ← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.mod_lt _ hp).le]
  exact Function.iterate_minimalPeriod

theorem face_relation_iff_iterate (d e : G.Dart) :
    R.FaceRelation d e ↔ ∃ k : ℕ, (⇑R.faceNext)^[k] d = e := by
  constructor
  · intro h
    induction h with
    | refl d => exact ⟨0, rfl⟩
    | step d => exact ⟨1, rfl⟩
    | symm _ ih => exact R.reverse_reaches ih
    | trans _ _ ih ih' =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨l, hl⟩ := ih'
      exact ⟨l + k, by rw [Function.iterate_add_apply, hk, hl]⟩
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => exact .refl _
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact .trans ih (.step _)

@[simp]
theorem face_of_iterate (d : G.Dart) (k : ℕ) :
    R.faceOf ((⇑R.faceNext)^[k] d) = R.faceOf d :=
  ((R.face_of_eq_iff _ _).2 ((R.face_relation_iff_iterate _ _).2 ⟨k, rfl⟩)).symm

/-- The period of the face successor at a dart. -/
noncomputable def facePeriod (a : G.Dart) : ℕ := Function.minimalPeriod (⇑R.faceNext) a

theorem face_period_pos (a : G.Dart) : 0 < R.facePeriod a := by
  classical
  let : Fintype V := Fintype.ofFinite V
  exact Function.minimalPeriod_pos_of_mem_periodicPts (R.faceNext.injective.mem_periodicPts a)

/-- Number the darts of a face starting at a chosen boundary dart. -/
noncomputable def faceOrbitEquiv (a : G.Dart) :
    Fin (R.facePeriod a) ≃ {d : G.Dart // R.faceOf d = R.faceOf a} := by
  refine Equiv.ofBijective (fun i => ⟨(⇑R.faceNext)^[i.val] a, R.face_of_iterate a i.val⟩) ?_
  constructor
  · intro i j h
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt (congrArg Subtype.val h)
  · intro d
    obtain ⟨k, hk⟩ := (R.face_relation_iff_iterate a d.val).1
      ((R.face_of_eq_iff _ _).1 d.property.symm)
    refine ⟨⟨k % R.facePeriod a, Nat.mod_lt _ (R.face_period_pos a)⟩, Subtype.ext ?_⟩
    exact Function.iterate_mod_minimalPeriod_eq.trans hk

@[simp]
theorem face_orbit_equiv_val (a : G.Dart) (i : Fin (R.facePeriod a)) :
    (R.faceOrbitEquiv a i).val = (⇑R.faceNext)^[i.val] a := rfl

/-- The position of a dart in the chosen face orbit; the period denotes a different face. -/
noncomputable def facePosition (a d : G.Dart) : ℕ := by
  classical
  exact if h : R.faceOf d = R.faceOf a then
    ((R.faceOrbitEquiv a).symm ⟨d, h⟩).val else R.facePeriod a

theorem face_position_lt (a d : G.Dart) :
    R.facePosition a d < R.facePeriod a ↔ R.faceOf d = R.faceOf a := by
  classical
  unfold facePosition
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => ((R.faceOrbitEquiv a).symm ⟨d, h⟩).isLt⟩
  · simp [h]

theorem face_position_spec (a d : G.Dart) (h : R.faceOf d = R.faceOf a) :
    (⇑R.faceNext)^[R.facePosition a d] a = d := by
  classical
  unfold facePosition
  rw [dite_eq_left h]
  exact congrArg Subtype.val ((R.faceOrbitEquiv a).apply_symm_apply ⟨d, h⟩)

theorem face_position_iterate (a : G.Dart) {i : ℕ} (hi : i < R.facePeriod a) :
    R.facePosition a ((⇑R.faceNext)^[i] a) = i := by
  classical
  unfold facePosition
  rw [dite_eq_left (R.face_of_iterate a i)]
  change ((R.faceOrbitEquiv a).symm (R.faceOrbitEquiv a ⟨i, hi⟩)).val = i
  rw [Equiv.symm_apply_apply]

@[simp]
theorem face_position_self (a : G.Dart) : R.facePosition a a = 0 :=
  R.face_position_iterate a (R.face_period_pos a)

theorem face_position_eq_zero (a d : G.Dart) : R.facePosition a d = 0 ↔ d = a := by
  constructor
  · intro h
    have hd : R.faceOf d = R.faceOf a := (R.face_position_lt a d).1
      (h ▸ R.face_period_pos a)
    simpa [h] using (R.face_position_spec a d hd).symm
  · rintro rfl
    exact R.face_position_self _

theorem face_position_next (a d : G.Dart) (h : R.faceOf d = R.faceOf a) :
    R.facePosition a (R.faceNext d) = (R.facePosition a d + 1) % R.facePeriod a := by
  have hd : R.faceNext d =
      (⇑R.faceNext)^[(R.facePosition a d + 1) % R.facePeriod a] a := by
    simp only [facePeriod]
    rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply',
      R.face_position_spec a d h]
  rw [hd]
  exact R.face_position_iterate a (Nat.mod_lt _ (R.face_period_pos a))

end OrbitCoordinates

section FiniteOrbitCoordinates

variable [Fintype V] [DecidableRel G.Adj] (R : RotationSystem G)

theorem face_length_eq_period (a : G.Dart) : R.faceLength (R.faceOf a) = R.facePeriod a := by
  classical
  simpa [faceLength] using (Fintype.card_congr (R.faceOrbitEquiv a)).symm

theorem face_next_iterate_length (a : G.Dart) :
    (⇑R.faceNext)^[R.faceLength (R.faceOf a)] a = a := by
  rw [R.face_length_eq_period]
  exact Function.iterate_minimalPeriod

theorem face_length_pos (a : G.Dart) : 0 < R.faceLength (R.faceOf a) := by
  rw [R.face_length_eq_period]
  exact R.face_period_pos a

end FiniteOrbitCoordinates

/-- The unique rotation on a graph with no darts. -/
def empty [IsEmpty G.Dart] : RotationSystem G where
  next := Equiv.refl _
  next_fst d := isEmptyElim d
  cyclic d := isEmptyElim d

theorem eq_empty [IsEmpty G.Dart] (R : RotationSystem G) : R = empty := by
  cases R with
  | mk next next_fst cyclic =>
    have h : next = Equiv.refl G.Dart := by
      apply Equiv.ext
      intro d
      exact isEmptyElim d
    cases h
    rfl

end RotationSystem

namespace RotationSystem

/-- Neighbours correspond to outgoing darts at a vertex. -/
def neighborDartEquiv (v : V) : G.neighborSet v ≃ {d : G.Dart // d.fst = v} where
  toFun w := ⟨G.dartOfNeighborSet v w, rfl⟩
  invFun d := ⟨d.val.snd, by
    change G.Adj v d.val.snd
    simpa only [d.property] using d.val.adj⟩
  left_inv _ := rfl
  right_inv d := by
    apply Subtype.ext
    apply Dart.ext
    exact Prod.ext d.property.symm rfl

/-- The cyclic permutation of the neighbours induced by a vertex rotation. -/
def neighborRotation (R : RotationSystem G) (v : V) : Equiv.Perm (G.neighborSet v) :=
  (neighborDartEquiv v).trans ((R.rotationAt v).trans (neighborDartEquiv v).symm)

variable (R : RotationSystem G)

theorem neighbor_rotation_dart (v : V) (w : G.neighborSet v) :
    G.dartOfNeighborSet v (R.neighborRotation v w) = R.next (G.dartOfNeighborSet v w) := by
  apply Dart.ext
  exact Prod.ext (R.next_fst (G.dartOfNeighborSet v w)).symm rfl

theorem neighbor_rotation_cyclic (v : V) (w z : G.neighborSet v) :
    ∃ k : ℕ, (⇑(R.neighborRotation v))^[k] w = z := by
  obtain ⟨k, hk⟩ := R.cyclic (G.dartOfNeighborSet v w) (G.dartOfNeighborSet v z) rfl
  refine ⟨k, G.dartOfNeighborSet_injective v ?_⟩
  have h : Function.Semiconj (G.dartOfNeighborSet v) (R.neighborRotation v) R.next :=
    R.neighbor_rotation_dart v
  exact (h.iterate_right k w).trans hk

section FiniteNeighbours

variable [Fintype V] [DecidableRel G.Adj]

theorem neighbor_rotation_adj (hfaces : ∀ f : R.Face, R.faceLength f = 3)
    (v : V) (w : G.neighborSet v) : G.Adj w.val (R.neighborRotation v w).val := by
  let d := G.dartOfNeighborSet v w
  have h := R.face_next_iterate_length d.symm
  rw [hfaces] at h
  have h₃ : R.faceNext (R.faceNext (R.next d)) = d.symm := by
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      RotationSystem.face_next_apply, Dart.symm_symm] using h
  have hs : (R.faceNext (R.next d)).snd = d.snd :=
    (R.face_next_fst _).symm.trans (congrArg (fun d : G.Dart => d.fst) h₃)
  have he := (R.faceNext (R.next d)).adj
  rw [R.face_next_fst, hs] at he
  exact he.symm

/-- Enumerate all neighbours by iterating their cyclic rotation from one neighbour. -/
noncomputable def neighborOrbitEquiv (v : V) (w : G.neighborSet v) :
    Fin (Function.minimalPeriod (⇑(R.neighborRotation v)) w) ≃ G.neighborSet v := by
  classical
  refine Equiv.ofBijective (fun i => (⇑(R.neighborRotation v))^[i.val] w) ?_
  constructor
  · intro i j h
    exact Fin.ext (Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt h)
  · intro z
    obtain ⟨k, hk⟩ := R.neighbor_rotation_cyclic v w z
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts
      ((R.neighborRotation v).injective.mem_periodicPts w)
    exact ⟨⟨k % _, Nat.mod_lt _ hp⟩, Function.iterate_mod_minimalPeriod_eq.trans hk⟩

theorem neighbor_period_eq_degree (v : V) (w : G.neighborSet v) :
    Function.minimalPeriod (⇑(R.neighborRotation v)) w = G.degree v := by
  simpa only [Fintype.card_fin, card_neighborSet_eq_degree] using
    Fintype.card_congr (R.neighborOrbitEquiv v w)

end FiniteNeighbours

end RotationSystem

end SimpleGraph
