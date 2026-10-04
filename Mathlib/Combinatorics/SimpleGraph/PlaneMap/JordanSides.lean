/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Examples
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic.Abel

/-!
# Combinatorial two-sides of a cycle

A `CycleCut` is a nonempty simple cycle given by its vertex set and, at
each cycle vertex, the two outgoing cycle darts that bound the sectors.
The open `next`-interval from the left dart to the right dart is the left
sector; the opposite interval is the right sector. Off-cycle vertices are
on the left (resp. right) side when a walk from the head of a left-sector
(resp. right-sector) dart reaches them without meeting the cycle.

No edge of a spherical map joins the two sides, and a walk that avoids
the cycle stays on one side. A cycle appears at a `split`; later grow
and split refine a side. This file defines the cut and proves the two
constructor checks: on `cycleMap` both sides are empty, and on a facial
triangle of `tetrahedron` the leftover vertex occupies exactly one side.

For the degree-5 step of five colour: if `x1,…,x5` are the neighbours of
a deleted vertex in rotation order, the cut through `x1,x,x3` places
`x2` and `x4` in opposite sectors at `x`.
-/

@[expose] public section

namespace SimpleGraph

open Walk
open PlaneMapConstruction

namespace PlaneMap

set_option linter.style.openClassical false

open Classical

variable {n : ℕ}

/-- A nonempty oriented simple cycle in a plane map, given by its
vertices and the two outgoing cycle darts at each vertex. `left` is the
successor dart and `right` is the predecessor dart. -/
structure CycleCut (M : PlaneMap n) where
  /-- Vertices of the cycle. -/
  verts : Finset (Fin n)
  /-- The cycle is nonempty. -/
  nonempty : verts.Nonempty
  /-- Outgoing successor dart at a cycle vertex. -/
  left : verts → M.Dart
  /-- Outgoing predecessor dart at a cycle vertex. -/
  right : verts → M.Dart
  left_fst : ∀ v, (left v).fst = v.val
  right_fst : ∀ v, (right v).fst = v.val
  left_ne_right : ∀ v, left v ≠ right v
  left_snd_mem : ∀ v, (left v).snd ∈ verts
  right_snd_mem : ∀ v, (right v).snd ∈ verts
  /-- The reverse of the successor dart is the predecessor at the next
  vertex. -/
  left_right_inv : ∀ v,
    right ⟨(left v).snd, left_snd_mem v⟩ = (left v).symm
  /-- The reverse of the predecessor dart is the successor at the
  previous vertex. -/
  right_left_inv : ∀ v,
    left ⟨(right v).snd, right_snd_mem v⟩ = (right v).symm

namespace CycleCut

variable {M : PlaneMap n} (C : CycleCut M)

/-- Cycle successor. -/
def succ (v : C.verts) : C.verts :=
  ⟨(C.left v).snd, C.left_snd_mem v⟩

/-- Cycle predecessor. -/
def pred (v : C.verts) : C.verts :=
  ⟨(C.right v).snd, C.right_snd_mem v⟩

@[simp]
theorem succ_val (v : C.verts) : (C.succ v).val = (C.left v).snd :=
  rfl

@[simp]
theorem pred_val (v : C.verts) : (C.pred v).val = (C.right v).snd :=
  rfl

end CycleCut

/-- Open `next`-interval of outgoing darts from `src` to `tgt`. -/
def InOpenInterval (M : PlaneMap n) (src tgt d : M.Dart) : Prop :=
  d.fst = src.fst ∧
    ∃ k : ℕ, 0 < k ∧
      (⇑M.rotation.next)^[k] src = d ∧
      ∀ j, 0 < j → j ≤ k → (⇑M.rotation.next)^[j] src ≠ tgt

/-- Left open sector at a cycle vertex. -/
def LeftSector {M : PlaneMap n} (C : CycleCut M) (v : C.verts)
    (d : M.Dart) : Prop :=
  InOpenInterval M (C.left v) (C.right v) d

/-- Right open sector at a cycle vertex. -/
def RightSector {M : PlaneMap n} (C : CycleCut M) (v : C.verts)
    (d : M.Dart) : Prop :=
  InOpenInterval M (C.right v) (C.left v) d

/-- A walk that never meets the given vertex set. -/
def AvoidsVerts {M : PlaneMap n} {u w : Fin n} (q : M.graph.Walk u w)
    (S : Finset (Fin n)) : Prop :=
  ∀ y ∈ q.support, y ∉ S

/-- Off-cycle vertex reachable from a left-sector dart head. -/
def LeftSide {M : PlaneMap n} (C : CycleCut M) (x : Fin n) : Prop :=
  x ∉ C.verts ∧
    ∃ (v : C.verts) (d : M.Dart),
      LeftSector C v d ∧ d.snd ∉ C.verts ∧
        ∃ q : M.graph.Walk d.snd x, AvoidsVerts q C.verts

/-- Off-cycle vertex reachable from a right-sector dart head. -/
def RightSide {M : PlaneMap n} (C : CycleCut M) (x : Fin n) : Prop :=
  x ∉ C.verts ∧
    ∃ (v : C.verts) (d : M.Dart),
      RightSector C v d ∧ d.snd ∉ C.verts ∧
        ∃ q : M.graph.Walk d.snd x, AvoidsVerts q C.verts

/-- The combinatorial two-sides property of a cycle cut. -/
def cycle_two_sides {M : PlaneMap n} (C : CycleCut M) : Prop :=
  (∀ x, x ∉ C.verts → LeftSide C x ∨ RightSide C x) ∧
    (∀ x, ¬ (LeftSide C x ∧ RightSide C x)) ∧
    (∀ x y, ¬ (LeftSide C x ∧ RightSide C y ∧ M.Adj x y)) ∧
    (∀ {x y} (q : M.graph.Walk x y),
      AvoidsVerts q C.verts →
        (LeftSide C x → LeftSide C y) ∧
          (RightSide C x → RightSide C y))

theorem inOpenInterval_fst {M : PlaneMap n} {src tgt d : M.Dart}
    (h : InOpenInterval M src tgt d) : d.fst = src.fst :=
  h.1

theorem inOpenInterval_ne_tgt {M : PlaneMap n} {src tgt d : M.Dart}
    (h : InOpenInterval M src tgt d) : d ≠ tgt := by
  obtain ⟨_, k, hk0, hk, hj⟩ := h
  intro he
  exact hj k hk0 le_rfl (hk.trans he)

theorem inOpenInterval_of_next_ne {M : PlaneMap n} {src tgt : M.Dart}
    (hne : M.rotation.next src ≠ tgt) :
    InOpenInterval M src tgt (M.rotation.next src) :=
  ⟨M.rotation.next_fst src, 1, Nat.one_pos, rfl, fun j hj0 hjle => by
      have : j = 1 := by omega
      subst j
      simpa using hne⟩

theorem not_inOpenInterval_of_next_eq {M : PlaneMap n}
    {src tgt d : M.Dart} (h : M.rotation.next src = tgt) :
    ¬ InOpenInterval M src tgt d := by
  intro ⟨_, k, hk0, _, hj⟩
  exact hj 1 (by omega) (Nat.succ_le_of_lt hk0)
    (by simpa [Function.iterate_one] using h)

theorem leftSide_not_mem {M : PlaneMap n} {C : CycleCut M} {x : Fin n}
    (h : LeftSide C x) : x ∉ C.verts :=
  h.1

theorem rightSide_not_mem {M : PlaneMap n} {C : CycleCut M} {x : Fin n}
    (h : RightSide C x) : x ∉ C.verts :=
  h.1

theorem avoids_append {M : PlaneMap n} {x y z : Fin n}
    {S : Finset (Fin n)} (p : M.graph.Walk x y) (q : M.graph.Walk y z)
    (hp : AvoidsVerts p S) (hq : AvoidsVerts q S) :
    AvoidsVerts (p.append q) S := by
  intro w hw
  rw [mem_support_append_iff] at hw
  rcases hw with hw | hw
  · exact hp w hw
  · exact hq w hw

theorem leftSide_of_leftSector {M : PlaneMap n} (C : CycleCut M)
    (v : C.verts) (d : M.Dart) (h : LeftSector C v d)
    (hs : d.snd ∉ C.verts) : LeftSide C d.snd :=
  ⟨hs, v, d, h, hs, Walk.nil, fun y hy => by
    rw [support_nil, List.mem_singleton] at hy
    subst y
    exact hs⟩

theorem rightSide_of_rightSector {M : PlaneMap n} (C : CycleCut M)
    (v : C.verts) (d : M.Dart) (h : RightSector C v d)
    (hs : d.snd ∉ C.verts) : RightSide C d.snd :=
  ⟨hs, v, d, h, hs, Walk.nil, fun y hy => by
    rw [support_nil, List.mem_singleton] at hy
    subst y
    exact hs⟩

theorem avoiding_walk_stays_left {M : PlaneMap n} (C : CycleCut M)
    {x y : Fin n} (q : M.graph.Walk x y) (hq : AvoidsVerts q C.verts)
    (hx : LeftSide C x) : LeftSide C y := by
  obtain ⟨_, v, d, hd, hs, p, hp⟩ := hx
  exact ⟨hq y (end_mem_support q), v, d, hd, hs, p.append q,
    avoids_append p q hp hq⟩

theorem avoiding_walk_stays_right {M : PlaneMap n} (C : CycleCut M)
    {x y : Fin n} (q : M.graph.Walk x y) (hq : AvoidsVerts q C.verts)
    (hx : RightSide C x) : RightSide C y := by
  obtain ⟨_, v, d, hd, hs, p, hp⟩ := hx
  exact ⟨hq y (end_mem_support q), v, d, hd, hs, p.append q,
    avoids_append p q hp hq⟩

theorem cycleMap_succ_adj (k : ℕ) (v : Fin (k + 3)) :
    (cycleMap k).Adj v (v + 1) := by
  change (cycleMap k).graph.Adj v (v + 1)
  rw [cycleMap_graph, cycleGraph_adj]
  exact Or.inr (add_sub_cancel_left v 1)

theorem cycleMap_pred_adj (k : ℕ) (v : Fin (k + 3)) :
    (cycleMap k).Adj v (v - 1) := by
  change (cycleMap k).graph.Adj v (v - 1)
  rw [cycleMap_graph, cycleGraph_adj]
  exact Or.inl (sub_sub_cancel v 1)

theorem cycleMap_succ_ne_pred (k : ℕ) (v : Fin (k + 3)) :
    v + 1 ≠ v - 1 := by
  intro h
  have h0 : (v + 1 - (v - 1) : Fin (k + 3)) = 0 := by rw [h, sub_self]
  have h2 : (v + 1 - (v - 1) : Fin (k + 3)) = 2 := by abel
  have h20 : (2 : Fin (k + 3)) = 0 := h2.symm.trans h0
  have : (2 : ℕ) = 0 := by
    have hv := congrArg Fin.val h20
    have hmod : (2 : Fin (k + 3)).val = 2 :=
      Nat.mod_eq_of_lt (by omega : 2 < k + 3)
    rw [hmod, Fin.val_zero] at hv
    exact hv
  omega

/-- The Hamilton cycle of `cycleMap k`, oriented by `+1`. -/
noncomputable def cycleMapCut (k : ℕ) : CycleCut (cycleMap k) where
  verts := Finset.univ
  nonempty := ⟨0, Finset.mem_univ 0⟩
  left := fun v => ⟨(v.val, v.val + 1), cycleMap_succ_adj k v.val⟩
  right := fun v => ⟨(v.val, v.val - 1), cycleMap_pred_adj k v.val⟩
  left_fst := fun _ => rfl
  right_fst := fun _ => rfl
  left_ne_right := fun v => by
    intro h
    exact cycleMap_succ_ne_pred k v.val
      (congrArg (fun d : (cycleMap k).Dart => d.snd) h)
  left_snd_mem := fun _ => Finset.mem_univ _
  right_snd_mem := fun _ => Finset.mem_univ _
  left_right_inv := fun v => by
    apply Dart.ext
    apply Prod.ext
    · simp [Dart.symm]
    · simp [Dart.symm, add_sub_cancel]
  right_left_inv := fun v => by
    apply Dart.ext
    apply Prod.ext
    · simp [Dart.symm]
    · simp [Dart.symm, sub_add_cancel]

/-- On `cycleMap`, every vertex lies on the Hamilton cycle. -/
theorem cycleMap_off_cycle_empty (k : ℕ) (x : Fin (k + 3)) :
    x ∈ (cycleMapCut k).verts :=
  Finset.mem_univ x

theorem cycleMap_sides_empty (k : ℕ) (x : Fin (k + 3)) :
    ¬ LeftSide (cycleMapCut k) x ∧ ¬ RightSide (cycleMapCut k) x :=
  ⟨fun h => h.1 (Finset.mem_univ x), fun h => h.1 (Finset.mem_univ x)⟩

/-- Both sides of `cycleMap` are empty, so two-sides is vacuous. -/
theorem cycleMap_cycle_two_sides (k : ℕ) :
    cycle_two_sides (cycleMapCut k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hx (Finset.mem_univ x)).elim
  · intro x h
    exact h.1.1 (Finset.mem_univ x)
  · intro x y h
    exact h.1.1 (Finset.mem_univ x)
  · intro x y q hq
    exact ⟨avoiding_walk_stays_left _ q hq,
      avoiding_walk_stays_right _ q hq⟩

theorem pathGraph_three_adj_zero (w : Fin 3) :
    (pathGraph 3).Adj 0 w ↔ w = 1 := by
  rw [pathGraph_adj]
  constructor
  · intro h
    rcases h with h | h
    · exact Fin.ext h.symm
    · have : w.val < 3 := w.isLt
      omega
  · intro h
    subst w
    exact Or.inl rfl

theorem pathStart_next_fixed :
    (pathMap 2).rotation.next (pathStart 0) = pathStart 0 := by
  have hfst : ((pathMap 2).rotation.next (pathStart 0)).fst = 0 := by
    rw [(pathMap 2).rotation.next_fst, pathStart_fst]
  have hsnd : ((pathMap 2).rotation.next (pathStart 0)).snd = 1 := by
    have hadj := ((pathMap 2).rotation.next (pathStart 0)).adj
    have hadj' : (pathGraph 3).Adj 0
        ((pathMap 2).rotation.next (pathStart 0)).snd := by
      rw [← pathMap_graph 2, ← hfst]
      exact hadj
    exact (pathGraph_three_adj_zero _).1 hadj'
  apply Dart.ext
  exact Prod.ext hfst hsnd

theorem cycleMap_zero_rotation :
    (cycleMap 0).rotation =
      PlaneMapConstruction.split (pathMap 2).rotation
        (pathStart 0) (pathEnd 0) (path_ends_ne 0)
        (path_ends_not_adj 0) :=
  rfl

/-- The dart `0 → 2` of the triangle. -/
noncomputable def cm02 : (cycleMap 0).Dart :=
  ⟨(0, 2), cycleMap_zero_adj (by decide)⟩

/-- The dart `2 → 0` of the triangle. -/
noncomputable def cm20 : (cycleMap 0).Dart :=
  ⟨(2, 0), cycleMap_zero_adj (by decide)⟩

/-- The dart `2 → 1` of the triangle. -/
noncomputable def cm21 : (cycleMap 0).Dart :=
  ⟨(2, 1), cycleMap_zero_adj (by decide)⟩

/-- The dart `1 → 2` of the triangle. -/
noncomputable def cm12 : (cycleMap 0).Dart :=
  (cycleMap 0).rotation.faceNext triDart

theorem triDart_eq_splitOld :
    triDart =
      splitOld (pathStart 0).fst (pathEnd 0).fst (path_ends_ne 0)
        (pathStart 0) := by
  apply Dart.ext
  rfl

theorem cm02_eq_splitOut :
    cm02 =
      splitOut (G := (pathMap 2).graph) (pathStart 0).fst
        (pathEnd 0).fst (path_ends_ne 0) := by
  apply Dart.ext
  rfl

theorem cm20_eq_splitBack :
    cm20 =
      splitBack (G := (pathMap 2).graph) (pathStart 0).fst
        (pathEnd 0).fst (path_ends_ne 0) := by
  apply Dart.ext
  rfl

theorem cm21_eq_splitOld_pathEnd :
    cm21 =
      splitOld (pathStart 0).fst (pathEnd 0).fst (path_ends_ne 0)
        (pathEnd 0) := by
  apply Dart.ext
  rfl

theorem fin3_ne_zero {z : Fin 3} (hz : z ≠ 0) : z = 1 ∨ z = 2 := by
  have hlt : z.val < 3 := z.isLt
  have hne : z.val ≠ 0 := fun h => hz (Fin.ext h)
  have : z.val = 1 ∨ z.val = 2 := by omega
  rcases this with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem fin3_ne_one {z : Fin 3} (hz : z ≠ 1) : z = 0 ∨ z = 2 := by
  have hlt : z.val < 3 := z.isLt
  have hne : z.val ≠ 1 := fun h => hz (Fin.ext h)
  have : z.val = 0 ∨ z.val = 2 := by omega
  rcases this with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem fin3_ne_two {z : Fin 3} (hz : z ≠ 2) : z = 0 ∨ z = 1 := by
  have hlt : z.val < 3 := z.isLt
  have hne : z.val ≠ 2 := fun h => hz (Fin.ext h)
  have : z.val = 0 ∨ z.val = 1 := by omega
  rcases this with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem cycleMap_zero_darts_at_zero (d : (cycleMap 0).Dart)
    (hd : d.fst = 0) : d = triDart ∨ d = cm02 := by
  have hne : d.snd ≠ 0 := fun h => d.fst_ne_snd (hd.trans h.symm)
  rcases fin3_ne_zero hne with h | h
  · left
    apply Dart.ext
    exact Prod.ext hd h
  · right
    apply Dart.ext
    exact Prod.ext hd h

theorem cycleMap_zero_darts_at_one (d : (cycleMap 0).Dart)
    (hd : d.fst = 1) : d = triDart.symm ∨ d = cm12 := by
  have hne : d.snd ≠ 1 := fun h => d.fst_ne_snd (hd.trans h.symm)
  rcases fin3_ne_one hne with h | h
  · left
    apply Dart.ext
    apply Prod.ext
    · rw [hd]
      rfl
    · rw [h]
      rfl
  · right
    apply Dart.ext
    apply Prod.ext
    · exact hd.trans faceNext_triDart_fst.symm
    · exact h.trans faceNext_triDart_snd.symm

theorem cycleMap_zero_darts_at_two (d : (cycleMap 0).Dart)
    (hd : d.fst = 2) : d = cm20 ∨ d = cm21 := by
  have hne : d.snd ≠ 2 := fun h => d.fst_ne_snd (hd.trans h.symm)
  rcases fin3_ne_two hne with h | h
  · left
    apply Dart.ext
    exact Prod.ext hd h
  · right
    apply Dart.ext
    exact Prod.ext hd h

theorem cycleMap_next_triDart :
    (cycleMap 0).rotation.next triDart = cm02 := by
  rw [cycleMap_zero_rotation, triDart_eq_splitOld, cm02_eq_splitOut]
  change (PlaneMapConstruction.split (pathMap 2).rotation
      (pathStart 0) (pathEnd 0) (path_ends_ne 0)
      (path_ends_not_adj 0)).next
    (splitDartEquiv (G := (pathMap 2).graph) (pathStart 0).fst
      (pathEnd 0).fst (path_ends_ne 0) (path_ends_not_adj 0)
      (.inl (pathStart 0))) =
    splitDartEquiv (G := (pathMap 2).graph) (pathStart 0).fst
      (pathEnd 0).fst (path_ends_ne 0) (path_ends_not_adj 0)
      (.inr false)
  rw [split_next_apply, split_next_old, pathStart_next_fixed]
  simp

theorem cycleMap_next_cm02 :
    (cycleMap 0).rotation.next cm02 = triDart := by
  have hne : (cycleMap 0).rotation.next cm02 ≠ cm02 := by
    intro h
    have h' : (cycleMap 0).rotation.next cm02 =
        (cycleMap 0).rotation.next triDart :=
      h.trans cycleMap_next_triDart.symm
    exact (by decide : (2 : Fin 3) ≠ 1)
      (congrArg (fun x : (cycleMap 0).Dart => x.snd)
        ((cycleMap 0).rotation.next.injective h'))
  have hfst : ((cycleMap 0).rotation.next cm02).fst = 0 := by
    rw [(cycleMap 0).rotation.next_fst]
    rfl
  rcases cycleMap_zero_darts_at_zero _ hfst with h | h
  · exact h
  · exact (hne h).elim

theorem cycleMap_next_10 :
    (cycleMap 0).rotation.next triDart.symm = cm12 :=
  (RotationSystem.face_next_apply _ _).symm

theorem cycleMap_next_12 :
    (cycleMap 0).rotation.next cm12 = triDart.symm := by
  have hne : (cycleMap 0).rotation.next cm12 ≠ cm12 := by
    intro h
    have heq : cm12 = triDart.symm :=
      (cycleMap 0).rotation.next.injective (h.trans cycleMap_next_10.symm)
    exact (by decide : (2 : Fin 3) ≠ 0)
      (faceNext_triDart_snd.symm.trans
        (congrArg (fun x : (cycleMap 0).Dart => x.snd) heq))
  have hfst : ((cycleMap 0).rotation.next cm12).fst = 1 := by
    rw [(cycleMap 0).rotation.next_fst]
    exact faceNext_triDart_fst
  rcases cycleMap_zero_darts_at_one _ hfst with h | h
  · exact h
  · exact (hne h).elim

theorem cycleMap_next_20 :
    (cycleMap 0).rotation.next cm20 = cm21 := by
  rw [cycleMap_zero_rotation, cm20_eq_splitBack, cm21_eq_splitOld_pathEnd]
  change (PlaneMapConstruction.split (pathMap 2).rotation
      (pathStart 0) (pathEnd 0) (path_ends_ne 0)
      (path_ends_not_adj 0)).next
    (splitDartEquiv (G := (pathMap 2).graph) (pathStart 0).fst
      (pathEnd 0).fst (path_ends_ne 0) (path_ends_not_adj 0)
      (.inr true)) =
    splitDartEquiv (G := (pathMap 2).graph) (pathStart 0).fst
      (pathEnd 0).fst (path_ends_ne 0) (path_ends_not_adj 0)
      (.inl (pathEnd 0))
  rw [split_next_apply, split_next_back]

theorem cycleMap_next_21 :
    (cycleMap 0).rotation.next cm21 = cm20 := by
  have hne : (cycleMap 0).rotation.next cm21 ≠ cm21 := by
    intro h
    have heq : cm21 = cm20 :=
      (cycleMap 0).rotation.next.injective (h.trans cycleMap_next_20.symm)
    exact (by decide : (1 : Fin 3) ≠ 0)
      (congrArg (fun x : (cycleMap 0).Dart => x.snd) heq)
  have hfst : ((cycleMap 0).rotation.next cm21).fst = 2 := by
    rw [(cycleMap 0).rotation.next_fst]
    rfl
  rcases cycleMap_zero_darts_at_two _ hfst with h | h
  · exact h
  · exact (hne h).elim

theorem faceNext_sq_triDart :
    (cycleMap 0).rotation.faceNext cm12 = cm20 := by
  rw [RotationSystem.face_next_apply]
  have hsymm : cm12.symm = cm21 := by
    apply Dart.ext
    exact Prod.ext faceNext_triDart_snd faceNext_triDart_fst
  rw [hsymm, cycleMap_next_21]

noncomputable def tgOld (d : (cycleMap 0).Dart) : tetGrow.Dart :=
  growOld (H := (cycleMap 0).graph) 0 d

noncomputable def tgOut : tetGrow.Dart :=
  growOut (H := (cycleMap 0).graph) 0

noncomputable def tsOld (d : tetGrow.Dart) : tetSplit.Dart :=
  splitOld tetBack.fst tetAt1.fst tet_fst_ne d

noncomputable def thOld (d : tetSplit.Dart) : tetrahedron.Dart :=
  splitOld tetOut.fst tetAt2.fst tet_second_fst_ne d

theorem tetGrow_next_old (d : (cycleMap 0).Dart) :
    tetGrow.rotation.next (tgOld d) =
      if (cycleMap 0).rotation.next d = triDart then tgOut
      else tgOld ((cycleMap 0).rotation.next d) := by
  rw [tetGrow_rotation]
  change (growBefore 0 (cycleMap 0).rotation triDart triDart_fst).next
      (growDartEquiv (H := (cycleMap 0).graph) 0 (.inl d)) = _
  rw [grow_before_next_apply, grow_before_next_old]
  split_ifs <;> rfl

theorem tetGrow_next_old_ne {d : (cycleMap 0).Dart}
    (hne : (cycleMap 0).rotation.next d ≠ triDart) :
    tetGrow.rotation.next (tgOld d) =
      tgOld ((cycleMap 0).rotation.next d) := by
  rw [tetGrow_next_old, ite_eq_right hne]

theorem cycleMap_next_ne_triDart_of_fst {d : (cycleMap 0).Dart}
    (hd : d.fst ≠ 0) :
    (cycleMap 0).rotation.next d ≠ triDart := by
  intro h
  have hs := congrArg (fun x : (cycleMap 0).Dart => x.fst) h
  rw [(cycleMap 0).rotation.next_fst] at hs
  exact hd (hs.trans triDart_fst)

theorem tetGrow_next_off_zero {d : (cycleMap 0).Dart} (hd : d.fst ≠ 0) :
    tetGrow.rotation.next (tgOld d) =
      tgOld ((cycleMap 0).rotation.next d) :=
  tetGrow_next_old_ne (cycleMap_next_ne_triDart_of_fst hd)

theorem tetSplit_next_old (d : tetGrow.Dart) :
    tetSplit.rotation.next (tsOld d) =
      if tetGrow.rotation.next d = tetBack then
        splitOut (G := tetGrow.graph) tetBack.fst tetAt1.fst tet_fst_ne
      else if tetGrow.rotation.next d = tetAt1 then
        splitBack tetBack.fst tetAt1.fst tet_fst_ne
      else tsOld (tetGrow.rotation.next d) := by
  rw [tetSplit_rotation]
  change (PlaneMapConstruction.split tetGrow.rotation tetBack tetAt1
      tet_fst_ne tet_not_adj).next
    (splitDartEquiv (G := tetGrow.graph) tetBack.fst tetAt1.fst
      tet_fst_ne tet_not_adj (.inl d)) = _
  rw [split_next_apply, split_next_old]
  by_cases h1 : tetGrow.rotation.next d = tetBack
  · simp only [h1, ↓reduceIte]
    rfl
  · have hneAB : tetAt1 ≠ tetBack := by
      intro h
      exact (by decide : (1 : Fin 4) ≠ 3)
        (tetAt1_fst.symm.trans
          ((congrArg (fun x : tetGrow.Dart => x.fst) h).trans tetBack_fst))
    by_cases h2 : tetGrow.rotation.next d = tetAt1
    · simp only [h2, hneAB, ↓reduceIte]
      rfl
    · simp only [h1, h2, ↓reduceIte]
      rfl

theorem tetrahedron_rotation :
    tetrahedron.rotation =
      PlaneMapConstruction.split tetSplit.rotation tetOut tetAt2
        tet_second_fst_ne tet_second_not_adj :=
  rfl

theorem tetrahedron_next_old (d : tetSplit.Dart) :
    tetrahedron.rotation.next (thOld d) =
      if tetSplit.rotation.next d = tetOut then
        splitOut (G := tetSplit.graph) tetOut.fst tetAt2.fst
          tet_second_fst_ne
      else if tetSplit.rotation.next d = tetAt2 then
        splitBack tetOut.fst tetAt2.fst tet_second_fst_ne
      else thOld (tetSplit.rotation.next d) := by
  rw [tetrahedron_rotation]
  change (PlaneMapConstruction.split tetSplit.rotation tetOut tetAt2
      tet_second_fst_ne tet_second_not_adj).next
    (splitDartEquiv (G := tetSplit.graph) tetOut.fst tetAt2.fst
      tet_second_fst_ne tet_second_not_adj (.inl d)) = _
  rw [split_next_apply, split_next_old]
  by_cases h1 : tetSplit.rotation.next d = tetOut
  · simp only [h1, ↓reduceIte]
    rfl
  · have hneAB : tetAt2 ≠ tetOut := by
      intro h
      exact (by decide : (2 : Fin 4) ≠ 3)
        (tetAt2_fst.symm.trans
          ((congrArg (fun x : tetSplit.Dart => x.fst) h).trans tetOut_fst))
    by_cases h2 : tetSplit.rotation.next d = tetAt2
    · simp only [h2, hneAB, ↓reduceIte]
      rfl
    · simp only [h1, h2, ↓reduceIte]
      rfl

theorem tetSplit_next_at_zero (d : tetGrow.Dart) (hd : d.fst = 0) :
    tetSplit.rotation.next (tsOld d) =
      tsOld (tetGrow.rotation.next d) := by
  rw [tetSplit_next_old]
  have hn1 : tetGrow.rotation.next d ≠ tetBack := by
    intro h
    have hs := congrArg (fun x : tetGrow.Dart => x.fst) h
    rw [tetGrow.rotation.next_fst, hd, tetBack_fst] at hs
    exact (by decide : (0 : Fin 4) ≠ 3) hs
  have hn2 : tetGrow.rotation.next d ≠ tetAt1 := by
    intro h
    have hs := congrArg (fun x : tetGrow.Dart => x.fst) h
    rw [tetGrow.rotation.next_fst, hd, tetAt1_fst] at hs
    exact (by decide : (0 : Fin 4) ≠ 1) hs
  rw [ite_eq_right hn1]
  exact ite_eq_right hn2

theorem tetrahedron_next_at_zero (d : tetSplit.Dart) (hd : d.fst = 0) :
    tetrahedron.rotation.next (thOld d) =
      thOld (tetSplit.rotation.next d) := by
  rw [tetrahedron_next_old]
  have hn1 : tetSplit.rotation.next d ≠ tetOut := by
    intro h
    have hs := congrArg (fun x : tetSplit.Dart => x.fst) h
    rw [tetSplit.rotation.next_fst, hd, tetOut_fst] at hs
    exact (by decide : (0 : Fin 4) ≠ 3) hs
  have hn2 : tetSplit.rotation.next d ≠ tetAt2 := by
    intro h
    have hs := congrArg (fun x : tetSplit.Dart => x.fst) h
    rw [tetSplit.rotation.next_fst, hd, tetAt2_fst] at hs
    exact (by decide : (0 : Fin 4) ≠ 2) hs
  rw [ite_eq_right hn1]
  exact ite_eq_right hn2

theorem tetrahedron_next_at_one (d : tetSplit.Dart) (hd : d.fst = 1) :
    tetrahedron.rotation.next (thOld d) =
      thOld (tetSplit.rotation.next d) := by
  rw [tetrahedron_next_old]
  have hn1 : tetSplit.rotation.next d ≠ tetOut := by
    intro h
    have hs := congrArg (fun x : tetSplit.Dart => x.fst) h
    rw [tetSplit.rotation.next_fst, hd, tetOut_fst] at hs
    exact (by decide : (1 : Fin 4) ≠ 3) hs
  have hn2 : tetSplit.rotation.next d ≠ tetAt2 := by
    intro h
    have hs := congrArg (fun x : tetSplit.Dart => x.fst) h
    rw [tetSplit.rotation.next_fst, hd, tetAt2_fst] at hs
    exact (by decide : (1 : Fin 4) ≠ 2) hs
  rw [ite_eq_right hn1]
  exact ite_eq_right hn2

theorem tgOld_fst (d : (cycleMap 0).Dart) :
    (tgOld d).fst = d.fst.castSucc :=
  rfl

theorem tgOld_snd (d : (cycleMap 0).Dart) :
    (tgOld d).snd = d.snd.castSucc :=
  rfl

theorem tsOld_fst (d : tetGrow.Dart) : (tsOld d).fst = d.fst := rfl

theorem tsOld_snd (d : tetGrow.Dart) : (tsOld d).snd = d.snd := rfl

theorem thOld_fst (d : tetSplit.Dart) : (thOld d).fst = d.fst := rfl

theorem thOld_snd (d : tetSplit.Dart) : (thOld d).snd = d.snd := rfl

theorem cm02_fst : cm02.fst = 0 := rfl
theorem cm02_snd : cm02.snd = 2 := rfl
theorem cm20_fst : cm20.fst = 2 := rfl
theorem cm20_snd : cm20.snd = 0 := rfl
theorem cm21_fst : cm21.fst = 2 := rfl
theorem cm21_snd : cm21.snd = 1 := rfl

theorem tetSplit_next_off (d : tetGrow.Dart)
    (hB : tetGrow.rotation.next d ≠ tetBack)
    (hA : tetGrow.rotation.next d ≠ tetAt1) :
    tetSplit.rotation.next (tsOld d) = tsOld (tetGrow.rotation.next d) := by
  rw [tetSplit_next_old, ite_eq_right hB]
  exact ite_eq_right hA

theorem tetrahedron_next_off (d : tetSplit.Dart)
    (hO : tetSplit.rotation.next d ≠ tetOut)
    (hA : tetSplit.rotation.next d ≠ tetAt2) :
    tetrahedron.rotation.next (thOld d) = thOld (tetSplit.rotation.next d) := by
  rw [tetrahedron_next_old, ite_eq_right hO]
  exact ite_eq_right hA

theorem tetrahedron_next_01 :
    tetrahedron.rotation.next (thOld (tsOld (tgOld triDart))) =
      thOld (tsOld (tgOld cm02)) := by
  have h0 : (tsOld (tgOld triDart)).fst = 0 := by
    rw [tsOld_fst, tgOld_fst, triDart_fst]
    rfl
  rw [tetrahedron_next_at_zero _ h0]
  have h0' : (tgOld triDart).fst = 0 := by
    rw [tgOld_fst, triDart_fst]
    rfl
  rw [tetSplit_next_at_zero _ h0']
  have hne : (cycleMap 0).rotation.next triDart ≠ triDart := by
    rw [cycleMap_next_triDart]
    intro h
    exact (by decide : (2 : Fin 3) ≠ 1)
      (congrArg (fun x : (cycleMap 0).Dart => x.snd) h)
  rw [tetGrow_next_old, ite_eq_right hne, cycleMap_next_triDart]

theorem tetrahedron_next_02 :
    tetrahedron.rotation.next (thOld (tsOld (tgOld cm02))) =
      thOld (tsOld tgOut) := by
  have h0 : (tsOld (tgOld cm02)).fst = 0 := by
    rw [tsOld_fst, tgOld_fst]
    rfl
  rw [tetrahedron_next_at_zero _ h0]
  have h0' : (tgOld cm02).fst = 0 := by
    rw [tgOld_fst]
    rfl
  rw [tetSplit_next_at_zero _ h0', tetGrow_next_old,
    ite_eq_left cycleMap_next_cm02]

theorem tetAt1_eq_tgOld : tetAt1 = tgOld cm12 := rfl

theorem tetSplit_next_12 :
    tetSplit.rotation.next (tsOld tetAt1) =
      tsOld (tgOld triDart.symm) := by
  have hf : cm12.fst ≠ 0 := by
    change ((cycleMap 0).rotation.faceNext triDart).fst ≠ 0
    rw [faceNext_triDart_fst]
    decide
  have hnext : tetGrow.rotation.next tetAt1 = tgOld triDart.symm := by
    rw [tetAt1_eq_tgOld, tetGrow_next_off_zero hf, cycleMap_next_12]
  have hnB : tetGrow.rotation.next tetAt1 ≠ tetBack := by
    intro h
    have hs := congrArg (fun x : tetGrow.Dart => x.fst) h
    rw [tetGrow.rotation.next_fst, tetAt1_fst, tetBack_fst] at hs
    exact (by decide : (1 : Fin 4) ≠ 3) hs
  have hnA : tetGrow.rotation.next tetAt1 ≠ tetAt1 := by
    rw [hnext]
    intro h
    have hs := congrArg (fun x : tetGrow.Dart => x.snd) h
    have h0 : (tgOld triDart.symm).snd = 0 := by
      rw [tgOld_snd]
      change triDart.fst.castSucc = 0
      rw [triDart_fst]
      rfl
    rw [h0, tetAt1_snd] at hs
    exact (by decide : (0 : Fin 4) ≠ 2) hs
  rw [tetSplit_next_off _ hnB hnA]
  exact congrArg tsOld hnext

theorem tetrahedron_next_12 :
    tetrahedron.rotation.next (thOld (tsOld tetAt1)) =
      thOld (tsOld (tgOld triDart.symm)) := by
  have h1 : (tsOld tetAt1).fst = 1 := tetAt1_fst
  rw [tetrahedron_next_at_one _ h1, tetSplit_next_12]

theorem tetAt2_eq : tetAt2 = tsOld (tgOld cm20) := by
  change splitOld tetBack.fst tetAt1.fst tet_fst_ne
      (growOld 0 ((cycleMap 0).rotation.faceNext
        ((cycleMap 0).rotation.faceNext triDart))) =
    tsOld (tgOld cm20)
  have h : (cycleMap 0).rotation.faceNext cm12 = cm20 :=
    faceNext_sq_triDart
  change splitOld tetBack.fst tetAt1.fst tet_fst_ne
      (growOld 0 ((cycleMap 0).rotation.faceNext cm12)) =
    tsOld (tgOld cm20)
  rw [h]
  rfl

theorem tetSplit_next_20 :
    tetSplit.rotation.next tetAt2 = tsOld (tgOld cm21) := by
  have hf : cm20.fst ≠ 0 := by
    rw [cm20_fst]
    decide
  have hnext : tetGrow.rotation.next (tgOld cm20) = tgOld cm21 := by
    rw [tetGrow_next_off_zero hf, cycleMap_next_20]
  have hnB : tetGrow.rotation.next (tgOld cm20) ≠ tetBack := by
    intro h
    have hs := congrArg (fun x : tetGrow.Dart => x.fst) h
    rw [tetGrow.rotation.next_fst, tgOld_fst, cm20_fst, tetBack_fst] at hs
    exact (by decide : (2 : Fin 3).castSucc ≠ (3 : Fin 4)) hs
  have hnA : tetGrow.rotation.next (tgOld cm20) ≠ tetAt1 := by
    intro h
    have hs := congrArg (fun x : tetGrow.Dart => x.fst) h
    rw [tetGrow.rotation.next_fst, tgOld_fst, cm20_fst, tetAt1_fst] at hs
    exact (by decide : (2 : Fin 3).castSucc ≠ (1 : Fin 4)) hs
  rw [tetAt2_eq, tetSplit_next_off _ hnB hnA]
  exact congrArg tsOld hnext

theorem tetrahedron_next_20 :
    tetrahedron.rotation.next (thOld tetAt2) =
      thOld (tsOld (tgOld cm21)) := by
  have hnext := tetSplit_next_20
  have hn1 : tetSplit.rotation.next tetAt2 ≠ tetOut := by
    rw [hnext]
    intro h
    have hs := congrArg (fun x : tetSplit.Dart => x.fst) h
    rw [tsOld_fst, tgOld_fst, cm21_fst, tetOut_fst] at hs
    exact (by decide : (2 : Fin 3).castSucc ≠ (3 : Fin 4)) hs
  have hn2 : tetSplit.rotation.next tetAt2 ≠ tetAt2 := by
    rw [hnext]
    intro h
    have hs := congrArg (fun x : tetSplit.Dart => x.snd) h
    have h1 : (tsOld (tgOld cm21)).snd = 1 := by
      rw [tsOld_snd, tgOld_snd, cm21_snd]
      rfl
    have h0 : tetAt2.snd = 0 := by
      rw [tetAt2_eq, tsOld_snd, tgOld_snd, cm20_snd]
      rfl
    rw [h1, h0] at hs
    exact (by decide : (1 : Fin 4) ≠ 0) hs
  rw [tetrahedron_next_off _ hn1 hn2]
  exact congrArg thOld hnext

theorem tet_adj {i j : Fin 4} (h : i ≠ j) : tetrahedron.graph.Adj i j :=
  tetrahedron_graph ▸ h

theorem tet_th_01 :
    (⟨(0, 1), tet_adj (by decide)⟩ : tetrahedron.Dart) =
      thOld (tsOld (tgOld triDart)) := by
  apply Dart.ext
  rfl

theorem tet_th_02 :
    (⟨(0, 2), tet_adj (by decide)⟩ : tetrahedron.Dart) =
      thOld (tsOld (tgOld cm02)) := by
  apply Dart.ext
  rfl

theorem tet_th_03 :
    (⟨(0, 3), tet_adj (by decide)⟩ : tetrahedron.Dart) =
      thOld (tsOld tgOut) := by
  apply Dart.ext
  rfl

theorem tet_th_12 :
    (⟨(1, 2), tet_adj (by decide)⟩ : tetrahedron.Dart) =
      thOld (tsOld tetAt1) := by
  apply Dart.ext
  apply Prod.ext
  · change (1 : Fin 4) = (thOld (tsOld tetAt1)).fst
    rw [thOld_fst, tsOld_fst, tetAt1_fst]
  · change (2 : Fin 4) = (thOld (tsOld tetAt1)).snd
    rw [thOld_snd, tsOld_snd, tetAt1_snd]

theorem tet_th_10 :
    (⟨(1, 0), tet_adj (by decide)⟩ : tetrahedron.Dart) =
      thOld (tsOld (tgOld triDart.symm)) := by
  apply Dart.ext
  rfl

theorem tet_th_20 :
    (⟨(2, 0), tet_adj (by decide)⟩ : tetrahedron.Dart) =
      thOld tetAt2 := by
  apply Dart.ext
  apply Prod.ext
  · exact tetAt2_fst.symm
  · rw [tetAt2_eq]
    simp [thOld, tsOld, tgOld, growOld, splitOld, cm20]

theorem tet_th_21 :
    (⟨(2, 1), tet_adj (by decide)⟩ : tetrahedron.Dart) =
      thOld (tsOld (tgOld cm21)) := by
  apply Dart.ext
  rfl

def tetFaceVerts : Finset (Fin 4) := {0, 1, 2}

@[simp] theorem mem_tetFace_zero : (0 : Fin 4) ∈ tetFaceVerts :=
  Finset.mem_insert_self _ _

@[simp] theorem mem_tetFace_one : (1 : Fin 4) ∈ tetFaceVerts :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

@[simp] theorem mem_tetFace_two : (2 : Fin 4) ∈ tetFaceVerts :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_singleton_self _))

@[simp] theorem not_mem_tetFace_three : (3 : Fin 4) ∉ tetFaceVerts := by
  simp [tetFaceVerts]

def tetSucc (v : Fin 4) : Fin 4 :=
  if v = 0 then 1 else if v = 1 then 2 else 0

def tetPred (v : Fin 4) : Fin 4 :=
  if v = 0 then 2 else if v = 1 then 0 else 1

theorem mem_tetFaceVerts {v : Fin 4} :
    v ∈ tetFaceVerts ↔ v = 0 ∨ v = 1 ∨ v = 2 := by
  simp [tetFaceVerts]

theorem tet_mem_of_mem {v : Fin 4} (hv : v ∈ tetFaceVerts) :
    v = 0 ∨ v = 1 ∨ v = 2 :=
  mem_tetFaceVerts.1 hv

theorem tetSucc_ne {v : Fin 4} (hv : v ∈ tetFaceVerts) :
    v ≠ tetSucc v := by
  rcases tet_mem_of_mem hv with h | h | h <;> subst h <;> decide

theorem tetPred_ne {v : Fin 4} (hv : v ∈ tetFaceVerts) :
    v ≠ tetPred v := by
  rcases tet_mem_of_mem hv with h | h | h <;> subst h <;> decide

theorem tetSucc_ne_pred {v : Fin 4} (hv : v ∈ tetFaceVerts) :
    tetSucc v ≠ tetPred v := by
  rcases tet_mem_of_mem hv with h | h | h <;> subst h <;> decide

theorem tetSucc_mem {v : Fin 4} (hv : v ∈ tetFaceVerts) :
    tetSucc v ∈ tetFaceVerts := by
  rcases tet_mem_of_mem hv with h | h | h <;> subst h <;>
    simp [tetSucc, tetFaceVerts]

theorem tetPred_mem {v : Fin 4} (hv : v ∈ tetFaceVerts) :
    tetPred v ∈ tetFaceVerts := by
  rcases tet_mem_of_mem hv with h | h | h <;> subst h <;>
    simp [tetPred, tetFaceVerts]

theorem tetPred_succ {v : Fin 4} (hv : v ∈ tetFaceVerts) :
    tetPred (tetSucc v) = v := by
  rcases tet_mem_of_mem hv with h | h | h <;> subst h <;> decide

theorem tetSucc_pred {v : Fin 4} (hv : v ∈ tetFaceVerts) :
    tetSucc (tetPred v) = v := by
  rcases tet_mem_of_mem hv with h | h | h <;> subst h <;> decide

/-- Facial 3-cycle `0 → 1 → 2 → 0` of the tetrahedron. -/
noncomputable def tetFaceCut : CycleCut tetrahedron where
  verts := tetFaceVerts
  nonempty := ⟨0, mem_tetFace_zero⟩
  left := fun v =>
    ⟨(v.val, tetSucc v.val), tet_adj (tetSucc_ne v.property)⟩
  right := fun v =>
    ⟨(v.val, tetPred v.val), tet_adj (tetPred_ne v.property)⟩
  left_fst := fun _ => rfl
  right_fst := fun _ => rfl
  left_ne_right := fun v => by
    intro h
    exact tetSucc_ne_pred v.property
      (congrArg (fun d : tetrahedron.Dart => d.snd) h)
  left_snd_mem := fun v => tetSucc_mem v.property
  right_snd_mem := fun v => tetPred_mem v.property
  left_right_inv := fun v => by
    apply Dart.ext
    apply Prod.ext
    · simp [Dart.symm]
    · simp [Dart.symm, tetPred_succ v.property]
  right_left_inv := fun v => by
    apply Dart.ext
    apply Prod.ext
    · simp [Dart.symm]
    · simp [Dart.symm, tetSucc_pred v.property]

theorem tetFaceCut_left_zero :
    tetFaceCut.left ⟨0, mem_tetFace_zero⟩ =
      ⟨(0, 1), tet_adj (by decide)⟩ :=
  Dart.ext _ _ rfl

theorem tetFaceCut_right_zero :
    tetFaceCut.right ⟨0, mem_tetFace_zero⟩ =
      ⟨(0, 2), tet_adj (by decide)⟩ :=
  Dart.ext _ _ rfl

theorem tetFaceCut_left_one :
    tetFaceCut.left ⟨1, mem_tetFace_one⟩ =
      ⟨(1, 2), tet_adj (by decide)⟩ :=
  Dart.ext _ _ rfl

theorem tetFaceCut_right_one :
    tetFaceCut.right ⟨1, mem_tetFace_one⟩ =
      ⟨(1, 0), tet_adj (by decide)⟩ :=
  Dart.ext _ _ rfl

theorem tetFaceCut_left_two :
    tetFaceCut.left ⟨2, mem_tetFace_two⟩ =
      ⟨(2, 0), tet_adj (by decide)⟩ :=
  Dart.ext _ _ rfl

theorem tetFaceCut_right_two :
    tetFaceCut.right ⟨2, mem_tetFace_two⟩ =
      ⟨(2, 1), tet_adj (by decide)⟩ :=
  Dart.ext _ _ rfl

theorem tetrahedron_next_left_zero :
    tetrahedron.rotation.next
        (tetFaceCut.left ⟨0, mem_tetFace_zero⟩) =
      tetFaceCut.right ⟨0, mem_tetFace_zero⟩ := by
  rw [tetFaceCut_left_zero, tetFaceCut_right_zero, tet_th_01, tet_th_02]
  exact tetrahedron_next_01

theorem tetrahedron_next_left_one :
    tetrahedron.rotation.next
        (tetFaceCut.left ⟨1, mem_tetFace_one⟩) =
      tetFaceCut.right ⟨1, mem_tetFace_one⟩ := by
  rw [tetFaceCut_left_one, tetFaceCut_right_one, tet_th_12, tet_th_10]
  exact tetrahedron_next_12

theorem tetrahedron_next_left_two :
    tetrahedron.rotation.next
        (tetFaceCut.left ⟨2, mem_tetFace_two⟩) =
      tetFaceCut.right ⟨2, mem_tetFace_two⟩ := by
  rw [tetFaceCut_left_two, tetFaceCut_right_two, tet_th_20, tet_th_21]
  exact tetrahedron_next_20

theorem tetrahedron_next_right_zero :
    tetrahedron.rotation.next
        (tetFaceCut.right ⟨0, mem_tetFace_zero⟩) =
      ⟨(0, 3), tet_adj (by decide)⟩ := by
  rw [tetFaceCut_right_zero, tet_th_02, tet_th_03]
  exact tetrahedron_next_02

theorem tetrahedron_leftSector_empty (v : tetFaceCut.verts)
    (d : tetrahedron.Dart) : ¬ LeftSector tetFaceCut v d := by
  rcases tet_mem_of_mem v.property with h | h | h
  · have hv : v = ⟨0, mem_tetFace_zero⟩ := Subtype.ext h
    rw [hv]
    exact not_inOpenInterval_of_next_eq tetrahedron_next_left_zero
  · have hv : v = ⟨1, mem_tetFace_one⟩ := Subtype.ext h
    rw [hv]
    exact not_inOpenInterval_of_next_eq tetrahedron_next_left_one
  · have hv : v = ⟨2, mem_tetFace_two⟩ := Subtype.ext h
    rw [hv]
    exact not_inOpenInterval_of_next_eq tetrahedron_next_left_two

theorem tetrahedron_not_leftSide (x : Fin 4) : ¬ LeftSide tetFaceCut x := by
  intro h
  obtain ⟨_, v, d, hd, _⟩ := h
  exact tetrahedron_leftSector_empty v d hd

theorem tetrahedron_off_eq_three {x : Fin 4} (hx : x ∉ tetFaceVerts) :
    x = 3 := by
  by_contra hx3
  rcases fin4_of_ne_last hx3 with h | h | h <;> subst x <;>
    exact hx (by simp)

theorem tetrahedron_rightSide_three : RightSide tetFaceCut 3 := by
  let v : tetFaceCut.verts := ⟨0, mem_tetFace_zero⟩
  have d03 :
      tetrahedron.rotation.next (tetFaceCut.right v) =
        ⟨(0, 3), tet_adj (by decide)⟩ :=
    tetrahedron_next_right_zero
  have hne :
      tetrahedron.rotation.next (tetFaceCut.right v) ≠
        tetFaceCut.left v := by
    rw [d03, tetFaceCut_left_zero]
    intro h
    exact (by decide : (3 : Fin 4) ≠ 1)
      (congrArg (fun x : tetrahedron.Dart => x.snd) h)
  have hsec : RightSector tetFaceCut v
      ⟨(0, 3), tet_adj (by decide)⟩ := by
    rw [← d03]
    exact inOpenInterval_of_next_ne hne
  exact rightSide_of_rightSector tetFaceCut v
    ⟨(0, 3), tet_adj (by decide)⟩ hsec not_mem_tetFace_three

/-- On a facial triangle of the tetrahedron the leftover vertex occupies
exactly the right side; the left side is empty, so there is no cross
edge. -/
theorem tetrahedron_face_sides :
    (3 : Fin 4) ∉ tetFaceCut.verts ∧
      RightSide tetFaceCut 3 ∧
      (∀ x, ¬ LeftSide tetFaceCut x) ∧
      (∀ x y, ¬ (LeftSide tetFaceCut x ∧ RightSide tetFaceCut y ∧
        tetrahedron.Adj x y)) ∧
      cycle_two_sides tetFaceCut := by
  refine ⟨not_mem_tetFace_three, tetrahedron_rightSide_three,
    tetrahedron_not_leftSide, ?_, ?_⟩
  · intro x y h
    exact tetrahedron_not_leftSide x h.1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      exact Or.inr (by
        have hx3 : x = 3 := tetrahedron_off_eq_three hx
        subst x
        exact tetrahedron_rightSide_three)
    · intro x h
      exact tetrahedron_not_leftSide x h.1
    · intro x y h
      exact tetrahedron_not_leftSide x h.1
    · intro x y q hq
      exact ⟨avoiding_walk_stays_left _ q hq,
        avoiding_walk_stays_right _ q hq⟩

end PlaneMap

end SimpleGraph
