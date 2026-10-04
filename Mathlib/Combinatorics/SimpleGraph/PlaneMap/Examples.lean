/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Constructor checks

The cycle of length `n + 3` is built from `PlaneMap.vertex`, `grow`, and
`split`. The tetrahedron is the complete graph on `Fin 4`, with six edges
and four faces.
-/

@[expose] public section

namespace SimpleGraph

open PlaneMapConstruction

namespace PlaneMap

theorem pathGraph_one_eq_bot : pathGraph 1 = ⊥ := by
  ext u v
  fin_cases u
  fin_cases v
  simp [pathGraph_adj, bot_adj]

theorem growGraph_pathGraph (n : ℕ) :
    growGraph (pathGraph (n + 1)) (Fin.last n) = pathGraph (n + 2) := by
  ext x y
  cases x using Fin.lastCases with
  | last =>
    cases y using Fin.lastCases with
    | last =>
      constructor
      · intro h
        simp [growGraph] at h
      · intro h
        simp [pathGraph_adj, Fin.val_last] at h
    | cast y =>
      rw [adj_comm, grow_graph_adj_last]
      constructor
      · rintro rfl
        simp [pathGraph_adj, Fin.val_castSucc, Fin.val_last]
      · intro h
        simp [pathGraph_adj, Fin.val_castSucc, Fin.val_last] at h
        rcases h with h | h
        · omega
        · apply Fin.ext
          simpa [Fin.val_last] using h
  | cast x =>
    cases y using Fin.lastCases with
    | last =>
      rw [grow_graph_adj_last]
      constructor
      · rintro rfl
        simp [pathGraph_adj, Fin.val_castSucc, Fin.val_last]
      · intro h
        simp [pathGraph_adj, Fin.val_castSucc, Fin.val_last] at h
        rcases h with h | h
        · apply Fin.ext
          simpa [Fin.val_last] using h
        · omega
    | cast y =>
      rw [grow_graph_adj_cast]
      simp [pathGraph_adj, Fin.val_castSucc]

/-- One path-growing step, together with the corner at its endpoint. -/
noncomputable def pathStep : (n : ℕ) → Σ M : PlaneMap (n + 1), M.rotation.Corner (Fin.last n)
  | 0 => ⟨vertex, .isolated <| by
      intro w
      rw [vertex_graph]
      simp [bot_adj]⟩
  | n + 1 =>
    let prev := pathStep n
    let M := prev.1.grow (Fin.last n) prev.2
    ⟨M, .before (growBack (H := prev.1.graph) (Fin.last n)) <| by
      simp [growBack, growOut, Dart.symm]⟩

/-- A path on `n + 1` vertices, grown from one vertex. -/
noncomputable def pathMap (n : ℕ) : PlaneMap (n + 1) :=
  (pathStep n).1

theorem pathMap_graph (n : ℕ) : (pathMap n).graph = pathGraph (n + 1) := by
  induction n with
  | zero =>
    rw [pathMap, pathStep, vertex_graph, pathGraph_one_eq_bot]
  | succ n ih =>
    simp only [pathMap, pathStep]
    change growGraph (pathMap n).graph (Fin.last n) = pathGraph (n + 2)
    rw [ih]
    exact growGraph_pathGraph n

theorem pathMap_edge_count (n : ℕ) : (pathMap n).e = n := by
  induction n with
  | zero => simp [pathMap, pathStep, vertex_edge_count]
  | succ n ih =>
    simp only [pathMap, pathStep]
    have ih' : (pathStep n).fst.e = n := by simpa [pathMap] using ih
    rw [grow_edge_count, ih']

theorem pathMap_face_count (n : ℕ) : (pathMap n).f = 1 := by
  have h := euler_sphere (pathMap n)
  rw [vertex_count, pathMap_edge_count] at h
  omega

theorem pathMap_faceOf_eq {n : ℕ} (a b : (pathMap n).Dart) :
    (pathMap n).faceOf a = (pathMap n).faceOf b := by
  have hcard : Fintype.card (pathMap n).Face ≤ 1 := by
    simpa [f, RotationSystem.faceCount] using (pathMap_face_count n).le
  haveI : Subsingleton (pathMap n).Face := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact Subsingleton.elim _ _

private theorem nat_mod_eq_one {m x : ℕ} (hm : 0 < m) (hx : x < 2 * m) (h : x % m = 1) :
    x = 1 ∨ x = m + 1 := by
  by_cases hlt : x < m
  · left
    rwa [Nat.mod_eq_of_lt hlt] at h
  · right
    have hle : m ≤ x := Nat.le_of_not_gt hlt
    have hx' : x = m * (x / m) + 1 := by
      have := Nat.div_add_mod x m
      omega
    have hlt2 : x / m < 2 := (Nat.div_lt_iff_lt_mul hm).2 (by simpa [Nat.mul_comm] using hx)
    have hge : 1 ≤ x / m := by
      have : 0 < x / m := Nat.div_pos hle hm
      omega
    have hdiv : x / m = 1 := by omega
    rw [hdiv, Nat.mul_one] at hx'
    exact hx'

theorem splitGraph_path_cycle (n : ℕ) :
    splitGraph (pathGraph (n + 3)) 0 (Fin.last (n + 2)) (by
      intro h
      have := congrArg Fin.val h
      simp [Fin.val_last] at this) =
    cycleGraph (n + 3) := by
  ext a b
  simp only [splitGraph, pathGraph_adj, cycleGraph_adj']
  constructor
  · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rcases h with h | h
      · right
        rw [Fin.sub_val_of_le (by rw [Fin.le_def]; omega : a ≤ b)]
        omega
      · left
        rw [Fin.sub_val_of_le (by rw [Fin.le_def]; omega : b ≤ a)]
        omega
    · left
      rw [Fin.val_sub]
      simp only [Fin.val_last, Fin.val_zero]
      rw [show n + 3 - (n + 2) = 1 by omega, Nat.add_zero,
        Nat.mod_eq_of_lt (by omega)]
    · right
      rw [Fin.val_sub]
      simp only [Fin.val_last, Fin.val_zero]
      rw [show n + 3 - (n + 2) = 1 by omega, Nat.add_zero,
        Nat.mod_eq_of_lt (by omega)]
  · rintro (h | h)
    · rw [Fin.val_sub] at h
      have hx : (n + 3 - b.val) + a.val < 2 * (n + 3) := by omega
      rcases nat_mod_eq_one (by omega) hx h with hsum | hsum
      · right
        left
        have ha : a.val = 0 := by omega
        have hb : b.val = n + 2 := by omega
        exact ⟨Fin.ext ha, Fin.ext (by rw [Fin.val_last]; exact hb)⟩
      · left
        right
        omega
    · rw [Fin.val_sub] at h
      have hx : (n + 3 - a.val) + b.val < 2 * (n + 3) := by omega
      rcases nat_mod_eq_one (by omega) hx h with hsum | hsum
      · right
        right
        have ha : a.val = n + 2 := by omega
        have hb : b.val = 0 := by omega
        exact ⟨Fin.ext (by rw [Fin.val_last]; exact ha), Fin.ext hb⟩
      · left
        left
        omega

/-- The dart at the start of a path, from vertex `0` to vertex `1`. -/
noncomputable def pathStart (n : ℕ) : (pathMap (n + 2)).Dart where
  toProd := (0, 1)
  adj := by
    rw [pathMap_graph (n + 2), pathGraph_adj]
    left
    rfl

/-- The dart at the end of a path, from the last vertex to the previous one. -/
noncomputable def pathEnd (n : ℕ) : (pathMap (n + 2)).Dart where
  toProd := (Fin.last (n + 2), ⟨n + 1, by omega⟩)
  adj := by
    rw [pathMap_graph (n + 2), pathGraph_adj]
    right
    simp [Fin.val_last]

theorem pathStart_fst (n : ℕ) : (pathStart n).fst = 0 := rfl

theorem pathEnd_fst (n : ℕ) : (pathEnd n).fst = Fin.last (n + 2) := rfl

theorem path_ends_ne (n : ℕ) : (pathStart n).fst ≠ (pathEnd n).fst := by
  intro h
  rw [pathStart_fst, pathEnd_fst, Fin.ext_iff, Fin.val_last] at h
  exact absurd h (by omega : (0 : ℕ) ≠ n + 2)

theorem path_ends_not_adj (n : ℕ) :
    ¬ (pathMap (n + 2)).Adj (pathStart n).fst (pathEnd n).fst := by
  intro hadj
  have hadj' : (pathGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
    rw [← pathMap_graph (n + 2)]
    simpa [pathStart_fst, pathEnd_fst] using hadj
  rw [pathGraph_adj] at hadj'
  simp [Fin.val_last] at hadj'

/-- Close a path on `n + 3` vertices into `cycleGraph (n + 3)`. -/
noncomputable def cycleMap (n : ℕ) : PlaneMap (n + 3) :=
  (pathMap (n + 2)).split (pathStart n) (pathEnd n)
    (pathMap_faceOf_eq _ _) (path_ends_ne n) (path_ends_not_adj n)

theorem cycleMap_graph (n : ℕ) : (cycleMap n).graph = cycleGraph (n + 3) := by
  apply SimpleGraph.ext
  have hgraph := pathMap_graph (n + 2)
  simp only [cycleMap, split, data, PlaneMapData.split, splitGraph, hgraph,
    pathStart_fst, pathEnd_fst]
  exact SimpleGraph.ext_iff.mp (splitGraph_path_cycle n)

theorem cycleMap_edge_count (n : ℕ) : (cycleMap n).e = n + 3 := by
  have h := (pathMap (n + 2)).split_edge_count (pathStart n) (pathEnd n)
    (pathMap_faceOf_eq _ _) (path_ends_ne n) (path_ends_not_adj n)
  simp [cycleMap, pathMap_edge_count, h]

theorem cycleMap_face_count (n : ℕ) : (cycleMap n).f = 2 := by
  have h := euler_sphere (cycleMap n)
  rw [vertex_count, cycleMap_edge_count] at h
  omega

/-- The edge `0 → 1` of the triangle `cycleMap 0`. -/
noncomputable def triDart : (cycleMap 0).Dart where
  toProd := (0, 1)
  adj := by
    rw [cycleMap_graph, cycleGraph_three_eq_top]
    decide

theorem triDart_fst : triDart.fst = 0 := rfl

theorem triDart_faceNext_ne : (cycleMap 0).rotation.faceNext triDart ≠ triDart := by
  intro h
  have := congrArg (fun d : (cycleMap 0).Dart => d.fst) h
  rw [(cycleMap 0).rotation.face_next_fst] at this
  exact triDart.fst_ne_snd this.symm

/-- The triangle with a leaf grown into the face at vertex `0`. -/
noncomputable def tetGrow : PlaneMap 4 :=
  (cycleMap 0).grow 0 (.before triDart triDart_fst)

theorem tetGrow_graph :
    tetGrow.graph = growGraph (cycleMap 0).graph 0 := rfl

theorem tetGrow_rotation :
    tetGrow.rotation = growBefore 0 (cycleMap 0).rotation triDart triDart_fst := rfl

noncomputable def tetBack : tetGrow.Dart :=
  growBack (H := (cycleMap 0).graph) 0

noncomputable def tetAt1 : tetGrow.Dart :=
  growOld 0 ((cycleMap 0).rotation.faceNext triDart)

theorem tetBack_fst : tetBack.fst = 3 := by
  simp [tetBack, growBack, growOut]

theorem tetAt1_fst : tetAt1.fst = 1 := by
  simp only [tetAt1, growOld]
  change ((cycleMap 0).rotation.faceNext triDart).fst.castSucc = (1 : Fin 4)
  rw [(cycleMap 0).rotation.face_next_fst]
  simp [triDart]

theorem tet_same_face : tetGrow.faceOf tetBack = tetGrow.faceOf tetAt1 := by
  have hback := grow_before_face_back 0 (cycleMap 0).rotation triDart triDart_fst
  have hold := grow_before_face_old 0 (cycleMap 0).rotation triDart triDart_fst triDart
  rw [if_neg triDart_faceNext_ne] at hold
  let R := growBefore 0 (cycleMap 0).rotation triDart triDart_fst
  have h1 := R.face_of_face_next (growBack (H := (cycleMap 0).graph) 0)
  have h2 := R.face_of_face_next (growOld 0 triDart)
  rw [hback] at h1
  rw [hold] at h2
  unfold faceOf
  cases tetGrow_rotation
  exact h1.symm.trans h2.symm

theorem tet_not_adj : ¬ tetGrow.Adj tetBack.fst tetAt1.fst := by
  intro h
  have h' : tetGrow.graph.Adj 3 1 := by simpa [Adj, tetBack_fst, tetAt1_fst] using h
  rw [tetGrow_graph] at h'
  have hc : (1 : Fin 4) = Fin.castSucc (1 : Fin 3) := rfl
  have hl : (3 : Fin 4) = Fin.last 3 := rfl
  rw [hc, hl, adj_comm] at h'
  exact one_ne_zero ((grow_graph_adj_last 0 (1 : Fin 3)).1 h')

theorem tet_fst_ne : tetBack.fst ≠ tetAt1.fst := by
  rw [tetBack_fst, tetAt1_fst]
  decide

/-- The triangle plus a leaf, with the chord from the leaf to vertex `1`. -/
noncomputable def tetSplit : PlaneMap 4 :=
  tetGrow.split tetBack tetAt1 tet_same_face tet_fst_ne tet_not_adj

theorem tetSplit_graph :
    tetSplit.graph = splitGraph tetGrow.graph tetBack.fst tetAt1.fst tet_fst_ne := rfl

theorem tetSplit_rotation :
    tetSplit.rotation =
      PlaneMapConstruction.split tetGrow.rotation tetBack tetAt1 tet_fst_ne tet_not_adj := rfl

theorem faceNext_triDart_fst :
    ((cycleMap 0).rotation.faceNext triDart).fst = 1 := by
  rw [RotationSystem.face_next_fst]
  rfl

theorem cycleMap_zero_adj {i j : Fin 3} (h : i ≠ j) : (cycleMap 0).graph.Adj i j := by
  rw [cycleMap_graph, cycleGraph_three_eq_top]
  exact h

theorem faceNext_triDart_snd :
    ((cycleMap 0).rotation.faceNext triDart).snd = 2 := by
  set d := (cycleMap 0).rotation.faceNext triDart
  have hf : d.fst = 1 := faceNext_triDart_fst
  have hne1 : d.snd ≠ 1 := fun h => d.fst_ne_snd (hf.trans h.symm)
  have hne0 : d.snd ≠ 0 := by
    intro h
    have heq : d = triDart.symm := Dart.ext d triDart.symm (Prod.ext hf h)
    have hfix : (cycleMap 0).rotation.next triDart.symm = triDart.symm := by
      simpa [d, RotationSystem.face_next_apply] using heq
    let d2 : (cycleMap 0).Dart := ⟨(1, 2), cycleMap_zero_adj (by decide)⟩
    obtain ⟨k, hk⟩ := (cycleMap 0).rotation.cyclic triDart.symm d2 rfl
    have heq2 : d2 = triDart.symm :=
      hk.symm.trans (Function.iterate_fixed hfix k)
    exact (by decide : (2 : Fin 3) ≠ 0)
      (congrArg (fun x : (cycleMap 0).Dart => x.snd) heq2)
  have hval : d.snd.val = 2 := by
    have hlt : d.snd.val < 3 := d.snd.isLt
    have n0 : d.snd.val ≠ 0 := fun hv => hne0 (Fin.ext hv)
    have n1 : d.snd.val ≠ 1 := fun hv => hne1 (Fin.ext hv)
    omega
  exact Fin.ext hval

theorem faceNext_triDart_ne :
    (cycleMap 0).rotation.faceNext ((cycleMap 0).rotation.faceNext triDart) ≠ triDart := by
  intro h
  have hs := congrArg (fun x : (cycleMap 0).Dart => x.fst) h
  rw [RotationSystem.face_next_fst, faceNext_triDart_snd] at hs
  exact (by decide : (2 : Fin 3) ≠ 0) hs

/-- The new dart `3 → 1` after the first tetrahedron split. -/
noncomputable def tetOut : tetSplit.Dart :=
  splitOut (G := tetGrow.graph) tetBack.fst tetAt1.fst tet_fst_ne

/-- The dart `2 → 0` transported through the first split. -/
noncomputable def tetAt2 : tetSplit.Dart :=
  splitOld tetBack.fst tetAt1.fst tet_fst_ne
    (growOld 0 ((cycleMap 0).rotation.faceNext
      ((cycleMap 0).rotation.faceNext triDart)))

theorem tetOut_fst : tetOut.fst = 3 := by
  simp [tetOut, splitOut, tetBack_fst]

theorem tetAt2_fst : tetAt2.fst = 2 := by
  simp only [tetAt2, splitOld, growOld]
  change ((cycleMap 0).rotation.faceNext
    ((cycleMap 0).rotation.faceNext triDart)).fst.castSucc = (2 : Fin 4)
  rw [RotationSystem.face_next_fst, faceNext_triDart_snd]
  rfl

theorem tetAt1_snd : tetAt1.snd = 2 := by
  simp only [tetAt1, growOld]
  change ((cycleMap 0).rotation.faceNext triDart).snd.castSucc = (2 : Fin 4)
  rw [faceNext_triDart_snd]
  rfl

theorem tet_second_same_face : tetSplit.faceOf tetOut = tetSplit.faceOf tetAt2 := by
  have hout := split_face_out tetGrow.rotation tetBack tetAt1 tet_fst_ne tet_not_adj
  have hold := split_face_old tetGrow.rotation tetBack tetAt1 tet_fst_ne tet_not_adj tetAt1
  have hne1 : tetGrow.rotation.faceNext tetAt1 ≠ tetBack := by
    intro h
    have hs := congrArg (fun x : tetGrow.Dart => x.fst) h
    rw [RotationSystem.face_next_fst, tetAt1_snd, tetBack_fst] at hs
    exact (by decide : (2 : Fin 4) ≠ 3) hs
  have hne2 : tetGrow.rotation.faceNext tetAt1 ≠ tetAt1 := by
    intro h
    have hs := congrArg (fun x : tetGrow.Dart => x.fst) h
    rw [RotationSystem.face_next_fst] at hs
    exact tetAt1.fst_ne_snd hs.symm
  have hnext : tetGrow.rotation.faceNext tetAt1 =
      growOld 0 ((cycleMap 0).rotation.faceNext
        ((cycleMap 0).rotation.faceNext triDart)) := by
    have hold' := grow_before_face_old 0 (cycleMap 0).rotation triDart triDart_fst
      ((cycleMap 0).rotation.faceNext triDart)
    rw [ite_eq_right faceNext_triDart_ne] at hold'
    change (growBefore 0 (cycleMap 0).rotation triDart triDart_fst).faceNext
        (growOld 0 ((cycleMap 0).rotation.faceNext triDart)) =
      growOld 0 ((cycleMap 0).rotation.faceNext
        ((cycleMap 0).rotation.faceNext triDart))
    exact hold'
  rw [ite_eq_right hne1, ite_eq_right hne2, hnext] at hold
  let R := PlaneMapConstruction.split tetGrow.rotation tetBack tetAt1 tet_fst_ne tet_not_adj
  have h1 := R.face_of_face_next (splitOut tetBack.fst tetAt1.fst tet_fst_ne)
  rw [hout] at h1
  have h2 := R.face_of_face_next (splitOld tetBack.fst tetAt1.fst tet_fst_ne tetAt1)
  rw [hold] at h2
  unfold faceOf tetOut tetAt2
  cases tetSplit_rotation
  exact h1.symm.trans h2.symm

theorem tet_second_fst_ne : tetOut.fst ≠ tetAt2.fst := by
  rw [tetOut_fst, tetAt2_fst]
  decide

theorem tet_second_not_adj : ¬ tetSplit.Adj tetOut.fst tetAt2.fst := by
  intro h
  have h' : tetSplit.graph.Adj 3 2 := by simpa [Adj, tetOut_fst, tetAt2_fst] using h
  rw [tetSplit_graph] at h'
  change tetGrow.graph.Adj 3 2 ∨
      (3 = tetBack.fst ∧ 2 = tetAt1.fst) ∨
      (3 = tetAt1.fst ∧ 2 = tetBack.fst) at h'
  rw [tetBack_fst, tetAt1_fst] at h'
  rcases h' with h0 | h0 | h0
  · rw [tetGrow_graph] at h0
    have hl : (3 : Fin 4) = Fin.last 3 := rfl
    have hc : (2 : Fin 4) = Fin.castSucc (2 : Fin 3) := rfl
    rw [hl, hc, adj_comm] at h0
    exact (by decide : (2 : Fin 3) ≠ 0) ((grow_graph_adj_last 0 (2 : Fin 3)).1 h0)
  · exact (by decide : (2 : Fin 4) ≠ 1) h0.2
  · exact (by decide : (3 : Fin 4) ≠ 1) h0.1

/-- The tetrahedron, obtained by adding the two missing edges at the leaf. -/
noncomputable def tetrahedron : PlaneMap 4 :=
  tetSplit.split tetOut tetAt2 tet_second_same_face tet_second_fst_ne tet_second_not_adj

theorem tetrahedron_edge_count : tetrahedron.e = 6 := by
  have h0 : tetGrow.e = 4 := by
    change ((cycleMap 0).grow 0 (.before triDart triDart_fst)).e = 4
    rw [(cycleMap 0).grow_edge_count 0 (.before triDart triDart_fst),
      cycleMap_edge_count 0]
  have h1 : tetSplit.e = 5 := by
    change (tetGrow.split tetBack tetAt1 tet_same_face tet_fst_ne tet_not_adj).e = 5
    rw [tetGrow.split_edge_count, h0]
  change (tetSplit.split tetOut tetAt2 tet_second_same_face
      tet_second_fst_ne tet_second_not_adj).e = 6
  rw [tetSplit.split_edge_count, h1]

theorem tetrahedron_face_count : tetrahedron.f = 4 := by
  have h := euler_sphere tetrahedron
  rw [vertex_count, tetrahedron_edge_count] at h
  omega

theorem cycleMap_zero_graph : (cycleMap 0).graph = ⊤ := by
  rw [cycleMap_graph, cycleGraph_three_eq_top]

theorem tetrahedron_of_tetSplit {x y : Fin 4} (h : tetSplit.graph.Adj x y) :
    tetrahedron.graph.Adj x y :=
  show (splitGraph tetSplit.graph tetOut.fst tetAt2.fst tet_second_fst_ne).Adj x y from
    Or.inl h

theorem tetSplit_of_tetGrow {x y : Fin 4} (h : tetGrow.graph.Adj x y) :
    tetSplit.graph.Adj x y :=
  show (splitGraph tetGrow.graph tetBack.fst tetAt1.fst tet_fst_ne).Adj x y from
    Or.inl h

theorem tetSplit_adj_31 : tetSplit.graph.Adj 3 1 :=
  show (splitGraph tetGrow.graph tetBack.fst tetAt1.fst tet_fst_ne).Adj 3 1 from
    Or.inr (Or.inl ⟨tetBack_fst.symm, tetAt1_fst.symm⟩)

theorem tetrahedron_adj_32 : tetrahedron.graph.Adj 3 2 :=
  show (splitGraph tetSplit.graph tetOut.fst tetAt2.fst tet_second_fst_ne).Adj 3 2 from
    Or.inr (Or.inl ⟨tetOut_fst.symm, tetAt2_fst.symm⟩)

theorem tetrahedron_of_tetGrow {x y : Fin 4} (h : tetGrow.graph.Adj x y) :
    tetrahedron.graph.Adj x y :=
  tetrahedron_of_tetSplit (tetSplit_of_tetGrow h)

theorem tetGrow_adj_last_zero : tetGrow.graph.Adj 3 0 := by
  rw [tetGrow_graph, adj_comm]
  have hl : (3 : Fin 4) = Fin.last 3 := rfl
  have hc : (0 : Fin 4) = Fin.castSucc (0 : Fin 3) := rfl
  rw [hl, hc, grow_graph_adj_last]

theorem tetGrow_adj_cast {a b : Fin 3} (h : a ≠ b) :
    tetGrow.graph.Adj a.castSucc b.castSucc := by
  rw [tetGrow_graph, grow_graph_adj_cast, cycleMap_zero_graph]
  exact h

theorem fin4_of_ne_last {z : Fin 4} (hz : z ≠ 3) :
    z = 0 ∨ z = 1 ∨ z = 2 := by
  have hlt : z.val < 4 := z.isLt
  have hne : z.val ≠ 3 := fun h => hz (Fin.ext h)
  have : z.val = 0 ∨ z.val = 1 ∨ z.val = 2 := by omega
  rcases this with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem tetrahedron_graph : tetrahedron.graph = ⊤ := by
  ext x y
  constructor
  · exact fun h => h.ne
  · intro hne
    by_cases hx : x = 3
    · subst hx
      have hy : y ≠ 3 := fun h => hne h.symm
      rcases fin4_of_ne_last hy with hy | hy | hy
      · subst hy
        exact tetrahedron_of_tetGrow tetGrow_adj_last_zero
      · subst hy
        exact tetrahedron_of_tetSplit tetSplit_adj_31
      · subst hy
        exact tetrahedron_adj_32
    · by_cases hy : y = 3
      · subst hy
        rcases fin4_of_ne_last hx with hx | hx | hx
        · subst hx
          exact (tetrahedron_of_tetGrow tetGrow_adj_last_zero).symm
        · subst hx
          exact (tetrahedron_of_tetSplit tetSplit_adj_31).symm
        · subst hx
          exact tetrahedron_adj_32.symm
      · rcases fin4_of_ne_last hx with hx0 | hx0 | hx0 <;>
          rcases fin4_of_ne_last hy with hy0 | hy0 | hy0
        · exact (hne (hx0.trans hy0.symm)).elim
        · subst hx0; subst hy0
          exact tetrahedron_of_tetGrow (tetGrow_adj_cast (by decide : (0 : Fin 3) ≠ 1))
        · subst hx0; subst hy0
          exact tetrahedron_of_tetGrow (tetGrow_adj_cast (by decide : (0 : Fin 3) ≠ 2))
        · subst hx0; subst hy0
          exact tetrahedron_of_tetGrow (tetGrow_adj_cast (by decide : (1 : Fin 3) ≠ 0))
        · exact (hne (hx0.trans hy0.symm)).elim
        · subst hx0; subst hy0
          exact tetrahedron_of_tetGrow (tetGrow_adj_cast (by decide : (1 : Fin 3) ≠ 2))
        · subst hx0; subst hy0
          exact tetrahedron_of_tetGrow (tetGrow_adj_cast (by decide : (2 : Fin 3) ≠ 0))
        · subst hx0; subst hy0
          exact tetrahedron_of_tetGrow (tetGrow_adj_cast (by decide : (2 : Fin 3) ≠ 1))
        · exact (hne (hx0.trans hy0.symm)).elim

end PlaneMap

end SimpleGraph
