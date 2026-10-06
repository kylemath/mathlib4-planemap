module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalFiveColor
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FaceCorner

@[expose] public section

namespace SimpleGraph.RotationSystem

/-- A mod-two potential with jumps at two consecutive positions is constant
away from the second position. This is the local algebraic Jordan step used
at a triangle's facial corner. -/
theorem potential_eq_of_two_consecutive_jumps
    {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (a b : α)
    (hnext : σ a = b) (hc : ∀ d, ∃ k : ℕ, (⇑σ)^[k] b = d)
    (c : α → ZMod 2)
    (hjump : ∀ d, c (σ d) + c d =
      (if d = a then 1 else 0) + (if d = b then 1 else 0))
    (d : α) (hd : d ≠ b) : c d = c b + 1 := by
  classical
  let g : α → ZMod 2 := fun d => c d + if d = b then 1 else 0
  have two (z : ZMod 2) : z + z = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
  have hpre (z : α) : σ z = b ↔ z = a := by
    rw [← hnext, σ.injective.eq_iff]
  have hg (z : α) : g (σ z) = g z := by
    have hh := hjump z
    have he : g (σ z) + g z = 0 := by
      dsimp [g]
      rw [if_congr (hpre z) rfl rfl]
      calc
        c (σ z) + (if z = a then 1 else 0) +
            (c z + if z = b then 1 else 0) =
            (c (σ z) + c z) +
              ((if z = a then 1 else 0) + if z = b then 1 else 0) := by ac_rfl
        _ = 0 := by rw [hh, two]
    have ht := two (g z)
    calc
      g (σ z) = g (σ z) + (g z + g z) := by rw [ht, add_zero]
      _ = (g (σ z) + g z) + g z := by ac_rfl
      _ = g z := by rw [he, zero_add]
  obtain ⟨k, hk⟩ := hc d
  have hi : ∀ k, g ((⇑σ)^[k] b) = g b := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hg, ih]
  have he := hi k
  rw [hk] at he
  simpa [g, hd] using he

/-- Face potentials at a vertex with two consecutive odd incident edges agree
on every outgoing dart except the second edge. -/
theorem face_potential_eq_of_two_consecutive_jumps
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (R : RotationSystem G) (v : V)
    (a b : G.neighborSet v) (hnext : R.neighborRotation v a = b)
    (c : R.Face → ZMod 2)
    (hjump : ∀ z : G.neighborSet v,
      c (R.faceOf (G.dartOfNeighborSet v z)) +
        c (R.faceOf (G.dartOfNeighborSet v z).symm) =
          (if z = a then 1 else 0) + (if z = b then 1 else 0))
    (z : G.neighborSet v) (hz : z ≠ b) :
    c (R.faceOf (G.dartOfNeighborSet v z)) =
      c (R.faceOf (G.dartOfNeighborSet v b)) + 1 := by
  classical
  apply potential_eq_of_two_consecutive_jumps (R.neighborRotation v) a b hnext
    (R.neighbor_rotation_cyclic v b)
    (fun z => c (R.faceOf (G.dartOfNeighborSet v z))) ?_ z hz
  intro w
  rw [R.neighbor_rotation_dart]
  have hf : R.faceOf (R.next (G.dartOfNeighborSet v w)) =
      R.faceOf (G.dartOfNeighborSet v w).symm := by
    exact R.face_of_face_next (G.dartOfNeighborSet v w).symm
  rw [hf, add_comm]
  exact hjump w

end SimpleGraph.RotationSystem

namespace SimpleGraph.SphericalMap

variable {n : ℕ} (M : SphericalMap n)

/-- At a facial triangle corner, any additional vertex on that same face is
nonadjacent to the corner's middle vertex. -/
theorem not_adj_of_triangle_face_corner
    {u v w x : Fin n} (huv : M.Adj u v) (hvw : M.Adj v w)
    (hwu : M.Adj w u)
    (hturn : M.rotation.next ⟨(v,u),huv.symm⟩ = ⟨(v,w),hvw⟩)
    (dx : M.Dart) (hdx : dx.fst = x)
    (hface : M.faceOf dx = M.faceOf (⟨(v,w),hvw⟩ : M.Dart))
    (hxu : x ≠ u) (hxv : x ≠ v) (hxw : x ≠ w) : ¬ M.Adj v x := by
  classical
  intro hvx
  let p : M.graph.Walk u u := .cons huv (.cons hvw (.cons hwu .nil))
  obtain ⟨c,hc⟩ := M.walkEdgeCoeff_is_face_sum p
  let a : M.graph.neighborSet v := ⟨u,huv.symm⟩
  let b : M.graph.neighborSet v := ⟨w,hvw⟩
  let z : M.graph.neighborSet v := ⟨x,hvx⟩
  have hnext : M.rotation.neighborRotation v a = b := by
    apply M.graph.dartOfNeighborSet_injective v
    rw [M.rotation.neighbor_rotation_dart]
    exact hturn
  have hjump (t : M.graph.neighborSet v) :
      c (M.faceOf (M.graph.dartOfNeighborSet v t)) +
        c (M.faceOf (M.graph.dartOfNeighborSet v t).symm) =
        (if t = a then 1 else 0) + (if t = b then 1 else 0) := by
    rw [← M.cycle_faceSum_edgeOfDart, ← hc]
    simp only [p, walkEdgeCoeff_cons, walkEdgeCoeff_nil, add_zero]
    have hea : RotationSystem.edgeOfDart (⟨(u,v),huv⟩ : M.Dart) =
        RotationSystem.edgeOfDart (M.graph.dartOfNeighborSet v t) ↔ t = a := by
      simp only [RotationSystem.edge_of_dart_eq_iff]
      constructor
      · rintro (h | h)
        · exact (huv.ne (congrArg (fun d : M.Dart => d.fst) h)).elim
        · apply Subtype.ext
          exact (congrArg (fun d : M.Dart => d.fst) h).symm
      · intro h
        subst t
        right
        rfl
    have heb : RotationSystem.edgeOfDart (⟨(v,w),hvw⟩ : M.Dart) =
        RotationSystem.edgeOfDart (M.graph.dartOfNeighborSet v t) ↔ t = b := by
      simp only [RotationSystem.edge_of_dart_eq_iff]
      constructor
      · rintro (h | h)
        · apply Subtype.ext
          exact (congrArg (fun d : M.Dart => d.snd) h).symm
        · exact (hvw.ne (congrArg (fun d : M.Dart => d.snd) h).symm).elim
      · intro h
        subst t
        left
        rfl
    have hec : RotationSystem.edgeOfDart (⟨(w,u),hwu⟩ : M.Dart) ≠
        RotationSystem.edgeOfDart (M.graph.dartOfNeighborSet v t) := by
      intro he
      rcases (RotationSystem.edge_of_dart_eq_iff _ _).mp he with h | h
      · exact hvw.ne (congrArg (fun d : M.Dart => d.fst) h).symm
      · exact huv.ne (congrArg (fun d : M.Dart => d.snd) h)
    rw [if_congr hea rfl rfl, if_congr heb rfl rfl, ite_eq_right hec, add_zero]
  have hz : z ≠ b := by intro h; exact hxw (congrArg Subtype.val h)
  have hlo := M.rotation.face_potential_eq_of_two_consecutive_jumps v a b hnext c hjump z hz
  have hx : x ∉ p.support := by simp [p, hxu, hxv, hxw]
  have heq := M.face_coeff_eq_at_unvisited_vertex p c hc hx
    (M.graph.dartOfNeighborSet v z).symm dx rfl hdx
  have hzero := M.walkEdgeCoeff_zero_of_not_mem_support p x hx
    (RotationSystem.edgeOfDart (M.graph.dartOfNeighborSet v z))
    ((mem_edgeOfDart_iff _ _).2 (Or.inr rfl))
  have hedge := M.face_coeff_eq_of_walkEdgeCoeff_zero p c hc
    (M.graph.dartOfNeighborSet v z) hzero
  have hh : c (M.faceOf (M.graph.dartOfNeighborSet v z)) =
      c (M.faceOf (M.graph.dartOfNeighborSet v b)) := by
    exact hedge.trans (heq.trans (congrArg c hface))
  rw [hh] at hlo
  exact one_ne_zero (add_left_cancel (hlo.symm.trans (add_zero _).symm))

/-- Every nontriangular dart face of a spherical map with minimum positive
degree two contains two distinct nonadjacent vertices. Repeated vertices in
the facial walk are allowed. -/
theorem exists_nonadjacent_face_vertices
    (hdeg : ∀ x ∈ M.graph.support, 2 ≤ M.graph.degree x)
    (d : M.Dart) (hlen : 4 ≤ M.rotation.faceLength (M.faceOf d)) :
    ∃ a b : M.Dart, M.faceOf a = M.faceOf d ∧ M.faceOf b = M.faceOf d ∧
      a.fst ≠ b.fst ∧ ¬ M.Adj a.fst b.fst := by
  classical
  by_contra hnone
  have hclique (a b : M.Dart) (ha : M.faceOf a = M.faceOf d)
      (hb : M.faceOf b = M.faceOf d) (hne : a.fst ≠ b.fst) :
      M.Adj a.fst b.fst := by
    by_contra hn
    exact hnone ⟨a,b,ha,hb,hne,hn⟩
  let e := M.rotation.faceNext d
  let f := M.rotation.faceNext e
  let g := M.rotation.faceNext f
  have he : M.faceOf e = M.faceOf d := M.rotation.face_of_face_next d
  have hf : M.faceOf f = M.faceOf d :=
    (M.rotation.face_of_face_next e).trans he
  have hg : M.faceOf g = M.faceOf d :=
    (M.rotation.face_of_face_next f).trans hf
  have hev : e.fst = d.snd := M.rotation.face_next_fst d
  have hfw : f.fst = e.snd := M.rotation.face_next_fst e
  have hgn : g.fst = f.snd := M.rotation.face_next_fst f
  have hduw : d.fst ≠ e.snd :=
    (M.rotation.face_next_snd_ne_fst_of_min_degree_two hdeg d).symm
  have huw : M.Adj d.fst e.snd := by
    simpa only [hfw] using hclique d f rfl hf (by simpa only [hfw] using hduw)
  have he_dart : e = (⟨(d.snd,e.snd),by simpa only [hev] using e.adj⟩ : M.Dart) := by
    apply Dart.ext
    exact Prod.ext hev rfl
  have hvertices (a : M.Dart) (ha : M.faceOf a = M.faceOf d) :
      a.fst = d.fst ∨ a.fst = d.snd ∨ a.fst = e.snd := by
    by_contra hn
    push Not at hn
    have hnot := M.not_adj_of_triangle_face_corner d.adj
      (show M.Adj d.snd e.snd by simpa [hev] using e.adj) huw.symm
      (show M.rotation.next ⟨(d.snd,d.fst),d.adj.symm⟩ =
        ⟨(d.snd,e.snd),by simpa [hev] using e.adj⟩ from
        by rw [← he_dart]; exact
          (show M.rotation.faceNext d = e from rfl))
      a rfl (by rw [← he_dart]; exact ha.trans he.symm) hn.1 hn.2.1 hn.2.2
    exact hnot (by simpa [hev] using hclique e a he ha (hev.trans_ne hn.2.1.symm))
  have hfu : f.snd = d.fst := by
    rcases hvertices g hg with hu | hv | hw
    · exact hgn.symm.trans hu
    · have hh := M.rotation.face_next_snd_ne_fst_of_min_degree_two hdeg e
      exact (hh (by change f.snd = e.fst; exact (hgn.symm.trans hv).trans hev.symm)).elim
    · exact (f.fst_ne_snd (hfw.trans (hgn.symm.trans hw).symm)).elim
  have hgv : g.snd = d.snd := by
    have hn : M.faceOf (M.rotation.faceNext g) = M.faceOf d :=
      (M.rotation.face_of_face_next g).trans hg
    rcases hvertices (M.rotation.faceNext g) hn with hu | hv | hw
    · exact (g.fst_ne_snd (hgn.trans hfu |>.trans
        ((M.rotation.face_next_fst g).symm.trans hu).symm)).elim
    · exact (M.rotation.face_next_fst g).symm.trans hv
    · have hh := M.rotation.face_next_snd_ne_fst_of_min_degree_two hdeg f
      exact (hh (by change g.snd = f.fst; exact
        ((M.rotation.face_next_fst g).symm.trans hw).trans hfw.symm)).elim
  have hreturn : M.rotation.faceNext (M.rotation.faceNext (M.rotation.faceNext d)) = d := by
    change g = d
    apply Dart.ext
    exact Prod.ext (hgn.trans hfu) hgv
  have hp : M.rotation.facePeriod d ≤ 3 := by
    exact Function.IsPeriodicPt.minimalPeriod_le (by decide) hreturn
  rw [M.rotation.face_length_eq_period] at hlen
  omega

/-- Chord endpoints in the insertion convention: the interrupted old facial
corners are the reversed selected outgoing darts. -/
theorem exists_face_chord
    (hdeg : ∀ x ∈ M.graph.support, 2 ≤ M.graph.degree x)
    (d : M.Dart) (hlen : 4 ≤ M.rotation.faceLength (M.faceOf d)) :
    ∃ a b : M.Dart, M.faceOf a.symm = M.faceOf d ∧
      M.faceOf b.symm = M.faceOf d ∧ a.fst ≠ b.fst ∧ ¬ M.Adj a.fst b.fst := by
  obtain ⟨u,v,hu,hv,hne,hnadj⟩ := M.exists_nonadjacent_face_vertices hdeg d hlen
  have hf (t : M.Dart) : (M.rotation.faceNext.symm t).snd = t.fst := by
    have hh := M.rotation.face_next_fst (M.rotation.faceNext.symm t)
    simpa only [Equiv.apply_symm_apply] using hh.symm
  have hp (t : M.Dart) : M.faceOf (M.rotation.faceNext.symm t) = M.faceOf t := by
    have hh := M.rotation.face_of_face_next (M.rotation.faceNext.symm t)
    simpa only [Equiv.apply_symm_apply] using hh.symm
  refine ⟨(M.rotation.faceNext.symm u).symm,
    (M.rotation.faceNext.symm v).symm, ?_, ?_, ?_, ?_⟩
  · simpa only [Dart.symm_symm] using (hp u).trans hu
  · simpa only [Dart.symm_symm] using (hp v).trans hv
  · change (M.rotation.faceNext.symm u).snd ≠ (M.rotation.faceNext.symm v).snd
    simpa only [hf] using hne
  · change ¬ M.Adj (M.rotation.faceNext.symm u).snd (M.rotation.faceNext.symm v).snd
    simpa only [hf] using hnadj

end SimpleGraph.SphericalMap
