module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalDegree
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Spherical sparsity and the twelve-vertex threshold

The incidence range has codimension at least one, yielding the sharper Euler
bound. Minimum positive degree five then requires twelve nonisolated vertices,
without connectedness or face-length assumptions.
-/

@[expose] public section
namespace SimpleGraph.SphericalMap
open scoped BigOperators
open Module
variable {n : ℕ} (M : SphericalMap n)

/-- The mod-two sum of all vertex incidences vanishes. -/
theorem sum_incidence_support (φ : M.graph.edgeSet → ZMod 2) :
    ∑ x : M.graph.support, edgeIncidence M.graph φ x.val = 0 := by
  classical
  unfold edgeIncidence
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  obtain ⟨d, hd⟩ := RotationSystem.edge_of_dart_surjective e
  let a : M.graph.support := ⟨d.fst, d.adj.mem_support_left⟩
  let b : M.graph.support := ⟨d.snd, d.adj.mem_support_right⟩
  have hab : a ≠ b := fun h => d.fst_ne_snd (congrArg Subtype.val h)
  have hterm : ∀ x : M.graph.support,
      (if x.val ∈ e.val then φ e else 0) =
        (if x = a then φ e else 0) + (if x = b then φ e else 0) := by
    intro x
    have hx : x.val ∈ e.val ↔ x = a ∨ x = b := by
      rw [← hd, mem_edgeOfDart_iff]
      simp only [a, b, Subtype.ext_iff, eq_comm]
    simp only [hx]
    by_cases hxa : x = a
    · simp [hxa, hab]
    · by_cases hxb : x = b
      · simp [hxb, hab.symm]
      · simp [hxa, hxb]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact ZModModule.add_self _

private theorem incidence_zero_off_support (φ : M.graph.edgeSet → ZMod 2)
    (x : Fin n) (hx : x ∉ M.graph.support) : edgeIncidence M.graph φ x = 0 := by
  classical
  unfold edgeIncidence
  apply Finset.sum_eq_zero
  intro e _
  have hne : x ∉ e.val := by
    intro he
    obtain ⟨d, hd⟩ := RotationSystem.edge_of_dart_surjective e
    rw [← hd, mem_edgeOfDart_iff] at he
    rcases he with he | he
    · exact hx (he ▸ d.adj.mem_support_left)
    · exact hx (he ▸ d.adj.mem_support_right)
  simp [hne]

/-- The filling property gives the Euler inequality needed for sparsity. -/
theorem edge_card_bound_two (d : M.Dart) :
    Fintype.card M.graph.edgeSet + 2 ≤
      Nat.card M.graph.support + Fintype.card M.Face := by
  classical
  let I := incidenceLinear M
  let B := boundaryLinear M
  have hker : LinearMap.ker I ≤ LinearMap.range B := by
    intro φ hφ
    have hφ' : IsEven M φ := by
      intro x
      by_cases hx : x ∈ M.graph.support
      · exact congrFun (LinearMap.mem_ker.mp hφ) ⟨x, hx⟩
      · exact incidence_zero_off_support M φ x hx
    obtain ⟨c, hc⟩ := even_is_face_sum M φ hφ'
    exact ⟨c, funext (fun e => (hc e).symm)⟩
  have hle := Submodule.finrank_mono hker
  have hi := I.finrank_range_add_finrank_ker
  have hb := B.finrank_range_add_finrank_ker
  have hir : finrank (ZMod 2) (LinearMap.range I) < Nat.card M.graph.support := by
    have hproper : LinearMap.range I ≠ ⊤ := by
      intro hh
      let a : M.graph.support := ⟨d.fst, d.adj.mem_support_left⟩
      have hmem : (fun x : M.graph.support => if x = a then (1 : ZMod 2) else 0) ∈
          LinearMap.range I := hh ▸ Submodule.mem_top
      obtain ⟨φ, hφ⟩ := hmem
      have hsum := sum_incidence_support M φ
      change (∑ x : M.graph.support, I φ x) = 0 at hsum
      rw [hφ] at hsum
      simp at hsum
    simpa using Submodule.finrank_lt hproper
  have hnonzero : LinearMap.ker B ≠ ⊥ := by
    intro hh
    have hconst : (fun _ : M.Face => (1 : ZMod 2)) ∈ LinearMap.ker B := by
      apply LinearMap.mem_ker.mpr
      ext e
      change (1 : ZMod 2) + 1 = 0
      exact ZMod.natCast_self 2
    rw [hh] at hconst
    have hc : (fun _ : M.Face => (1 : ZMod 2)) = 0 := by simpa using hconst
    exact one_ne_zero (congrFun hc (M.faceOf d))
  have hpos : 1 ≤ finrank (ZMod 2) (LinearMap.ker B) :=
    Submodule.one_le_finrank_iff.mpr hnonzero
  simp only [Module.finrank_fintype_fun_eq_card] at hi hb
  omega

private theorem degree_le_one_of_next_fixed (d : M.Dart)
    (hd : M.rotation.next d = d) : M.graph.degree d.fst ≤ 1 := by
  classical
  have hiter : ∀ k : ℕ, (⇑M.rotation.next)^[k] d = d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hd]
  have hsub : M.graph.neighborFinset d.fst ⊆ {d.snd} := by
    intro y hy
    let e : M.Dart := ⟨(d.fst, y), (M.graph.mem_neighborFinset _ _).mp hy⟩
    obtain ⟨k, hk⟩ := M.rotation.cyclic d e rfl
    have he : e = d := hk.symm.trans (hiter k)
    exact Finset.mem_singleton.mpr (congrArg (fun e : M.Dart => e.snd) he)
  simpa using Finset.card_le_card hsub

private theorem face_length_three_of_high_degree (d : M.Dart)
    (hdeg : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x) :
    3 ≤ M.rotation.faceLength (M.faceOf d) := by
  have hpos := M.rotation.face_length_pos d
  change 0 < M.rotation.faceLength (M.faceOf d) at hpos
  by_contra hlen
  change ¬ 3 ≤ M.rotation.faceLength (M.faceOf d) at hlen
  have hsmall : M.rotation.faceLength (M.faceOf d) = 1 ∨
      M.rotation.faceLength (M.faceOf d) = 2 := by omega
  have hperiod := M.rotation.face_next_iterate_length d
  rcases hsmall with hsmall | hsmall
  · rw [hsmall] at hperiod
    have hh := congrArg (fun e : M.Dart => e.fst) hperiod
    simp only [Function.iterate_one, RotationSystem.face_next_fst] at hh
    exact d.fst_ne_snd hh.symm
  · rw [hsmall] at hperiod
    have hp : M.rotation.faceNext (M.rotation.faceNext d) = d := hperiod
    have he : M.rotation.faceNext d = d.symm := by
      apply Dart.ext
      apply Prod.ext
      · exact M.rotation.face_next_fst d
      · have hh := congrArg (fun e : M.Dart => e.fst) hp
        change (M.rotation.faceNext d).snd = d.fst
        simpa only [RotationSystem.face_next_fst] using hh
    have hfixed : M.rotation.next d = d := by
      simpa only [he, RotationSystem.face_next_apply, Dart.symm_symm] using hp
    have hlo := degree_le_one_of_next_fixed M d hfixed
    have hhi := hdeg d.fst d.adj.mem_support_left
    omega

/-- A spherical map of minimum nonzero degree five has at least twelve
nonisolated vertices. The proof needs no connectedness or face-size premise. -/
theorem twelve_le_support_of_min_degree_five (d : M.Dart)
    (hdeg : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x) :
    12 ≤ Nat.card M.graph.support := by
  classical
  have hfaces : ∀ f : M.Face, 3 ≤ M.rotation.faceLength f := by
    intro f
    cases f with
    | inl f =>
      refine Quotient.inductionOn f ?_
      intro e
      exact face_length_three_of_high_degree M e hdeg
    | inr f => exact (f.property.false d).elim
  have hf : 3 * Fintype.card M.Face ≤ 2 * Fintype.card M.graph.edgeSet := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun f _ => hfaces f)
    have hs := M.rotation.sum_face_lengths_eq_twice_card_edges
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      edgeFinset_card, Nat.mul_comm] using hh.trans_eq hs
  have hv : 5 * Nat.card M.graph.support ≤ 2 * Fintype.card M.graph.edgeSet := by
    have hh := Finset.sum_le_sum (s := M.graph.support.toFinset)
      (fun x hx => hdeg x (Set.mem_toFinset.mp hx))
    have hs := M.graph.sum_degrees_support_eq_twice_card_edges
    simpa only [Finset.sum_const, Set.toFinset_card, smul_eq_mul,
      edgeFinset_card, Nat.mul_comm, Nat.card_eq_fintype_card] using hh.trans_eq hs
  have he := edge_card_bound_two M d
  omega

/-- Every edge-containing spherical map on at most eleven vertices has a
nonisolated vertex of degree at most four. This applies to spanning subgraphs
via spherical deletion closure. -/
theorem exists_pos_degree_le_four_of_order_le_eleven (hn : n ≤ 11) (d : M.Dart) :
    ∃ x : Fin n, 0 < M.graph.degree x ∧ M.graph.degree x ≤ 4 := by
  classical
  by_contra h
  have hdeg : ∀ x ∈ M.graph.support, 5 ≤ M.graph.degree x := by
    intro x hx
    have hp := (M.graph.degree_pos_iff_mem_support x).mpr hx
    have hh : ¬ M.graph.degree x ≤ 4 := fun hh => h ⟨x, hp, hh⟩
    omega
  have ht := twelve_le_support_of_min_degree_five M d hdeg
  have hs : Nat.card M.graph.support ≤ n := by
    simpa only [Nat.card_fin] using
      Nat.card_le_card_of_injective (fun x : M.graph.support => (x.val : Fin n))
        Subtype.val_injective
  omega

end SimpleGraph.SphericalMap
