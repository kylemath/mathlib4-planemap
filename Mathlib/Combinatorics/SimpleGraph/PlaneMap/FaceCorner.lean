module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationSystem

/-!
# Short face walks and minimum positive degree

These lemmas concern arbitrary finite rotation systems. They exclude immediate
reversal and short faces under minimum positive degree two; they do not assert
that every nontriangular face admits a chord.
-/

@[expose] public section

namespace SimpleGraph.RotationSystem

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (R : RotationSystem G)

/-- A dart fixed by the vertex rotation is the only outgoing dart at its vertex. -/
theorem degree_le_one_of_next_fixed (d : G.Dart) (hd : R.next d = d) :
    G.degree d.fst ≤ 1 := by
  classical
  have hiter : ∀ k : ℕ, (⇑R.next)^[k] d = d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hd]
  have hsub : G.neighborFinset d.fst ⊆ {d.snd} := by
    intro y hy
    let e : G.Dart := ⟨(d.fst, y), (G.mem_neighborFinset _ _).mp hy⟩
    obtain ⟨k, hk⟩ := R.cyclic d e rfl
    have he : e = d := hk.symm.trans (hiter k)
    exact Finset.mem_singleton.mpr (congrArg (fun e : G.Dart => e.snd) he)
  simpa using Finset.card_le_card hsub

/-- Immediate face reversal can occur only at a vertex of degree one. -/
theorem degree_le_one_of_face_next_eq_symm (d : G.Dart)
    (hd : R.faceNext d = d.symm) : G.degree d.snd ≤ 1 := by
  exact R.degree_le_one_of_next_fixed d.symm hd

/-- Minimum positive degree two excludes immediate reversal in a face walk. -/
theorem face_next_ne_symm_of_min_degree_two
    (hdeg : ∀ x ∈ G.support, 2 ≤ G.degree x) (d : G.Dart) :
    R.faceNext d ≠ d.symm := by
  intro hd
  have hlo := R.degree_le_one_of_face_next_eq_symm d hd
  have hhi := hdeg d.snd d.adj.mem_support_right
  omega

/-- Under minimum positive degree two, two successive facial edges do not return
immediately to the first vertex. -/
theorem face_next_snd_ne_fst_of_min_degree_two
    (hdeg : ∀ x ∈ G.support, 2 ≤ G.degree x) (d : G.Dart) :
    (R.faceNext d).snd ≠ d.fst := by
  intro hh
  apply R.face_next_ne_symm_of_min_degree_two hdeg d
  apply Dart.ext
  exact Prod.ext (R.face_next_fst d) hh

/-- Every dart-containing face has at least three darts under minimum positive
degree two. No spherical filling hypothesis is needed. -/
theorem three_le_face_length_of_min_degree_two
    (hdeg : ∀ x ∈ G.support, 2 ≤ G.degree x) (d : G.Dart) :
    3 ≤ R.faceLength (R.faceOf d) := by
  have hpos := R.face_length_pos d
  by_contra hlen
  have hsmall : R.faceLength (R.faceOf d) = 1 ∨
      R.faceLength (R.faceOf d) = 2 := by omega
  have hperiod := R.face_next_iterate_length d
  rcases hsmall with hsmall | hsmall
  · rw [hsmall] at hperiod
    have hh := congrArg (fun e : G.Dart => e.fst) hperiod
    simp only [Function.iterate_one, face_next_fst] at hh
    exact d.fst_ne_snd hh.symm
  · rw [hsmall] at hperiod
    have hp : R.faceNext (R.faceNext d) = d := hperiod
    have he : R.faceNext d = d.symm := by
      apply Dart.ext
      apply Prod.ext
      · exact R.face_next_fst d
      · have hh := congrArg (fun e : G.Dart => e.fst) hp
        change (R.faceNext d).snd = d.fst
        simpa only [face_next_fst] using hh
    exact R.face_next_ne_symm_of_min_degree_two hdeg d he

end SimpleGraph.RotationSystem
