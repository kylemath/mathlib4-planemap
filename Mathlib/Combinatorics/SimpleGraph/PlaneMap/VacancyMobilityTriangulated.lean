module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyMobilityGeneral
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalCompletion

/-!
# Vacancy mobility on triangulations

`vacancy_mobility_general` assumes the ring hypothesis (consecutive ports are adjacent) and the
rotation hypothesis (the vertex rotation at `h` steps from port `i` to port `i+1`).  On a
spherical map all of whose faces are triangles both are consequences of the structure:

* the vertex rotation at `h` is a single cycle through the neighbours, so listing the neighbours
  by iterating the rotation from one of them gives a `FiveLink` satisfying the rotation
  hypothesis (the pattern conclusion does not depend on the chosen `FiveLink`);
* in a triangular face, the dart `h → w` followed by the rotation step `w' = next w` closes up,
  so `w ~ w'` (`neighbor_rotation_adj`, here with the triangle hypothesis used only on the one
  face through the dart, not on every face).

The only hypothesis beyond `vacancy_mobility_general` is `Triangulated`.
-/

@[expose] public section
namespace SimpleGraph

namespace RotationSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (R : RotationSystem G)

/-- Consecutive neighbours in the vertex rotation are adjacent when the face of the reversed dart
is a triangle. -/
theorem neighbor_rotation_adj_of_triangle (v : V) (w : G.neighborSet v)
    (hw : R.faceLength (R.faceOf (G.dartOfNeighborSet v w).symm) = 3) :
    G.Adj w.val (R.neighborRotation v w).val := by
  let d := G.dartOfNeighborSet v w
  have h := R.face_next_iterate_length d.symm
  rw [hw] at h
  have h₃ : R.faceNext (R.faceNext (R.next d)) = d.symm := by
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      RotationSystem.face_next_apply, Dart.symm_symm] using h
  have hs : (R.faceNext (R.next d)).snd = d.snd :=
    (R.face_next_fst _).symm.trans (congrArg (fun d : G.Dart => d.fst) h₃)
  have he := (R.faceNext (R.next d)).adj
  rw [R.face_next_fst, hs] at he
  exact he.symm

end RotationSystem

namespace SphericalMap
open VacancyMobility VacancySlide VacancyShortFill
variable {n : ℕ} (M : SphericalMap n)

/-- On a triangulation, any five-port link can be re-listed along the vertex rotation, giving a
link whose consecutive ports are adjacent and in rotation order. -/
theorem exists_rotation_link (htri : M.Triangulated) {h : Fin n} (L : FiveLink M.graph h) :
    ∃ L' : FiveLink M.graph h, (∀ i : Fin 5, M.graph.Adj (L'.port i) (L'.port (i + 1))) ∧
      ∀ i : Fin 5, M.rotation.next ⟨(h, L'.port i), port_adj M.graph L' i⟩ =
        ⟨(h, L'.port (i + 1)), port_adj M.graph L' (i + 1)⟩ := by
  classical
  let R := M.rotation
  let σ := R.neighborRotation h
  let w0 : M.graph.neighborSet h := ⟨L.port 0, port_adj M.graph L 0⟩
  have hcard : Nat.card (M.graph.neighborSet h) = 5 := by
    have e : Fin 5 ≃ M.graph.neighborSet h :=
      Equiv.ofBijective (fun i => ⟨L.port i, port_adj M.graph L i⟩)
        ⟨fun a b hab => L.injective (congrArg Subtype.val hab), fun z => by
          obtain ⟨i, hi⟩ := (L.neighbours z.val).mp z.property
          exact ⟨i, Subtype.ext hi.symm⟩⟩
    simpa using (Nat.card_congr e).symm
  have hp : Function.minimalPeriod σ w0 = 5 := by
    have h1 := Nat.card_congr (R.neighborOrbitEquiv h w0)
    rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin, hcard] at h1
    exact h1
  have hper : σ^[5] w0 = w0 := by
    rw [← hp]; exact Function.iterate_minimalPeriod
  -- the iterate at position `i + 1` of `Fin 5` is `σ` of the iterate at `i`
  have hval : ∀ i : Fin 5, (i + 1 : Fin 5).val = (i.val + 1) % 5 := fun i => by
    rw [Fin.val_add]; rfl
  have hstep : ∀ i : Fin 5, σ^[(i + 1 : Fin 5).val] w0 = σ (σ^[i.val] w0) := by
    intro i
    by_cases hi : i.val = 4
    · rw [hval, hi]
      change σ^[0] w0 = σ (σ^[4] w0)
      rw [← Function.iterate_succ_apply' σ 4]
      exact hper.symm
    · have : (i + 1 : Fin 5).val = i.val + 1 := by
        rw [hval]; have := i.isLt; omega
      rw [this, Function.iterate_succ_apply']
  have hnbr : ∀ i : Fin 5, M.graph.Adj h (σ^[i.val] w0).val := fun i => (σ^[i.val] w0).property
  refine ⟨⟨fun i => (σ^[i.val] w0).val, ?_, ?_⟩, ?_, ?_⟩
  · intro a b hab
    have hab' : σ^[a.val] w0 = σ^[b.val] w0 := Subtype.ext hab
    have ha : a.val < Function.minimalPeriod σ w0 := by rw [hp]; exact a.isLt
    have hb : b.val < Function.minimalPeriod σ w0 := by rw [hp]; exact b.isLt
    exact Fin.ext (Function.iterate_injOn_Iio_minimalPeriod ha hb hab')
  · intro v
    constructor
    · intro hv
      obtain ⟨k, hk⟩ := R.neighbor_rotation_cyclic h w0 ⟨v, hv⟩
      have hk' : σ^[k % 5] w0 = ⟨v, hv⟩ := by
        rw [← hp, Function.iterate_mod_minimalPeriod_eq]; exact hk
      exact ⟨⟨k % 5, Nat.mod_lt _ (by norm_num)⟩, (congrArg Subtype.val hk').symm⟩
    · rintro ⟨i, rfl⟩; exact hnbr i
  · intro i
    simp only
    rw [hstep i]
    exact R.neighbor_rotation_adj_of_triangle h _ (htri _)
  · intro i
    have key : R.next (M.graph.dartOfNeighborSet h (σ^[i.val] w0)) =
        M.graph.dartOfNeighborSet h (σ^[(i + 1 : Fin 5).val] w0) := by
      rw [hstep i]; exact (R.neighbor_rotation_dart h _).symm
    exact key

/-- **Vacancy mobility on a triangulation.**  For a triangulated spherical map, a five-port link
at a hole `h` and a colouring proper off `h`, either a zero-or-one-move pure fill exists, or every
neighbour of `h` is approachable.  No ring or rotation hypothesis is needed. -/
theorem vacancy_mobility_triangulated (htri : M.Triangulated) {h : Fin n}
    (L : FiveLink M.graph h) {c : Fin n → Fin 4} (hc : ProperOff M.graph h c) :
    PureFill M.graph h c 1 ∨ ∀ u, M.Adj h u → Approach M.graph h c u := by
  obtain ⟨L', ring, rot⟩ := M.exists_rotation_link htri L
  exact M.vacancy_mobility_general L' hc ring rot

end SphericalMap
end SimpleGraph
