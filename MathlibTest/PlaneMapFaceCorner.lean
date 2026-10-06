module

import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FaceCorner
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.Icosahedron

open SimpleGraph

/-- info: 'SimpleGraph.RotationSystem.degree_le_one_of_next_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.degree_le_one_of_next_fixed

/-- info: 'SimpleGraph.RotationSystem.degree_le_one_of_face_next_eq_symm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.degree_le_one_of_face_next_eq_symm

/-- info: 'SimpleGraph.RotationSystem.face_next_ne_symm_of_min_degree_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.face_next_ne_symm_of_min_degree_two

/-- info: 'SimpleGraph.RotationSystem.face_next_snd_ne_fst_of_min_degree_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.face_next_snd_ne_fst_of_min_degree_two

/-- info: 'SimpleGraph.RotationSystem.three_le_face_length_of_min_degree_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.three_le_face_length_of_min_degree_two

example (d : Icosahedron.graph.Dart) :
    Icosahedron.sphericalMap.rotation.faceNext d ≠ d.symm := by
  apply RotationSystem.face_next_ne_symm_of_min_degree_two
  intro x _
  rw [Icosahedron.sphericalMap_degree]
  decide

example (d : Icosahedron.graph.Dart) :
    3 ≤ Icosahedron.sphericalMap.rotation.faceLength
      (Icosahedron.sphericalMap.faceOf d) := by
  apply RotationSystem.three_le_face_length_of_min_degree_two
  intro x _
  rw [Icosahedron.sphericalMap_degree]
  decide

namespace DegreeOneRegression

-- A single edge has immediate facial reversal. The degree hypothesis is necessary.
def graph : SimpleGraph (Fin 2) := ⊤

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel (⊤ : SimpleGraph (Fin 2)).Adj)

def rotation : RotationSystem graph where
  next := Equiv.refl _
  next_fst _ := rfl
  cyclic d e h := by
    refine ⟨0, ?_⟩
    change d = e
    apply Dart.ext
    apply Prod.ext h
    apply Fin.ext
    have hd := d.adj.ne
    have he := e.adj.ne
    have hf := congrArg Fin.val h
    simp only [ne_eq, Fin.ext_iff] at hd he
    omega

def dart : graph.Dart := ⟨(0, 1), by decide⟩

example : graph.degree dart.snd = 1 := by decide
example : rotation.faceNext dart = dart.symm := rfl

end DegreeOneRegression
