import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FiniteFourExtension

/-- info: 'SimpleGraph.SphericalMap.finiteFourColorSwapPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.finiteFourColorSwapPair

/-- info: 'SimpleGraph.SphericalMap.finiteFourColorMissing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.finiteFourColorMissing

/-- info: 'SimpleGraph.SphericalMap.finiteFourColorOpposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.finiteFourColorOpposite

/-- info: 'SimpleGraph.SphericalMap.finiteFourColorCyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.finiteFourColorCyclic

open SimpleGraph
def singletonM : SphericalMap 1 where
  graph := ⊥
  rotation := {
    next := Equiv.refl _
    next_fst := fun _ => rfl
    cyclic := fun d _ _ => False.elim d.adj }
  fills := fun _ _ => ⟨fun _ => 0, fun d => False.elim d.adj⟩
instance : DecidableRel singletonM.graph.Adj := fun _ _ => isFalse (by
  intro h
  exact h.ne (Subsingleton.elim _ _))
def singletonColouring := SphericalMap.finiteFourColorMissing singletonM 0 (fun _ => 3)
  (by intro u v h; exact False.elim (u.property (Subsingleton.elim _ _)))
  (by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro z h
    exact False.elim (h.ne (Subsingleton.elim _ _)))
/-- info: 0 -/
#guard_msgs in
#eval singletonColouring 0

-- The output is a certified proper colouring, rather than an existence proof.
example (M : SphericalMap 1) [DecidableRel M.graph.Adj]
    (c : Fin 1 → Fin 4)
    (hp : Kempe.IsProperColouring (M.graph.induce {z | z ≠ 0}) (fun z => c z.val))
    (hm : ((Finset.univ : Finset (Fin 4)).filter
      (fun a => ∀ z : Fin 1, M.Adj 0 z → c z ≠ a)).Nonempty)
    {u v : Fin 1} (h : M.graph.Adj u v) :
    M.finiteFourColorMissing 0 c hp hm u ≠ M.finiteFourColorMissing 0 c hp hm v :=
  (M.finiteFourColorMissing 0 c hp hm).valid h

/-- info: 'SimpleGraph.SphericalMap.finiteFourColorExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.finiteFourColorExtension

def singletonFullExtension := singletonM.finiteFourColorExtension 0
  (by rw [SimpleGraph.degree_eq_zero_of_subsingleton]; decide) (fun _ => 3)
  (by intro u v h; exact False.elim (u.property (Subsingleton.elim _ _)))
  (fun hd => False.elim (by rw [SimpleGraph.degree_eq_zero_of_subsingleton] at hd; omega))
  (by intro hd; rw [SimpleGraph.degree_eq_zero_of_subsingleton] at hd; omega)

/-- info: 0 -/
#guard_msgs in
#eval singletonFullExtension 0

-- A nontrivial component search on an actual deleted graph: the component
-- contains the surviving edge 0–1, while the surviving edge 3–4 is untouched.
def deletedPath : SimpleGraph {z : Fin 5 // z ≠ 2} :=
  (pathGraph 5).induce {z | z ≠ 2}
instance : DecidableRel deletedPath.Adj := fun u v =>
  decidable_of_iff (u.val.val + 1 = v.val.val ∨ v.val.val + 1 = u.val.val)
    pathGraph_adj.symm
def pathColours (z : {z : Fin 5 // z ≠ 2}) : Fin 4 := ⟨z.val.val % 4, Nat.mod_lt _ (by decide)⟩
def pathSwap := FiniteReachability.componentSwap deletedPath pathColours 0 1
  ⟨0, by decide⟩

/-- info: [1, 0, 3, 0] -/
#guard_msgs in
#eval [pathSwap ⟨0, by decide⟩, pathSwap ⟨1, by decide⟩,
  pathSwap ⟨3, by decide⟩, pathSwap ⟨4, by decide⟩]

example : Kempe.IsProperColouring deletedPath pathSwap := by
  apply FiniteReachability.componentSwap_proper deletedPath pathColours 0 1
    (by decide) ⟨0, by decide⟩ rfl
  intro u v huv
  have hu := u.property
  have hv := v.property
  have h : (pathGraph 5).Adj u.val v.val := huv
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  fin_cases u <;> fin_cases v <;>
    simp_all [pathGraph_adj, pathColours]

/-- info: 'SimpleGraph.SphericalMap.finiteCyclicEnumeration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.finiteCyclicEnumeration

/-- info: 'SimpleGraph.SphericalMap.finiteFourColorExtend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SimpleGraph.SphericalMap.finiteFourColorExtend

def singletonAutomatic := singletonM.finiteFourColorExtend 0
  (by rw [SimpleGraph.degree_eq_zero_of_subsingleton]; decide) (fun _ => 3)
  (by intro u v h; exact False.elim (u.property (Subsingleton.elim _ _)))

/-- info: 0 -/
#guard_msgs in
#eval singletonAutomatic 0

-- Exercise the exhaustive tuple-search backend on a genuine four-neighbour
-- rotation table. This fixture tests the search, without asserting a new
-- spherical-map construction or a complete four-neighbour extension run.
def fourLeafCycle (v : Fin 4 → Fin 5) : Prop :=
  ∀ i : Fin 4, v i ≠ 0 ∧ v (i + 1) = if v i = 4 then 1 else v i + 1
instance (v : Fin 4 → Fin 5) : Decidable (fourLeafCycle v) :=
  inferInstanceAs (Decidable (∀ i : Fin 4, v i ≠ 0 ∧
    v (i + 1) = if v i = 4 then 1 else v i + 1))
def fourLeafEnumeration := SphericalMap.finiteFirst fourLeafCycle
  (SphericalMap.finiteFourTuples 5) (fun _ => 0)

/-- info: [1, 2, 3, 4] -/
#guard_msgs in
#eval List.ofFn fourLeafEnumeration

example : fourLeafCycle fourLeafEnumeration := by
  apply SphericalMap.finiteFirst_spec
  refine ⟨![1, 2, 3, 4], SphericalMap.mem_finiteFourTuples _, ?_⟩
  decide
