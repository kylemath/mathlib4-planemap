module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TwoPoleBeltWalk

@[expose] public section
namespace SimpleGraph.TwoPoleBeltWalk
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex
variable {n : Nat}

lemma root_automorphism (h : Vertex n) (hb : IsBelt h) :
    ∃ φ : G n ≃g G n, φ (u 0) = h ∧
      ((φ a = a ∧ φ b = b) ∨ (φ a = b ∧ φ b = a)) := by
  cases h with
  | a => exact (hb.1 rfl).elim
  | b => exact (hb.2 rfl).elim
  | u i =>
    refine ⟨rot i,?_,Or.inl ⟨rfl,rfl⟩⟩
    change u (0+i) = u i
    simp
  | v i =>
    refine ⟨(rot (-i)).trans ringSwap,?_,Or.inr ⟨rfl,rfl⟩⟩
    change v (-(0 + -i)) = v i
    simp

/-- Unequal-pole vacancy at every belt hole, with the uniform slide bound. -/
theorem belt_unequal_at (hn : 5 ≤ n) (h : Vertex n) (hb : IsBelt h)
    (c : Vertex n → Colour) (hc : ProperOff (G n) h c) (hab : c a ≠ c b) :
    ∃ k t, VacancyPotential.Path SlideStep k (h,c) t ∧ k ≤ 2*n ∧ Filled t ∧
      ProperOff (G n) t.1 t.2 ∧ IsBelt t.1 ∧ t.2 a = c a ∧ t.2 b = c b := by
  obtain ⟨φ,hφ,hpoles⟩ := root_automorphism h hb
  let c0 : Vertex n → Colour := c ∘ φ
  have hc0 : ProperOff (G n) (u 0) c0 := by
    intro x y edge hx hy
    change c (φ x) ≠ c (φ y)
    exact hc ((φ.map_rel_iff').mpr edge)
      (fun e => hx (φ.injective (e.trans hφ.symm)))
      (fun e => hy (φ.injective (e.trans hφ.symm)))
  have hneq : c0 a ≠ c0 b := by
    rcases hpoles with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa [c0,ha,hb] using hab
    · simpa [c0,ha,hb] using hab.symm
  obtain ⟨k,t,path,hk,filled,proper,belt,pa,pb⟩ := belt_unequal hn c0 hc0 hneq
  have cback : transport φ c0 = c := by
    funext x
    simp [transport,c0,Function.comp_apply]
  have moved := slidePath_transport φ (slidePath_of_path path)
  have path' : VacancyPotential.Path SlideStep k (h,c) (φ t.1,transport φ t.2) := by
    apply path_of_slidePath
    simpa [hφ,cback] using moved
  refine ⟨k,_,path',hk,target_transport φ filled,properOff_transport φ proper,?_,?_,?_⟩
  · change φ t.1 ≠ a ∧ φ t.1 ≠ b
    rcases hpoles with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨fun e => belt.1 (φ.injective (e.trans ha.symm)),
        fun e => belt.2 (φ.injective (e.trans hb.symm))⟩
    · exact ⟨fun e => belt.2 (φ.injective (e.trans hb.symm)),
        fun e => belt.1 (φ.injective (e.trans ha.symm))⟩
  · change t.2 (φ.symm a) = c a
    rcases hpoles with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · have inv : φ.symm a = a := by simpa using (congrArg φ.symm ha).symm
      rw [inv,pa]
      simp [c0,ha]
    · have inv : φ.symm a = b := by simpa using (congrArg φ.symm hb).symm
      rw [inv,pb]
      simp [c0,hb]
  · change t.2 (φ.symm b) = c b
    rcases hpoles with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · have inv : φ.symm b = b := by simpa using (congrArg φ.symm hb).symm
      rw [inv,pb]
      simp [c0,hb]
    · have inv : φ.symm b = a := by simpa using (congrArg φ.symm ha).symm
      rw [inv,pa]
      simp [c0,ha]

end SimpleGraph.TwoPoleBeltWalk
