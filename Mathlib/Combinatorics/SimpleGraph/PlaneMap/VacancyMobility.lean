module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyShortFill
public import Mathlib.Tactic.FinCases
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalFiveColor

@[expose] public section
namespace SimpleGraph.VacancyMobility
open VacancySlide VacancyShortFill
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Five distinct ports, comprising the actual complete neighbourhood of the hole. -/
structure FiveLink (h : V) where
  port : Fin 5 → V
  injective : Function.Injective port
  neighbours : ∀ v, G.Adj h v ↔ ∃ i, v = port i

def gapWord (i : Fin 5) : Fin 4 :=
  if i=1 then 1 else if i=3 then 2 else if i=4 then 3 else 0
def Pattern {h : V} (L : FiveLink G h) (c : V → Fin 4) : Prop :=
  ∀ i, c (L.port i) = gapWord i

/-- Explicit alternating-pair separation implications. These are graph reachability
facts supplied by the spherical Jordan wrapper, not assumed move/target conclusions. -/
structure Alternation {h : V} (L : FiveLink G h) (c : V → Fin 4) : Prop where
  right : (pairGraph G h c 1 3).Reachable (L.port 1) (L.port 4) →
    ¬ (pairGraph G h c 0 2).Reachable (L.port 0) (L.port 2) ∧
    ¬ (pairGraph G h c 0 2).Reachable (L.port 0) (L.port 3)
  left : (pairGraph G h c 1 2).Reachable (L.port 1) (L.port 3) →
    ¬ (pairGraph G h c 0 3).Reachable (L.port 2) (L.port 0) ∧
    ¬ (pairGraph G h c 0 3).Reachable (L.port 2) (L.port 4)

omit [DecidableEq V] in
lemma port_adj {h : V} (L : FiveLink G h) (i : Fin 5) : G.Adj h (L.port i) :=
  (L.neighbours _).mpr ⟨i,rfl⟩

omit [DecidableEq V] in
lemma singleton_ports {h : V} (L : FiveLink G h) {c : V → Fin 4}
    (pat : Pattern G L c) (i : Fin 5) (hi : i=1 ∨ i=3 ∨ i=4) :
    UniqueAt G h (L.port i) c := by
  intro v ev eq
  obtain ⟨j,rfl⟩ := (L.neighbours v).mp ev
  rw [pat j,pat i] at eq
  rcases hi with rfl | rfl | rfl <;> fin_cases j <;>
    simp [gapWord] at eq ⊢

/-- An actual short path reaching a selected hole, with proper endpoint. -/
def ReachHole (h : V) (c : V → Fin 4) (u : V) : Prop :=
  ∃ n, n ≤ 2 ∧ ∃ d, MixedPath G n (h,c) (u,d) ∧ ProperOff G u d

/-- A concrete optional Kempe prefix at the original hole, followed by a legal
singleton slide. This exposes the shape needed by short-fill suffix conversion. -/
def Approach (h : V) (c : V → Fin 4) (u : V) : Prop :=
  ∃ d, (d=c ∨ KempeStep G h c d) ∧ ProperOff G h d ∧
    G.Adj h u ∧ UniqueAt G h u d

lemma approach_reach {h u : V} {c : V → Fin 4}
    (ap : Approach G h c u) : ReachHole G h c u := by
  obtain ⟨d,first,proper,adj,uniq⟩ := ap
  rcases first with hd | step
  · subst d
    exact ⟨1,by decide,slide h u c,.cons (.slide adj uniq) (.nil _),
      properOff_slide G proper uniq⟩
  · exact ⟨2,le_rfl,slide h u d,
      .cons (.kempe step) (.cons (.slide adj uniq) (.nil _)),
      properOff_slide G proper uniq⟩

omit [DecidableEq V] in
lemma singleton_approach {h u : V} {c : V → Fin 4}
    (hc : ProperOff G h c) (adj : G.Adj h u) (uniq : UniqueAt G h u c) :
    Approach G h c u := ⟨c,Or.inl rfl,hc,adj,uniq⟩

lemma singleton_reach {h u : V} {c : V → Fin 4}
    (hc : ProperOff G h c) (adj : G.Adj h u) (uniq : UniqueAt G h u c) :
    ReachHole G h c u := by
  exact ⟨1,by decide,slide h u c,.cons (.slide adj uniq) (.nil _),
    properOff_slide G hc uniq⟩

omit [DecidableEq V] in
lemma one_fill_of_right_missing {h : V} (L : FiveLink G h) {c : V → Fin 4}
    (hc : ProperOff G h c) (pat : Pattern G L c)
    (absent : ¬ (pairGraph G h c 1 3).Reachable (L.port 1) (L.port 4)) :
    PureFill G h c 1 := by
  apply pureFill_one G
  apply one_swap_target G hc (port_adj G L 1)
    (singleton_ports G L pat 1 (Or.inl rfl)) (rho := 3)
  · simp [pat 1,gapWord]
  · intro v ev eq reach
    have hv : v = L.port 4 := by
      apply singleton_ports G L pat 4 (Or.inr (Or.inr rfl)) ev
      simpa [pat 4,gapWord] using eq
    subst v
    apply absent
    simpa [pat 1,gapWord] using reach

omit [DecidableEq V] in
lemma one_fill_of_left_missing {h : V} (L : FiveLink G h) {c : V → Fin 4}
    (hc : ProperOff G h c) (pat : Pattern G L c)
    (absent : ¬ (pairGraph G h c 1 2).Reachable (L.port 1) (L.port 3)) :
    PureFill G h c 1 := by
  apply pureFill_one G
  apply one_swap_target G hc (port_adj G L 1)
    (singleton_ports G L pat 1 (Or.inl rfl)) (rho := 2)
  · simp [pat 1,gapWord]
  · intro v ev eq reach
    have hv : v = L.port 3 := by
      apply singleton_ports G L pat 3 (Or.inr (Or.inl rfl)) ev
      simpa [pat 3,gapWord] using eq
    subst v
    apply absent
    simpa [pat 1,gapWord] using reach



omit [DecidableEq V] in
/-- The actual alpha/gamma component swap unlocks the second repeated port. -/
lemma unlock_second {h : V} (L : FiveLink G h) {c : V → Fin 4}
    (hc : ProperOff G h c) (pat : Pattern G L c)
    (sep : ¬ (pairGraph G h c 0 2).Reachable (L.port 0) (L.port 2) ∧
      ¬ (pairGraph G h c 0 2).Reachable (L.port 0) (L.port 3)) :
    Approach G h c (L.port 2) := by
  classical
  let S : Set V := {v | (pairGraph G h c 0 2).Reachable (L.port 0) v}
  have whole : Whole G h c 0 2 S := whole_component G h c 0 2 (L.port 0)
    ⟨(port_adj G L 0).ne.symm,Or.inl (by simpa [gapWord] using pat 0)⟩
  have out1 : L.port 1 ∉ S := by
    intro hin
    have ha := (whole_active G whole hin).2
    simp [pat 1,gapWord] at ha
  have out4 : L.port 4 ∉ S := by
    intro hin
    have ha := (whole_active G whole hin).2
    simp [pat 4,gapWord] at ha
  let d := swap c (0 : Fin 4) 2 S
  have col0 : d (L.port 0) = 2 := by
    dsimp [d]; rw [swap_in (show L.port 0 ∈ S from Reachable.rfl),pat 0]
    simp [gapWord]
  have col1 : d (L.port 1) = 1 := by
    dsimp [d]; rw [swap_out out1,pat 1]; simp [gapWord]
  have col2 : d (L.port 2) = 0 := by
    dsimp [d]; rw [swap_out (S := S) sep.1,pat 2]; simp [gapWord]
  have col3 : d (L.port 3) = 2 := by
    dsimp [d]; rw [swap_out (S := S) sep.2,pat 3]; simp [gapWord]
  have col4 : d (L.port 4) = 3 := by
    dsimp [d]; rw [swap_out out4,pat 4]; simp [gapWord]
  have uniq : UniqueAt G h (L.port 2) d := by
    intro v ev eq
    obtain ⟨i,rfl⟩ := (L.neighbours v).mp ev
    rw [col2] at eq
    fin_cases i <;> simp [col0,col1,col2,col3,col4] at eq ⊢
  have step : KempeStep G h c d := ⟨0,2,S,by decide,whole,rfl⟩
  exact ⟨d,Or.inr step,properOff_swap G hc whole,port_adj G L 2,uniq⟩

omit [DecidableEq V] in
/-- The actual alpha/delta component swap unlocks the first repeated port. -/
lemma unlock_first {h : V} (L : FiveLink G h) {c : V → Fin 4}
    (hc : ProperOff G h c) (pat : Pattern G L c)
    (sep : ¬ (pairGraph G h c 0 3).Reachable (L.port 2) (L.port 0) ∧
      ¬ (pairGraph G h c 0 3).Reachable (L.port 2) (L.port 4)) :
    Approach G h c (L.port 0) := by
  classical
  let S : Set V := {v | (pairGraph G h c 0 3).Reachable (L.port 2) v}
  have whole : Whole G h c 0 3 S := whole_component G h c 0 3 (L.port 2)
    ⟨(port_adj G L 2).ne.symm,Or.inl (by simpa [gapWord] using pat 2)⟩
  have out1 : L.port 1 ∉ S := by
    intro hin
    have ha := (whole_active G whole hin).2
    simp [pat 1,gapWord] at ha
  have out3 : L.port 3 ∉ S := by
    intro hin
    have ha := (whole_active G whole hin).2
    simp [pat 3,gapWord] at ha
  let d := swap c (0 : Fin 4) 3 S
  have col0 : d (L.port 0) = 0 := by
    dsimp [d]; rw [swap_out (S := S) sep.1,pat 0]; simp [gapWord]
  have col1 : d (L.port 1) = 1 := by
    dsimp [d]; rw [swap_out out1,pat 1]; simp [gapWord]
  have col2 : d (L.port 2) = 3 := by
    dsimp [d]; rw [swap_in (show L.port 2 ∈ S from Reachable.rfl),pat 2]
    simp [gapWord]
  have col3 : d (L.port 3) = 2 := by
    dsimp [d]; rw [swap_out out3,pat 3]; simp [gapWord]
  have col4 : d (L.port 4) = 3 := by
    dsimp [d]; rw [swap_out (S := S) sep.2,pat 4]; simp [gapWord]
  have uniq : UniqueAt G h (L.port 0) d := by
    intro v ev eq
    obtain ⟨i,rfl⟩ := (L.neighbours v).mp ev
    rw [col0] at eq
    fin_cases i <;> simp [col0,col1,col2,col3,col4] at eq ⊢
  have step : KempeStep G h c d := ⟨0,3,S,by decide,whole,rfl⟩
  exact ⟨d,Or.inr step,properOff_swap G hc whole,port_adj G L 0,uniq⟩

omit [DecidableEq V] in
/-- Actual local dichotomy on the normalized four-colour five-port link. The
explicit alternating-connectivity implications are the remaining geometric input. -/
theorem local_alternative {h : V} (L : FiveLink G h) {c : V → Fin 4}
    (hc : ProperOff G h c) (pat : Pattern G L c) (sep : Alternation G L c) :
    PureFill G h c 1 ∨ ∀ u, G.Adj h u → Approach G h c u := by
  classical
  by_cases right : (pairGraph G h c 1 3).Reachable (L.port 1) (L.port 4)
  · by_cases left : (pairGraph G h c 1 2).Reachable (L.port 1) (L.port 3)
    · right
      intro u eu
      obtain ⟨i,rfl⟩ := (L.neighbours u).mp eu
      fin_cases i
      · exact unlock_first G L hc pat (sep.left left)
      · exact singleton_approach G hc (port_adj G L 1)
          (singleton_ports G L pat 1 (Or.inl rfl))
      · exact unlock_second G L hc pat (sep.right right)
      · exact singleton_approach G hc (port_adj G L 3)
          (singleton_ports G L pat 3 (Or.inr (Or.inl rfl)))
      · exact singleton_approach G hc (port_adj G L 4)
          (singleton_ports G L pat 4 (Or.inr (Or.inr rfl)))
    · exact Or.inl (one_fill_of_left_missing G L hc pat left)
  · exact Or.inl (one_fill_of_right_missing G L hc pat right)

theorem local_short_alternative {h : V} (L : FiveLink G h) {c : V → Fin 4}
    (hc : ProperOff G h c) (pat : Pattern G L c) (sep : Alternation G L c) :
    PureFill G h c 1 ∨ ∀ u, G.Adj h u → ReachHole G h c u := by
  rcases local_alternative G L hc pat sep with fill | move
  · exact Or.inl fill
  · exact Or.inr (fun u hu => approach_reach G (move u hu))



omit [DecidableEq V] in
lemma pair_walk_support {h s t : V} {c : V → Fin 4} {a b : Fin 4}
    (p : (pairGraph G h c a b).Walk s t) (hs : Active h c a b s) :
    ∀ z ∈ p.support, Active h c a b z := by
  induction p with
  | nil =>
    intro z hz
    simp only [Walk.support_nil,List.mem_singleton] at hz
    subst z
    exact hs
  | @cons s t u e p ih =>
    intro z hz
    simp only [Walk.support_cons,List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hs
    · exact ih e.2.2 z hz

end SimpleGraph.VacancyMobility

namespace SimpleGraph.SphericalMap
open VacancySlide VacancyShortFill VacancyMobility
variable {n : Nat} (M : SphericalMap n)

/-- Native spherical separation for actual pair-graph walks, using the existing
rotation/face-sum intersection theorem rather than a new topological axiom. -/
lemma vacancy_pairs_separate {h v0 v1 v2 v3 : Fin n} {c : Fin n → Fin 4}
    {a b r s : Fin 4} (h0 : M.Adj h v0) (h1 : M.Adj h v1)
    (h2 : M.Adj h v2) (h3 : M.Adj h v3) (h02 : v0 ≠ v2)
    (rot12 : M.rotation.next ⟨(h,v1),h1⟩ = ⟨(h,v2),h2⟩)
    (rot23 : M.rotation.next ⟨(h,v2),h2⟩ = ⟨(h,v3),h3⟩)
    (active0 : c v0=a ∨ c v0=b) (active1 : c v1=r ∨ c v1=s)
    (disjoint : ∀ col : Fin 4, (col=a ∨ col=b) → (col=r ∨ col=s) → False) :
    (pairGraph M.graph h c a b).Reachable v0 v2 →
    ¬ (pairGraph M.graph h c r s).Reachable v1 v3 := by
  rintro ⟨p⟩ ⟨q⟩
  let fp : pairGraph M.graph h c a b →g M.graph := ⟨id,fun e => e.1⟩
  let fq : pairGraph M.graph h c r s →g M.graph := ⟨id,fun e => e.1⟩
  let p' := p.map fp
  let q' := q.map fq
  have ps : p'.support=p.support := by simp [p',Walk.support_map,fp]
  have qs : q'.support=q.support := by simp [q',Walk.support_map,fq]
  have ap := pair_walk_support M.graph p ⟨h0.ne.symm,active0⟩
  have aq := pair_walk_support M.graph q ⟨h1.ne.symm,active1⟩
  obtain ⟨z,hpz,hqz⟩ := alternating_walks_intersect h0 h1 h2 h3 h02 rot12 rot23
    p' (fun hx => (ap h (ps ▸ hx)).1 rfl)
    q' (fun hx => (aq h (qs ▸ hx)).1 rfl)
  exact disjoint (c z) (ap z (ps ▸ hpz)).2 (aq z (qs ▸ hqz)).2



/-- All separation inputs of the normalized mobility theorem are discharged
from the native spherical rotation and face-sum theory. -/
theorem vacancy_alternation {h : Fin n} (L : FiveLink M.graph h)
    {c : Fin n → Fin 4} (pat : Pattern M.graph L c)
    (rot : ∀ i : Fin 5,
      M.rotation.next ⟨(h,L.port i),port_adj M.graph L i⟩ =
        ⟨(h,L.port (i+1)),port_adj M.graph L (i+1)⟩) :
    Alternation M.graph L c := by
  have ne (i j : Fin 5) (hij : i ≠ j) : L.port i ≠ L.port j :=
    fun eq => hij (L.injective eq)
  constructor
  · intro right
    constructor
    · exact vacancy_pairs_separate M
        (port_adj M.graph L 4) (port_adj M.graph L 0)
        (port_adj M.graph L 1) (port_adj M.graph L 2)
        (ne 4 1 (by decide)) (by simpa using rot 0) (by simpa using rot 1)
        (Or.inr (by simpa [gapWord] using pat 4))
        (Or.inl (by simpa [gapWord] using pat 0)) (by decide) right.symm
    · intro opposite
      exact vacancy_pairs_separate M
        (port_adj M.graph L 1) (port_adj M.graph L 3)
        (port_adj M.graph L 4) (port_adj M.graph L 0)
        (ne 1 4 (by decide)) (by simpa using rot 3) (by simpa using rot 4)
        (Or.inl (by simpa [gapWord] using pat 1))
        (Or.inr (by simpa [gapWord] using pat 3)) (by decide) right opposite.symm
  · intro left
    constructor
    · intro opposite
      exact vacancy_pairs_separate M
        (port_adj M.graph L 0) (port_adj M.graph L 1)
        (port_adj M.graph L 2) (port_adj M.graph L 3)
        (ne 0 2 (by decide)) (by simpa using rot 1) (by simpa using rot 2)
        (Or.inl (by simpa [gapWord] using pat 0))
        (Or.inl (by simpa [gapWord] using pat 1)) (by decide) opposite.symm left
    · exact vacancy_pairs_separate M
        (port_adj M.graph L 1) (port_adj M.graph L 2)
        (port_adj M.graph L 3) (port_adj M.graph L 4)
        (ne 1 3 (by decide)) (by simpa using rot 2) (by simpa using rot 3)
        (Or.inl (by simpa [gapWord] using pat 1))
        (Or.inl (by simpa [gapWord] using pat 2)) (by decide) left

/-- Normalized native spherical degree-five mobility. No independent separation
premise remains: every chosen actual neighbour is reachable by optional K then S,
unless the original hole has a pure fill within one swap. -/
theorem vacancy_mobility_normalized {h : Fin n} (L : FiveLink M.graph h)
    {c : Fin n → Fin 4} (hc : ProperOff M.graph h c) (pat : Pattern M.graph L c)
    (rot : ∀ i : Fin 5,
      M.rotation.next ⟨(h,L.port i),port_adj M.graph L i⟩ =
        ⟨(h,L.port (i+1)),port_adj M.graph L (i+1)⟩) :
    PureFill M.graph h c 1 ∨ ∀ u, M.Adj h u → Approach M.graph h c u :=
  local_alternative M.graph L hc pat (vacancy_alternation M L pat rot)

end SimpleGraph.SphericalMap
