module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyShortFill

@[expose] public section
namespace SimpleGraph.VacancyCliqueLift
open VacancySlide VacancyShortFill
variable {V C : Type*} (G : SimpleGraph V)

/-- The induced side on the same vertex type; outside vertices are isolated. -/
def sideGraph (A : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ A ∧ v ∈ A
  symm := ⟨fun _ _ e => ⟨e.1.symm,e.2.2,e.2.1⟩⟩
  loopless := ⟨fun _ e => e.1.ne rfl⟩

/-- Every edge leaving the side starts on its interface. -/
def Boundary (A F : Set V) : Prop :=
  F ⊆ A ∧ ∀ u v, u ∈ A → v ∉ A → G.Adj u v → u ∈ F

/-- Pairwise adjacency, including all interface vertices, not just a cycle. -/
def Clique (F : Set V) : Prop :=
  ∀ u v, u ∈ F → v ∈ F → u ≠ v → G.Adj u v

lemma pair_le (A : Set V) (h : V) (c : V → C) (a b : C) :
    pairGraph (sideGraph G A) h c a b ≤ pairGraph G h c a b :=
  fun _ _ e => ⟨e.1.1,e.2⟩

/-- A whole bichromatic component restricts to one side component at a clique separator.
The hole may itself lie on the separator. -/
theorem component_restriction {A F : Set V} (bd : Boundary G A F) (cl : Clique G F)
    {h s v : V} {c : V → C} {a b : C} (hs : s ∈ A)
    (active : Active h c a b s) (hv : v ∈ A) :
    (pairGraph G h c a b).Reachable s v ↔
      (pairGraph (sideGraph G A) h c a b).Reachable s v := by
  let H := pairGraph G h c a b
  let K := pairGraph (sideGraph G A) h c a b
  have act {x} (hx : K.Reachable s x) : Active h c a b x :=
    reachable_invariant (H := K) (P := Active h c a b)
      (fun _ _ e _ => e.2.2) active hx
  have stay {x} (hx : K.Reachable s x) : x ∈ A :=
    reachable_invariant (H := K) (P := fun z => z ∈ A)
      (fun _ _ e _ => e.1.2.2) hs hx
  constructor
  · intro path
    by_cases touch : ∃ f, f ∈ F ∧ K.Reachable s f
    · obtain ⟨f,hf,reachf⟩ := touch
      have boundary_reach {x} (hx : x ∈ F) (ha : Active h c a b x) :
          K.Reachable s x := by
        by_cases eq : f = x
        · simpa [eq] using reachf
        · exact reachf.trans (Adj.reachable
            ⟨⟨cl f x hf hx eq,bd.1 hf,bd.1 hx⟩,act reachf,ha⟩)
      have invariant : ∀ u w, H.Adj u w → (u ∈ A → K.Reachable s u) →
          (w ∈ A → K.Reachable s w) := by
        intro u w edge ih hw
        by_cases hu : u ∈ A
        · exact (ih hu).trans (Adj.reachable ⟨⟨edge.1,hu,hw⟩,edge.2⟩)
        · exact boundary_reach (bd.2 w u hw hu edge.1.symm) edge.2.2
      exact reachable_invariant (H := H) (P := fun z => z ∈ A → K.Reachable s z)
        invariant (fun _ => Reachable.rfl) path hv
    · have invariant : ∀ u w, H.Adj u w → K.Reachable s u → K.Reachable s w := by
        intro u w edge ih
        have hu := stay ih
        have hw : w ∈ A := by
          by_contra hn
          exact touch ⟨u,bd.2 u w hu hn edge.1,ih⟩
        exact ih.trans (Adj.reachable ⟨⟨edge.1,hu,hw⟩,edge.2⟩)
      exact reachable_invariant (H := H) (P := fun z => K.Reachable s z)
        invariant Reachable.rfl path
  · exact Reachable.mono (pair_le G A h c a b)

/-- Lift a chosen side component to the actual global component of its seed. -/
theorem whole_lift {A F : Set V} (bd : Boundary G A F) (cl : Clique G F)
    {h : V} {c : V → C} {a b : C} {S : Set V}
    (inside : S ⊆ A) (whole : Whole (sideGraph G A) h c a b S) :
    ∃ U, Whole G h c a b U ∧ ∀ v, v ∈ A → (v ∈ U ↔ v ∈ S) := by
  obtain ⟨s,active,mem⟩ := whole
  have hs : s ∈ A := inside ((mem s).mpr Reachable.rfl)
  refine ⟨{v | (pairGraph G h c a b).Reachable s v},
    whole_component G h c a b s active,?_⟩
  intro v hv
  exact (component_restriction G bd cl hs active hv).trans (mem v).symm

/-- Actual side moves must use a component on the side, not an artificial isolated
vertex of the ambient spanning graph. -/
def SideKempeStep [DecidableEq C] (A : Set V) (h : V) (c d : V → C) : Prop :=
  ∃ a b S, a ≠ b ∧ Whole (sideGraph G A) h c a b S ∧ S ⊆ A ∧ d = swap c a b S

/-- The lifted swap agrees with the side swap on every side vertex. -/
theorem kempe_lift [DecidableEq C] {A F : Set V}
    (bd : Boundary G A F) (cl : Clique G F) {h : V}
    {c d : V → C} (step : SideKempeStep G A h c d) :
    ∃ e, KempeStep G h c e ∧ ∀ v, v ∈ A → e v = d v := by
  classical
  obtain ⟨a,b,S,hab,whole,inside,rfl⟩ := step
  obtain ⟨U,hU,agreement⟩ := whole_lift G bd cl inside whole
  refine ⟨swap c a b U,⟨a,b,U,hab,hU,rfl⟩,?_⟩
  intro v hv
  simp only [swap]
  rw [agreement v hv]

/-- Equality on the side determines its whole bichromatic graph. -/
lemma pair_side_congr {A : Set V} {h : V} {c g : V → C} {a b : C}
    (eq : ∀ v, v ∈ A → g v = c v) :
    pairGraph (sideGraph G A) h g a b = pairGraph (sideGraph G A) h c a b := by
  ext u v
  constructor <;> intro e
  · exact ⟨e.1,⟨e.2.1.1,by simpa [eq u e.1.2.1] using e.2.1.2⟩,
      ⟨e.2.2.1,by simpa [eq v e.1.2.2] using e.2.2.2⟩⟩
  · exact ⟨e.1,⟨e.2.1.1,by simpa [eq u e.1.2.1] using e.2.1.2⟩,
      ⟨e.2.2.1,by simpa [eq v e.1.2.2] using e.2.2.2⟩⟩

lemma side_step_congr [DecidableEq C] {A : Set V} {h : V} {c d g : V → C}
    (eq : ∀ v, v ∈ A → g v = c v) (step : SideKempeStep G A h c d) :
    ∃ e, SideKempeStep G A h g e ∧ ∀ v, v ∈ A → e v = d v := by
  classical
  obtain ⟨a,b,S,hab,whole,inside,rfl⟩ := step
  have whole' : Whole (sideGraph G A) h g a b S := by
    obtain ⟨seed,active,mem⟩ := whole
    have hs := inside ((mem seed).mpr Reachable.rfl)
    refine ⟨seed,⟨active.1,by simpa [eq seed hs] using active.2⟩,?_⟩
    simpa [pair_side_congr G eq] using mem
  refine ⟨swap g a b S,⟨a,b,S,hab,whole',inside,rfl⟩,?_⟩
  intro v hv
  simp only [swap,eq v hv]

/-- The local and global functions may differ off the side after earlier lifts. -/
theorem kempe_lift_agree [DecidableEq C] {A F : Set V}
    (bd : Boundary G A F) (cl : Clique G F) {h : V} {c d g : V → C}
    (eq : ∀ v, v ∈ A → g v = c v) (step : SideKempeStep G A h c d) :
    ∃ e, KempeStep G h g e ∧ ∀ v, v ∈ A → e v = d v := by
  obtain ⟨sideNext,st,agree⟩ := side_step_congr G eq step
  obtain ⟨globalNext,st',agree'⟩ := kempe_lift G bd cl st
  exact ⟨globalNext,st',fun v hv => (agree' v hv).trans (agree v hv)⟩

lemma neighbours_inside {A F : Set V} (bd : Boundary G A F) {h v : V}
    (hh : h ∈ A) (hf : h ∉ F) (edge : G.Adj h v) : v ∈ A := by
  by_contra hn
  exact hf (bd.2 h v hh hn edge)

lemma slide_lift [DecidableEq V] {A F : Set V} (bd : Boundary G A F)
    {h u : V} {c g : V → C} (hh : h ∈ A) (hf : h ∉ F)
    (edge : (sideGraph G A).Adj h u)
    (unique : UniqueAt (sideGraph G A) h u c)
    (eq : ∀ v, v ∈ A → g v = c v) :
    UniqueAt G h u g ∧
      ∀ v, v ∈ A → VacancySlide.slide h u g v = VacancySlide.slide h u c v := by
  constructor
  · intro v ev colours
    have hv := neighbours_inside G bd hh hf ev
    apply unique ⟨ev,hh,hv⟩
    simpa [eq v hv,eq u edge.2.2] using colours
  · intro v hv
    simp only [VacancySlide.slide,eq u edge.2.2,eq v hv]

/-- A genuine side path with every hole strictly away from the interface. -/
inductive InteriorStep [DecidableEq V] [DecidableEq C] (A F : Set V) :
    (V × (V → C)) → (V × (V → C)) → Prop
  | kempe {h c d} : h ∈ A → h ∉ F → SideKempeStep G A h c d →
      InteriorStep A F (h,c) (h,d)
  | slide {h u c} : h ∈ A → h ∉ F → u ∈ A → u ∉ F →
      (sideGraph G A).Adj h u → UniqueAt (sideGraph G A) h u c →
      InteriorStep A F (h,c) (u,VacancySlide.slide h u c)

inductive InteriorPath [DecidableEq V] [DecidableEq C] (A F : Set V) :
    Nat → (V × (V → C)) → (V × (V → C)) → Prop
  | nil {h c} : h ∈ A → h ∉ F → InteriorPath A F 0 (h,c) (h,c)
  | cons {n s t v} : InteriorStep G A F s t → InteriorPath A F n t v →
      InteriorPath A F (n+1) s v

/-- Lift the complete side path, preserving its holes and exact number of moves. -/
theorem interior_path_lift [DecidableEq V] [DecidableEq C] {A F : Set V}
    (bd : Boundary G A F) (cl : Clique G F) {n : Nat} {s t : V × (V → C)} {g : V → C}
    (path : InteriorPath G A F n s t)
    (eq : ∀ v, v ∈ A → g v = s.2 v) :
    ∃ e, MixedPath G n (s.1,g) (t.1,e) ∧ ∀ v, v ∈ A → e v = t.2 v := by
  induction path generalizing g with
  | nil ha hf => exact ⟨g,.nil _,eq⟩
  | @cons n s t v st rest ih =>
    cases st with
    | kempe ha hf step =>
      obtain ⟨next,move,agree⟩ := kempe_lift_agree G bd cl eq step
      obtain ⟨last,rest',agree'⟩ := ih agree
      exact ⟨last,.cons (.kempe move) rest',agree'⟩
    | slide ha hf ua uf edge unique =>
      obtain ⟨unique',agree⟩ := slide_lift G bd ha hf edge unique eq
      obtain ⟨last,rest',agree'⟩ := ih agree
      exact ⟨last,.cons (.slide edge.1 unique') rest',agree'⟩

lemma terminal_interior [DecidableEq V] [DecidableEq C] {A F : Set V}
    {n : Nat} {s t : V × (V → C)} (path : InteriorPath G A F n s t) :
    t.1 ∈ A ∧ t.1 ∉ F := by
  induction path with
  | nil ha hf => exact ⟨ha,hf⟩
  | cons _ _ ih => exact ih

lemma mixed_path_proper [DecidableEq V] [DecidableEq C]
    {n : Nat} {s t : V × (V → C)} (path : MixedPath G n s t)
    (proper : ProperOff G s.1 s.2) : ProperOff G t.1 t.2 := by
  induction path with
  | nil => exact proper
  | cons step _ ih =>
    apply ih
    cases step with
    | kempe k => exact kempe_proper G proper k
    | slide _ unique => exact properOff_slide G proper unique

lemma target_lift {A F : Set V} (bd : Boundary G A F)
    {h : V} {c g : V → C} (ha : h ∈ A) (hf : h ∉ F)
    (eq : ∀ v, v ∈ A → g v = c v) (filled : Target (sideGraph G A) h c) :
    Target G h g := by
  obtain ⟨colour,missing⟩ := filled
  refine ⟨colour,?_⟩
  intro v edge
  have hv := neighbours_inside G bd ha hf edge
  rw [eq v hv]
  exact missing ⟨edge,ha,hv⟩

/-- The whole interior side fill lifts, with properness and a genuine global fill.
This is graph-level composition, with no planarity, degree or palette-size assumption. -/
theorem interior_fill_lift [DecidableEq V] [DecidableEq C] {A F : Set V}
    (bd : Boundary G A F) (cl : Clique G F) {n : Nat} {s t : V × (V → C)}
    {g : V → C} (path : InteriorPath G A F n s t)
    (eq : ∀ v, v ∈ A → g v = s.2 v) (proper : ProperOff G s.1 g)
    (filled : Target (sideGraph G A) t.1 t.2) :
    ∃ e, MixedPath G n (s.1,g) (t.1,e) ∧
      ProperOff G t.1 e ∧ Target G t.1 e := by
  obtain ⟨e,globalPath,agree⟩ := interior_path_lift G bd cl path eq
  obtain ⟨ha,hf⟩ := terminal_interior G path
  exact ⟨e,globalPath,mixed_path_proper G globalPath proper,
    target_lift G bd ha hf agree filled⟩

end SimpleGraph.VacancyCliqueLift
