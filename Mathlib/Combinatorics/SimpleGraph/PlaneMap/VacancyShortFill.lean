module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancySlide
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Logic.Equiv.Basic

@[expose] public section
namespace SimpleGraph.VacancyShortFill
open VacancySlide
variable {V C : Type*} (G : SimpleGraph V)

/-- A currently available fill colour. -/
def Missing (h : V) (c : V → C) (x : C) : Prop :=
  ∀ ⦃v⦄, G.Adj h v → c v ≠ x

def Target (h : V) (c : V → C) : Prop := ∃ x, Missing G h c x

def Active (h : V) (c : V → C) (a b : C) (v : V) : Prop :=
  v ≠ h ∧ (c v = a ∨ c v = b)

/-- The actual two-colour graph in the deletion; all excluded vertices are isolated. -/
def pairGraph (h : V) (c : V → C) (a b : C) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ Active h c a b u ∧ Active h c a b v
  symm := ⟨fun _ _ e => ⟨e.1.symm, e.2.2, e.2.1⟩⟩
  loopless := ⟨fun _ e => e.1.ne rfl⟩

/-- One entire connected component, with an active seed. -/
def Whole (h : V) (c : V → C) (a b : C) (S : Set V) : Prop :=
  ∃ s, Active h c a b s ∧ ∀ v, v ∈ S ↔ (pairGraph G h c a b).Reachable s v

noncomputable def swap [DecidableEq C] (c : V → C) (a b : C) (S : Set V) : V → C :=
  by classical exact fun v => if v ∈ S then Equiv.swap a b (c v) else c v

lemma reachable_invariant {H : SimpleGraph V} {P : V → Prop}
    (closed : ∀ u v, H.Adj u v → P u → P v) {s v : V}
    (hs : P s) (hv : H.Reachable s v) : P v := by
  obtain ⟨p⟩ := hv
  revert hs
  induction p with
  | nil => exact id
  | cons e p ih => intro hs; exact ih (closed _ _ e hs)

lemma whole_active {h : V} {c : V → C} {a b : C} {S : Set V}
    (hS : Whole G h c a b S) {v : V} (hv : v ∈ S) : Active h c a b v := by
  obtain ⟨s,hs,hmem⟩ := hS
  exact reachable_invariant (H := pairGraph G h c a b)
    (P := Active h c a b) (fun _ _ e _ => e.2.2) hs ((hmem v).mp hv)

lemma whole_closed {h : V} {c : V → C} {a b : C} {S : Set V}
    (hS : Whole G h c a b S) {v w : V}
    (hv : v ∈ S) (e : G.Adj v w) (hw : Active h c a b w) : w ∈ S := by
  obtain ⟨s,hs,hmem⟩ := hS
  apply (hmem w).mpr
  exact ((hmem v).mp hv).trans (Adj.reachable ⟨e,whole_active G ⟨s,hs,hmem⟩ hv,hw⟩)

lemma whole_component (h : V) (c : V → C) (a b : C) (s : V)
    (hs : Active h c a b s) :
    Whole G h c a b {v | (pairGraph G h c a b).Reachable s v} := ⟨s,hs,fun _ => Iff.rfl⟩

lemma whole_singleton {h u : V} {c : V → C} {a b : C}
    (hu : Active h c a b u)
    (isolated : ∀ v, G.Adj u v → v ≠ h → c v ≠ a ∧ c v ≠ b) :
    Whole G h c a b {u} := by
  refine ⟨u,hu,fun v => ?_⟩
  constructor
  · intro hv; have hv' : v = u := hv; subst v; exact Reachable.rfl
  · intro hv
    apply reachable_invariant (P := fun v => v = u) (s := u) (v := v) ?_ rfl hv
    intro z w e hz
    subst z
    have hn := isolated w e.1 e.2.2.1
    rcases e.2.2.2 with ha | hb
    · exact (hn.1 ha).elim
    · exact (hn.2 hb).elim

lemma swap_out [DecidableEq C] {c : V → C} {a b : C} {S : Set V} {v : V}
    (hv : v ∉ S) : swap c a b S v = c v := by classical simp [swap,hv]

lemma swap_in [DecidableEq C] {c : V → C} {a b : C} {S : Set V} {v : V}
    (hv : v ∈ S) : swap c a b S v = Equiv.swap a b (c v) := by classical simp [swap,hv]

lemma swap_other [DecidableEq C] {c : V → C} {a b : C} {S : Set V} {v : V}
    (ha : c v ≠ a) (hb : c v ≠ b) : swap c a b S v = c v := by
  classical
  by_cases hv : v ∈ S
  · rw [swap_in hv]; exact Equiv.swap_apply_of_ne_of_ne ha hb
  · exact swap_out hv

lemma swap_eq_iff [DecidableEq C] {c : V → C} {a b : C} {S : Set V} {v : V}
    (hv : v ∈ S) (x : C) : swap c a b S v = x ↔ c v = Equiv.swap a b x := by
  rw [swap_in hv,Equiv.swap_apply_eq_iff]

lemma properOff_swap [DecidableEq C] {h : V} {c : V → C} {a b : C} {S : Set V}
    (hc : ProperOff G h c) (hS : Whole G h c a b S) :
    ProperOff G h (swap c a b S) := by
  classical
  intro v w e hvh hwh
  by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
  · rw [swap_in hv,swap_in hw]
    exact (Equiv.swap a b).injective.ne (hc e hvh hwh)
  · rw [swap_in hv,swap_out hw]
    have hout : c w ≠ a ∧ c w ≠ b := by
      constructor <;> intro he
      · exact hw (whole_closed G hS hv e ⟨hwh,Or.inl he⟩)
      · exact hw (whole_closed G hS hv e ⟨hwh,Or.inr he⟩)
    rw [← Equiv.swap_apply_of_ne_of_ne hout.1 hout.2]
    exact (Equiv.swap a b).injective.ne (hc e hvh hwh)
  · rw [swap_out hv,swap_in hw]
    have hout : c v ≠ a ∧ c v ≠ b := by
      constructor <;> intro he
      · exact hv (whole_closed G hS hw e.symm ⟨hvh,Or.inl he⟩)
      · exact hv (whole_closed G hS hw e.symm ⟨hvh,Or.inr he⟩)
    rw [← Equiv.swap_apply_of_ne_of_ne hout.1 hout.2]
    exact (Equiv.swap a b).injective.ne (hc e hvh hwh)
  · rw [swap_out hv,swap_out hw]; exact hc e hvh hwh

/-- Actual Kempe move, not a black-box target-conversion relation. -/
def KempeStep [DecidableEq C] (h : V) (c d : V → C) : Prop :=
  ∃ a b S, a ≠ b ∧ Whole G h c a b S ∧ d = swap c a b S

lemma terminal_slide [DecidableEq V] [DecidableEq C] {h u : V} {c : V → C}
    (hc : ProperOff G h c) (hu : G.Adj h u) (unique : UniqueAt G h u c)
    (filled : Target G u (slide h u c)) :
    ∃ d, KempeStep G h c d ∧ ProperOff G h d ∧ Target G h d := by
  classical
  obtain ⟨x,hx⟩ := filled
  have hax : c u ≠ x := by simpa using hx hu.symm
  have comp : Whole G h c (c u) x {u} := by
    apply whole_singleton G ⟨hu.ne.symm,Or.inl rfl⟩
    intro v e hv
    refine ⟨(hc e hu.ne.symm hv).symm,?_⟩
    simpa [slide,hv] using hx e
  refine ⟨swap c (c u) x {u},⟨c u,x,{u},hax,comp,rfl⟩,
    properOff_swap G hc comp, c u, ?_⟩
  intro v e he
  by_cases hv : v = u
  · subst v
    rw [swap_in (by simp),Equiv.swap_apply_left] at he
    exact hax he.symm
  · rw [swap_out (by simpa)] at he
    exact hv (unique e he)

lemma swap_preserves_eq [DecidableEq C] {c : V → C} {a b x : C} {S : Set V}
    (ha : x ≠ a) (hb : x ≠ b) (v : V) : swap c a b S v = x ↔ c v = x := by
  classical
  by_cases hv : v ∈ S
  · rw [swap_eq_iff hv,Equiv.swap_apply_of_ne_of_ne ha hb]
  · rw [swap_out hv]

lemma one_swap_target [DecidableEq C] {h u : V} {c : V → C} {rho : C}
    (hc : ProperOff G h c) (hu : G.Adj h u) (unique : UniqueAt G h u c)
    (hne : c u ≠ rho)
    (separated : ∀ v, G.Adj h v → c v = rho →
      ¬ (pairGraph G h c (c u) rho).Reachable u v) :
    ∃ d, KempeStep G h c d ∧ ProperOff G h d ∧ Target G h d := by
  classical
  let J : Set V := {v | (pairGraph G h c (c u) rho).Reachable u v}
  have hj : Whole G h c (c u) rho J := whole_component G h c (c u) rho u
    ⟨hu.ne.symm,Or.inl rfl⟩
  refine ⟨swap c (c u) rho J,⟨c u,rho,J,hne,hj,rfl⟩,
    properOff_swap G hc hj,c u,?_⟩
  intro v e he
  by_cases hv : v ∈ J
  · have he' : c v = rho := by
      apply (swap_eq_iff hv (c u)).mp at he
      simpa using he
    exact separated v e he' hv
  · rw [swap_out hv] at he
    have hvu := unique e he
    subst v
    exact hv Reachable.rfl

/-- The noncommuting slide--Kempe cases collapse to one original Kempe move. -/
lemma slide_swap_same [DecidableEq V] [DecidableEq C] {h u : V} {c : V → C}
    {rho : C} {S : Set V}
    (hc : ProperOff G h c) (hu : G.Adj h u) (unique : UniqueAt G h u c)
    (hne : c u ≠ rho) (hS : Whole G u (slide h u c) (c u) rho S)
    (filled : Target G u (swap (slide h u c) (c u) rho S)) :
    ∃ d, KempeStep G h c d ∧ ProperOff G h d ∧ Target G h d := by
  classical
  obtain ⟨x,hx⟩ := filled
  by_cases hxa : x = c u
  · subst x
    have hhin : h ∈ S := by
      by_contra hh
      have he := hx hu.symm
      rw [swap_out hh,slide_at] at he
      exact he rfl
    have neighbor_not : ∀ v, G.Adj u v → v ≠ h → c v = rho → v ∉ S := by
      intro v e hv he hin
      have hm := hx e
      rw [swap_in hin,slide_away h u c hv,he,Equiv.swap_apply_right] at hm
      exact hm rfl
    have old_closed : ∀ v w, (pairGraph G h c (c u) rho).Adj v w → v ∉ S → w ∉ S := by
      intro v w e hv hw
      by_cases hvu : v = u
      · subst v
        have hcol : c w = rho := by
          rcases e.2.2.2 with ha | hb
          · exact ((hc e.1 hu.ne.symm e.2.2.1) ha.symm).elim
          · exact hb
        exact neighbor_not w e.1 e.2.2.1 hcol hw
      · have vact : Active u (slide h u c) (c u) rho v := by
          refine ⟨hvu,?_⟩; rw [slide_away h u c e.2.1.1]; exact e.2.1.2
        exact hv (whole_closed G hS hw e.1.symm vact)
    apply one_swap_target G hc hu unique hne
    intro v e he hv
    have hnot : v ∉ S := reachable_invariant old_closed
      (fun hin => (whole_active G hS hin).1 rfl) hv
    have hvu : v ≠ u := by intro h; subst v; exact hne he
    have vact : Active u (slide h u c) (c u) rho v := by
      refine ⟨hvu,Or.inr ?_⟩; rw [slide_away h u c e.ne.symm]; exact he
    exact hnot (whole_closed G hS hhin e vact)
  · by_cases hxr : x = rho
    · subst x
      have hhout : h ∉ S := by
        intro hh
        have he := hx hu.symm
        rw [swap_in hh,slide_at,Equiv.swap_apply_left] at he
        exact he rfl
      have neighbor_in : ∀ v, G.Adj u v → v ≠ h → c v = rho → v ∈ S := by
        intro v e hv he
        by_contra hout
        have hm := hx e
        rw [swap_out hout,slide_away h u c hv,he] at hm
        exact hm rfl
      have old_closed : ∀ v w, (pairGraph G h c (c u) rho).Adj v w →
          (v = u ∨ v ∈ S) → (w = u ∨ w ∈ S) := by
        intro v w e hv
        by_cases hwu : w = u
        · exact Or.inl hwu
        · apply Or.inr
          rcases hv with rfl | hv
          · have hcol : c w = rho := by
              rcases e.2.2.2 with ha | hb
              · exact ((hc e.1 hu.ne.symm e.2.2.1) ha.symm).elim
              · exact hb
            exact neighbor_in w e.1 e.2.2.1 hcol
          · have wact : Active u (slide h u c) (c u) rho w := by
              refine ⟨hwu,?_⟩; rw [slide_away h u c e.2.2.1]; exact e.2.2.2
            exact whole_closed G hS hv e.1 wact
      apply one_swap_target G hc hu unique hne
      intro v e he hv
      have hv' : v = u ∨ v ∈ S := reachable_invariant old_closed (Or.inl rfl) hv
      have hvu : v ≠ u := by intro h; subst v; exact hne he
      have hin := hv'.resolve_left hvu
      have hact : Active u (slide h u c) (c u) rho h := ⟨hu.ne,Or.inl (slide_at h u c)⟩
      exact hhout (whole_closed G hS hin e.symm hact)
    · have hax : c u ≠ x := Ne.symm hxa
      have comp : Whole G h c (c u) x {u} := by
        apply whole_singleton G ⟨hu.ne.symm,Or.inl rfl⟩
        intro v e hv
        refine ⟨(hc e hu.ne.symm hv).symm,?_⟩
        intro he
        have hm := hx e
        have hcv : slide h u c v = x := by rw [slide_away h u c hv]; exact he
        have hn1 : slide h u c v ≠ c u := by rw [hcv]; exact hxa
        have hn2 : slide h u c v ≠ rho := by rw [hcv]; exact hxr
        rw [swap_other hn1 hn2,hcv] at hm
        exact hm rfl
      refine ⟨swap c (c u) x {u},⟨c u,x,{u},hax,comp,rfl⟩,
        properOff_swap G hc comp,c u,?_⟩
      intro v e he
      by_cases hv : v = u
      · subst v; rw [swap_in (by simp),Equiv.swap_apply_left] at he; exact hax he.symm
      · rw [swap_out (by simpa)] at he; exact hv (unique e he)

lemma active_slide_eq [DecidableEq V] {h u : V} {c : V → C} {a b : C}
    (ha : c u ≠ a) (hb : c u ≠ b) (v : V) :
    Active h c a b v ↔ Active u (slide h u c) a b v := by
  by_cases hvh : v = h
  · subst v; simp [Active,slide,ha,hb]
  · by_cases hvu : v = u
    · subst v; simp [Active,ha,hb]
    · simp [Active,slide,hvh,hvu]

lemma pairGraph_slide_eq [DecidableEq V] {h u : V} {c : V → C} {a b : C}
    (ha : c u ≠ a) (hb : c u ≠ b) :
    pairGraph G h c a b = pairGraph G u (slide h u c) a b := by
  ext v w
  change (G.Adj v w ∧ Active h c a b v ∧ Active h c a b w) ↔
    (G.Adj v w ∧ Active u (slide h u c) a b v ∧ Active u (slide h u c) a b w)
  rw [active_slide_eq ha hb,active_slide_eq ha hb]

lemma swap_slide_commute [DecidableEq V] [DecidableEq C] {h u : V} {c : V → C}
    {a b : C} {S : Set V}
    (ha : c u ≠ a) (hb : c u ≠ b)
    (hS : Whole G u (slide h u c) a b S) :
    swap (slide h u c) a b S = slide h u (swap c a b S) := by
  classical
  have huout : u ∉ S := fun hs => (whole_active G hS hs).1 rfl
  have hhout : h ∉ S := by
    intro hs
    have hc := (whole_active G hS hs).2
    rw [slide_at] at hc
    exact hc.elim ha hb
  funext v
  by_cases hvh : v = h
  · subst v; rw [swap_out hhout,slide_at,slide_at,swap_out huout]
  · rw [slide_away h u _ hvh]
    by_cases hv : v ∈ S
    · rw [swap_in hv,swap_in hv,slide_away h u c hvh]
    · rw [swap_out hv,swap_out hv,slide_away h u c hvh]

lemma whole_pair_comm {h : V} {c : V → C} {a b : C} {S : Set V}
    (hS : Whole G h c a b S) : Whole G h c b a S := by
  have hg : pairGraph G h c a b = pairGraph G h c b a := by
    ext v w; simp only [pairGraph,Active,or_comm]
  obtain ⟨s,hs,hm⟩ := hS
  refine ⟨s,⟨hs.1,hs.2.symm⟩,?_⟩
  intro v; rw [←hg]; exact hm v

lemma swap_pair_comm [DecidableEq C] (c : V → C) (a b : C) (S : Set V) :
    swap c a b S = swap c b a S := by
  classical
  funext v; unfold swap
  rw [Equiv.swap_comm a b]

/-- Concrete pure paths at a fixed hole, indexed by their exact number of moves. -/
inductive PurePath [DecidableEq C] (h : V) : Nat → (V → C) → (V → C) → Prop
  | nil (c) : PurePath h 0 c c
  | cons {n c d e} : KempeStep G h c d → PurePath h n d e → PurePath h (n+1) c e

def PureFill [DecidableEq C] (h : V) (c : V → C) (bound : Nat) : Prop :=
  ∃ n, n ≤ bound ∧ ∃ d, PurePath G h n c d ∧ Target G h d

lemma pureFill_one [DecidableEq C] {h : V} {c : V → C}
    (hh : ∃ d, KempeStep G h c d ∧ ProperOff G h d ∧ Target G h d) :
    PureFill G h c 1 := by
  obtain ⟨d,step,_,target⟩ := hh
  exact ⟨1,le_rfl,d,.cons step (.nil d),target⟩

lemma pureFill_mono [DecidableEq C] {h : V} {c : V → C} {m n : Nat}
    (hp : PureFill G h c m) (hm : m ≤ n) : PureFill G h c n := by
  obtain ⟨k,hk,d,path,ht⟩ := hp
  exact ⟨k,hk.trans hm,d,path,ht⟩

/-- Full slide--Kempe conversion, with no degree or palette-size hypothesis. -/
lemma slide_kempe [DecidableEq V] [DecidableEq C] {h u : V} {c d : V → C}
    (hc : ProperOff G h c) (hu : G.Adj h u) (unique : UniqueAt G h u c)
    (step : KempeStep G u (slide h u c) d) (filled : Target G u d) :
    PureFill G h c 2 := by
  classical
  obtain ⟨a,b,S,hab,hS,rfl⟩ := step
  by_cases ha : c u = a
  · subst a
    exact pureFill_mono G (pureFill_one G (slide_swap_same G hc hu unique hab hS filled)) (by decide)
  · by_cases hb : c u = b
    · subst b
      have hs := whole_pair_comm G hS
      rw [swap_pair_comm] at filled
      exact pureFill_mono G (pureFill_one G (slide_swap_same G hc hu unique hab.symm hs filled)) (by decide)
    · have hgraph := pairGraph_slide_eq G (h := h) ha hb
      have hS' : Whole G h c a b S := by
        obtain ⟨s,hs,hm⟩ := hS
        refine ⟨s,(active_slide_eq ha hb s).mpr hs,?_⟩
        intro v; rw [hgraph]; exact hm v
      have first : KempeStep G h c (swap c a b S) := ⟨a,b,S,hab,hS',rfl⟩
      have hc' := properOff_swap G hc hS'
      have huni : UniqueAt G h u (swap c a b S) := by
        intro v e hv
        rw [swap_other ha hb] at hv
        exact unique e ((swap_preserves_eq ha hb v).mp hv)
      rw [swap_slide_commute G ha hb hS] at filled
      obtain ⟨e,second,_,he⟩ := terminal_slide G hc' hu huni filled
      exact ⟨2,le_rfl,e,.cons first (.cons second (.nil e)),he⟩

lemma kempe_proper [DecidableEq C] {h : V} {c d : V → C}
    (hc : ProperOff G h c) (step : KempeStep G h c d) : ProperOff G h d := by
  obtain ⟨a,b,S,_,hS,rfl⟩ := step
  exact properOff_swap G hc hS

/-- Mixed moves on actual hole/function states. -/
inductive MixedStep [DecidableEq V] [DecidableEq C] :
    (V × (V → C)) → (V × (V → C)) → Prop
  | kempe {h c d} : KempeStep G h c d → MixedStep (h,c) (h,d)
  | slide {h u c} : G.Adj h u → UniqueAt G h u c →
      MixedStep (h,c) (u,VacancySlide.slide h u c)

inductive MixedPath [DecidableEq V] [DecidableEq C] :
    Nat → (V × (V → C)) → (V × (V → C)) → Prop
  | nil (s) : MixedPath 0 s s
  | cons {n s t v} : MixedStep G s t → MixedPath n t v → MixedPath (n+1) s v

lemma mixed_one [DecidableEq V] [DecidableEq C] {h z : V} {c d : V → C}
    (hc : ProperOff G h c) (step : MixedStep G (h,c) (z,d))
    (filled : Target G z d) : PureFill G h c 1 := by
  cases step with
  | kempe hk => exact ⟨1,le_rfl,d,.cons hk (.nil d),filled⟩
  | slide hu unique => exact pureFill_one G (terminal_slide G hc hu unique filled)

lemma mixed_two [DecidableEq V] [DecidableEq C] {h : V} {c : V → C}
    {s t : V × (V → C)} (hc : ProperOff G h c)
    (first : MixedStep G (h,c) s) (second : MixedStep G s t)
    (filled : Target G t.1 t.2) : PureFill G h c 2 := by
  cases first with
  | @kempe h c d hk =>
    have hd := kempe_proper G hc hk
    cases second with
    | @kempe _ _ e hk' => exact ⟨2,le_rfl,e,.cons hk (.cons hk' (.nil e)),filled⟩
    | slide hu unique =>
      obtain ⟨e,he,_,ht⟩ := terminal_slide G hd hu unique filled
      exact ⟨2,le_rfl,e,.cons hk (.cons he (.nil e)),ht⟩
  | slide hu unique =>
    have hd := properOff_slide G hc unique
    cases second with
    | kempe hk => exact slide_kempe G hc hu unique hk filled
    | slide hv unique' =>
      obtain ⟨e,he,_,ht⟩ := terminal_slide G hd hv unique' filled
      exact slide_kempe G hc hu unique he ht

/-- Any mixed path of length at most two has an original-hole pure replacement
of no greater length. The replacement need not have exactly the supplied length. -/
theorem short_fill [DecidableEq V] [DecidableEq C] {h : V} {c : V → C}
    {n : Nat} {t : V × (V → C)} (hc : ProperOff G h c)
    (hn : n ≤ 2) (path : MixedPath G n (h,c) t)
    (filled : Target G t.1 t.2) : PureFill G h c n := by
  cases n with
  | zero =>
    cases path
    exact ⟨0,le_rfl,c,.nil c,filled⟩
  | succ n =>
    cases n with
    | zero =>
      cases path with
      | cons first rest =>
        cases rest
        exact mixed_one G hc first filled
    | succ n =>
      cases n with
      | zero =>
        cases path with
        | cons first rest =>
          cases rest with
          | cons second rest =>
            cases rest
            exact mixed_two G hc first second filled
      | succ n => omega

lemma purePath_mixed [DecidableEq V] [DecidableEq C] {h : V} {c d : V → C} {n : Nat}
    (path : PurePath G h n c d) : MixedPath G n (h,c) (h,d) := by
  induction path with
  | nil c => exact .nil (h,c)
  | cons step rest ih => exact .cons (.kempe step) ih

def MixedOptimal [DecidableEq V] [DecidableEq C] (h : V) (c : V → C) (n : Nat) : Prop :=
  (∃ t, MixedPath G n (h,c) t ∧ Target G t.1 t.2) ∧
  ∀ m, m < n → ¬ ∃ t, MixedPath G m (h,c) t ∧ Target G t.1 t.2

def PureOptimal [DecidableEq C] (h : V) (c : V → C) (n : Nat) : Prop :=
  (∃ d, PurePath G h n c d ∧ Target G h d) ∧
  ∀ m, m < n → ¬ ∃ d, PurePath G h m c d ∧ Target G h d

/-- Exact minimum-distance equality, expressed without arbitrary choice of
infinite-distance sentinels or padding of nonminimal paths. -/
theorem optimal_short [DecidableEq V] [DecidableEq C] {h : V} {c : V → C} {n : Nat}
    (hc : ProperOff G h c) (hn : n ≤ 2) (optimal : MixedOptimal G h c n) :
    PureOptimal G h c n := by
  obtain ⟨⟨t,path,ht⟩,minimal⟩ := optimal
  obtain ⟨m,hm,d,pure,hd⟩ := short_fill G hc hn path ht
  have hmn : m = n := by
    by_contra hne
    exact minimal m (lt_of_le_of_ne hm hne) ⟨(h,d),purePath_mixed G pure,hd⟩
  subst m
  refine ⟨⟨d,pure,hd⟩,?_⟩
  intro k hk ⟨e,pe,he⟩
  exact minimal k hk ⟨(h,e),purePath_mixed G pe,he⟩

lemma PurePath.proper [DecidableEq C] {h : V} {c d : V → C} {n : Nat}
    (path : PurePath G h n c d) (hc : ProperOff G h c) : ProperOff G h d := by
  induction path with
  | nil => exact hc
  | cons step rest ih => exact ih (kempe_proper G hc step)

lemma MixedPath.proper [DecidableEq V] [DecidableEq C] {s t : V × (V → C)} {n : Nat}
    (path : MixedPath G n s t) (hc : ProperOff G s.1 s.2) : ProperOff G t.1 t.2 := by
  induction path with
  | nil => exact hc
  | cons step rest ih =>
    apply ih
    cases step with
    | kempe step => exact kempe_proper G hc step
    | slide adj unique => exact properOff_slide G hc unique

end SimpleGraph.VacancyShortFill
