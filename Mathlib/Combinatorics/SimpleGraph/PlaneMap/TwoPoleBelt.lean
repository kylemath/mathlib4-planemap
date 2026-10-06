module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancySlide
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

@[expose] public section
namespace SimpleGraph.TwoPoleBelt
open VacancySlide

/-- The actual two-pole belt, indexed cyclically; there is no pole--pole edge. -/
inductive Vertex (n : Nat)
  | a | b | u (i : ZMod n) | v (i : ZMod n)
  deriving DecidableEq

open Vertex

def edge {n : Nat} : Vertex n → Vertex n → Prop
  | a,u _ | u _,a | b,v _ | v _,b => True
  | u i,u j | v i,v j => j = i+1 ∨ i = j+1
  | u i,v j => j=i ∨ j=i-1
  | v j,u i => j=i ∨ j=i-1
  | _,_ => False

def graph (n : Nat) : SimpleGraph (Vertex n) where
  Adj x y := x ≠ y ∧ edge x y
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    have he := h.2
    cases x <;> cases y <;> simp_all [edge,or_comm]⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {n : Nat} : DecidableRel (graph n).Adj := fun x y => by
  change Decidable (x ≠ y ∧ edge x y)
  cases x <;> cases y <;> simp only [edge] <;> infer_instance

lemma one_ne_zero {n : Nat} (hn : 5 ≤ n) : (1 : ZMod n) ≠ 0 := by
  intro h; have := ZMod.one_eq_zero_iff.mp h; omega

lemma plus_ne {n : Nat} (hn : 5 ≤ n) (i : ZMod n) : i+1 ≠ i := by
  intro h
  have : (1 : ZMod n) = 0 := by simpa using add_left_cancel (show i+1=i+0 by simpa using h)
  exact one_ne_zero hn this

lemma minus_ne {n : Nat} (hn : 5 ≤ n) (i : ZMod n) : i-1 ≠ i := by
  intro h
  have : i = i+1 := (sub_eq_iff_eq_add).mp h
  exact plus_ne hn i this.symm

/-- Exact upper-ring neighbourhood, not an assumed five-cycle interface. -/
lemma adj_u {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (x : Vertex n) :
    (graph n).Adj (u i) x ↔
    x=a ∨ x=u (i+1) ∨ x=v i ∨ x=v (i-1) ∨ x=u (i-1) := by
  cases x with
  | a => simp [graph,edge]
  | b => simp [graph,edge]
  | u j =>
    simp only [graph,edge,Vertex.u.injEq,ne_eq,reduceCtorEq,false_or]
    have hsecond : i=j+1 ↔ j=i-1 := by rw [eq_sub_iff_add_eq]; exact eq_comm
    rw [hsecond]
    constructor
    · intro h; exact h.2
    · intro h
      refine ⟨?_,h⟩
      rcases h with rfl | rfl
      · exact (plus_ne hn i).symm
      · exact (minus_ne hn i).symm
  | v j => simp [graph,edge]

/-- Exact lower-ring neighbourhood. -/
lemma adj_v {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (x : Vertex n) :
    (graph n).Adj (v i) x ↔
    x=b ∨ x=v (i-1) ∨ x=u i ∨ x=u (i+1) ∨ x=v (i+1) := by
  cases x with
  | a => simp [graph,edge]
  | b => simp [graph,edge]
  | u j =>
    simp only [graph,edge,Vertex.u.injEq,ne_eq,reduceCtorEq,false_or]
    have hsecond : i=j-1 ↔ j=i+1 := by rw [eq_sub_iff_add_eq]; exact eq_comm
    rw [hsecond]
    simp only [not_false_eq_true,true_and,eq_comm,or_false]
  | v j =>
    simp only [graph,edge,Vertex.v.injEq,ne_eq,reduceCtorEq,false_or]
    have hsecond : i=j+1 ↔ j=i-1 := by rw [eq_sub_iff_add_eq]; exact eq_comm
    rw [hsecond]
    constructor
    · intro h; exact h.2.symm
    · intro h
      refine ⟨?_,h.symm⟩
      rcases h with rfl | rfl
      · exact (minus_ne hn i).symm
      · exact (plus_ne hn i).symm

abbrev Colour := Fin 4
abbrev State (n : Nat) := Vertex n × (Vertex n → Colour)

def Target {n : Nat} (h : Vertex n) (c : Vertex n → Colour) : Prop :=
  ∃ x, ∀ v, (graph n).Adj h v → c v ≠ x

/-- Only actual singleton slides, with exact edge and uniqueness conditions. -/
inductive SlidePath {n : Nat} : Nat → State n → State n → Prop
  | nil (s) : SlidePath 0 s s
  | cons {k h x c t} : (graph n).Adj h x → UniqueAt (graph n) h x c →
      SlidePath k (x,slide h x c) t → SlidePath (k+1) (h,c) t

lemma SlidePath.proper {n k : Nat} {s t : State n} (path : SlidePath k s t)
    (hc : ProperOff (graph n) s.1 s.2) : ProperOff (graph n) t.1 t.2 := by
  induction path with
  | nil => exact hc
  | cons adj unique path ih => exact ih (properOff_slide (graph n) hc unique)

/-- An entirely belt-supported walk does not recolour either pole. -/
lemma slide_poles {n : Nat} {h x : Vertex n} {c : Vertex n → Colour}
    (ha : h ≠ a) (hb : h ≠ b) :
    slide h x c a = c a ∧ slide h x c b = c b := by
  exact ⟨slide_away h x c ha.symm,slide_away h x c hb.symm⟩

/-- Pole-colour exclusion on every actually coloured belt vertex. -/
lemma pole_exclusion {n : Nat} {h : Vertex n} {c : Vertex n → Colour}
    (hc : ProperOff (graph n) h c) (ha : h ≠ a) (hb : h ≠ b)
    (ca : c a=0) (cb : c b=1) (i : ZMod n) :
    (u i ≠ h → c (u i) ≠ 0) ∧ (v i ≠ h → c (v i) ≠ 1) := by
  constructor
  · intro hi he
    exact hc (show (graph n).Adj a (u i) by simp [graph,edge]) ha.symm hi (ca.trans he.symm)
  · intro hi he
    exact hc (show (graph n).Adj b (v i) by simp [graph,edge]) hb.symm hi (cb.trans he.symm)

lemma offset_ne {n : Nat} (i : ZMod n) (k : Nat) (hk : 0 < k) (hkn : k < n) :
    i+(k : ZMod n) ≠ i := by
  intro h
  have heq : i+(k : ZMod n)=i+0 := by simpa using h
  have hz : (k : ZMod n) = 0 := add_left_cancel heq
  have hd := (ZMod.natCast_eq_zero_iff k n).mp hz
  have hl := Nat.le_of_dvd hk hd
  omega

lemma unique_u_v {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (c : Vertex n → Colour)
    (ha : c a ≠ c (v i)) (hup : c (u (i+1)) ≠ c (v i))
    (hvm : c (v (i-1)) ≠ c (v i)) (hum : c (u (i-1)) ≠ c (v i)) :
    UniqueAt (graph n) (u i) (v i) c := by
  intro x hx hc
  rcases (adj_u hn i x).mp hx with rfl | rfl | rfl | rfl | rfl
  · exact (ha hc).elim
  · exact (hup hc).elim
  · rfl
  · exact (hvm hc).elim
  · exact (hum hc).elim

lemma unique_v_vnext {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (c : Vertex n → Colour)
    (hb : c b ≠ c (v (i+1))) (hvm : c (v (i-1)) ≠ c (v (i+1)))
    (hui : c (u i) ≠ c (v (i+1))) (hup : c (u (i+1)) ≠ c (v (i+1))) :
    UniqueAt (graph n) (v i) (v (i+1)) c := by
  intro x hx hc
  rcases (adj_v hn i x).mp hx with rfl | rfl | rfl | rfl | rfl
  · exact (hb hc).elim
  · exact (hvm hc).elim
  · exact (hui hc).elim
  · exact (hup hc).elim
  · rfl

lemma unique_v_unext {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (c : Vertex n → Colour)
    (hb : c b ≠ c (u (i+1))) (hvm : c (v (i-1)) ≠ c (u (i+1)))
    (hui : c (u i) ≠ c (u (i+1))) (hvp : c (v (i+1)) ≠ c (u (i+1))) :
    UniqueAt (graph n) (v i) (u (i+1)) c := by
  intro x hx hc
  rcases (adj_v hn i x).mp hx with rfl | rfl | rfl | rfl | rfl
  · exact (hb hc).elim
  · exact (hvm hc).elim
  · exact (hui hc).elim
  · rfl
  · exact (hvp hc).elim

lemma target_v {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (c : Vertex n → Colour) (x : Colour)
    (hb : c b ≠ x) (hvm : c (v (i-1)) ≠ x) (hui : c (u i) ≠ x)
    (hup : c (u (i+1)) ≠ x) (hvp : c (v (i+1)) ≠ x) : Target (v i) c := by
  refine ⟨x,?_⟩
  intro y hy
  rcases (adj_v hn i y).mp hy with rfl | rfl | rfl | rfl | rfl
  · exact hb
  · exact hvm
  · exact hui
  · exact hup
  · exact hvp

/-- Finite-palette forcing; these premises are colour inequalities, not transitions. -/
lemma tight_remaining (rho tau x : Colour) (hr0 : rho ≠ 0) (hr1 : rho ≠ 1)
    (ht0 : tau ≠ 0) (ht1 : tau ≠ 1) (hrt : rho ≠ tau)
    (hx1 : x ≠ 1) (hxr : x ≠ rho) : x=0 ∨ x=tau := by
  fin_cases rho <;> fin_cases tau <;> fin_cases x <;> simp_all

/-- The actual D-opening slide: it fills or forces the next lower vertex to zero.
No step-table or termination hypothesis appears in its premises. -/
lemma doubled_one_first {n : Nat} (hn : 5 ≤ n) (i : ZMod n)
    (c : Vertex n → Colour) (rho tau : Colour)
    (hc : ProperOff (graph n) (u i) c)
    (ca : c a=0) (cb : c b=1)
    (cup : c (u (i+1))=1) (cum : c (u (i-1))=1)
    (cvi : c (v i)=rho) (cvm : c (v (i-1))=tau)
    (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (ht0 : tau ≠ 0)
    (ht1 : tau ≠ 1) (hrt : rho ≠ tau) :
    SlidePath 1 (u i,c) (v i,slide (u i) (v i) c) ∧
    (Target (v i) (slide (u i) (v i) c) ∨ c (v (i+1))=0) := by
  have hstep : UniqueAt (graph n) (u i) (v i) c := by
    apply unique_u_v hn i c
    · rw [ca,cvi]; exact hr0.symm
    · rw [cup,cvi]; exact hr1.symm
    · rw [cvm,cvi]; exact hrt.symm
    · rw [cum,cvi]; exact hr1.symm
  refine ⟨.cons ((adj_u hn i _).mpr (Or.inr (Or.inr (Or.inl rfl)))) hstep (.nil _),?_⟩
  have hx1 : c (v (i+1)) ≠ 1 := by
    exact (pole_exclusion hc (by simp) (by simp) ca cb (i+1)).2 (by simp)
  have hxr : c (v (i+1)) ≠ rho := by
    have he : (graph n).Adj (v (i+1)) (v i) :=
      ((adj_v hn i _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).symm
    simpa [cvi] using hc he (by simp) (by simp)
  rcases tight_remaining rho tau (c (v (i+1))) hr0 hr1 ht0 ht1 hrt hx1 hxr with hx | hx
  · exact Or.inr hx
  · apply Or.inl
    apply target_v hn i (slide (u i) (v i) c) 0
    · simp [slide,cb]
    · simpa [slide,cvm] using ht0
    · simpa [slide,cvi] using hr0
    · simp [slide,cup,plus_ne hn i]
    · simpa [slide,hx] using ht0

lemma SlidePath.append {n k l : Nat} {s t w : State n}
    (p : SlidePath k s t) (q : SlidePath l t w) : SlidePath (k+l) s w := by
  induction p with
  | nil => simpa using q
  | cons adj unique p ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using SlidePath.cons adj unique (ih q)

lemma tight_one (p q x : Colour) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hpq : p ≠ q)
    (hx0 : x ≠ 0) (hxp : x ≠ p) (hxq : x ≠ q) : x=1 := by
  fin_cases p <;> fin_cases q <;> fin_cases x <;> simp_all

/-- Actual three-slide D return, including every forced colour. -/
lemma doubled_one_return {n : Nat} (hn : 5 ≤ n) (i : ZMod n)
    (c : Vertex n → Colour) (rho tau : Colour)
    (hc : ProperOff (graph n) (u i) c)
    (ca : c a=0) (cb : c b=1)
    (cup : c (u (i+1))=1) (cum : c (u (i-1))=1)
    (cvi : c (v i)=rho) (cvm : c (v (i-1))=tau)
    (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (ht0 : tau ≠ 0)
    (ht1 : tau ≠ 1) (hrt : rho ≠ tau) (hx : c (v (i+1))=0) :
    ∃ d p q, SlidePath 3 (u i,c) (u (i+2),d) ∧
      d a=0 ∧ d b=1 ∧ d (u (i+3))=1 ∧ d (u (i+1))=1 ∧
      d (v (i+2))=q ∧ d (v (i+1))=p ∧
      p ≠ 0 ∧ p ≠ 1 ∧ q ≠ 0 ∧ q ≠ 1 ∧ p ≠ q ∧
      d = slide (v (i+1)) (u (i+2)) (slide (v i) (v (i+1)) (slide (u i) (v i) c)) := by
  let p := c (u (i+2))
  let q := c (v (i+2))
  have h2 : i+2 ≠ i := offset_ne i 2 (by decide) (by omega)
  have h3 : i+3 ≠ i := offset_ne i 3 (by decide) (by omega)
  have h20 : (2 : ZMod n) ≠ 0 := by simpa using offset_ne (0 : ZMod n) 2 (by decide) (by omega)
  have h21 : (2 : ZMod n) ≠ 1 := by simpa [one_add_one_eq_two] using plus_ne hn (1 : ZMod n)
  have hi2 : i+1+1=i+2 := by ring
  have hi3 : i+2+1=i+3 := by ring
  have hm : (i+1)-1=i := by ring
  have hp0 : p ≠ 0 :=
    (pole_exclusion hc (by simp) (by simp) ca cb (i+2)).1 (by simpa using h2)
  have hp1 : p ≠ 1 := by
    have adj : (graph n).Adj (u (i+2)) (u (i+1)) := by
      apply Adj.symm
      apply (adj_u hn (i+1) _).mpr
      right; left; rw [hi2]
    have ne := hc adj (by simpa using h2) (by simpa using plus_ne hn i)
    simpa [p,cup] using ne
  have hq1 : q ≠ 1 :=
    (pole_exclusion hc (by simp) (by simp) ca cb (i+2)).2 (by simp)
  have hq0 : q ≠ 0 := by
    have adj : (graph n).Adj (v (i+2)) (v (i+1)) := by
      apply Adj.symm
      apply (adj_v hn (i+1) _).mpr
      right; right; right; right; rw [hi2]
    have ne := hc adj (by simp) (by simp)
    simpa [q,hx] using ne
  have hpq : p ≠ q := by
    exact hc ((adj_u hn (i+2) _).mpr (Or.inr (Or.inr (Or.inl rfl))))
      (by simpa using h2) (by simp)
  have cu3 : c (u (i+3))=1 := by
    apply tight_one p q (c (u (i+3))) hp0 hp1 hq0 hq1 hpq
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (i+3)).1 (by simpa using h3)
    · have adj : (graph n).Adj (u (i+3)) (u (i+2)) := by
        apply Adj.symm
        apply (adj_u hn (i+2) _).mpr
        right; left; rw [hi3]
      exact hc adj (by simpa using h3) (by simpa using h2)
    · have adj : (graph n).Adj (u (i+3)) (v (i+2)) := by
        apply Adj.symm
        apply (adj_v hn (i+2) _).mpr
        right; right; right; left; rw [hi3]
      exact hc adj (by simpa using h3) (by simp)
  let c1 := slide (u i) (v i) c
  let c2 := slide (v i) (v (i+1)) c1
  let d := slide (v (i+1)) (u (i+2)) c2
  have first : SlidePath 1 (u i,c) (v i,c1) :=
    (doubled_one_first hn i c rho tau hc ca cb cup cum cvi cvm hr0 hr1 ht0 ht1 hrt).1
  have unique2 : UniqueAt (graph n) (v i) (v (i+1)) c1 := by
    apply unique_v_vnext hn i c1
    · simp [c1,cb,hx]
    · simpa [c1,slide,cvm,hx] using ht0
    · simpa [c1,slide,cvi,hx] using hr0
    · simp [c1,cup,hx,plus_ne hn i]
  have unique3 : UniqueAt (graph n) (v (i+1)) (u (i+2)) c2 := by
    rw [←hi2]
    apply unique_v_unext hn (i+1) c2
    · simpa [c2,c1,slide,cb,hi2,h2] using hp1.symm
    · simpa [c2,c1,slide,hm,hi2,h2,hx,p] using hp0.symm
    · simpa [c2,c1,slide,cup,hi2,h2,plus_ne hn i] using hp1.symm
    · simpa [c2,c1,slide,hi2,h2,plus_ne hn i] using hpq.symm
  have adj2 : (graph n).Adj (v i) (v (i+1)) :=
    (adj_v hn i _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have adj3 : (graph n).Adj (v (i+1)) (u (i+2)) := by
    apply (adj_v hn (i+1) _).mpr
    right; right; right; left; rw [hi2]
  have path : SlidePath 3 (u i,c) (u (i+2),d) :=
    first.append (.cons adj2 unique2 (.cons adj3 unique3 (.nil _)))
  refine ⟨d,p,q,path,?_,?_,?_,?_,?_,?_,hp0,hp1,hq0,hq1,hpq,rfl⟩
  · simp [d,c2,c1,slide,ca]
  · simp [d,c2,c1,slide,cb]
  · simp [d,c2,c1,slide,cu3,h3]
  · simp [d,c2,c1,slide,cup,plus_ne hn i]
  · simp [d,c2,c1,slide,h20,h21,q]
  · simp [d,c2,c1,slide,h2,p]

lemma unique_v_vprev {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (c : Vertex n → Colour)
    (hb : c b ≠ c (v (i-1))) (hui : c (u i) ≠ c (v (i-1)))
    (hup : c (u (i+1)) ≠ c (v (i-1))) (hvp : c (v (i+1)) ≠ c (v (i-1))) :
    UniqueAt (graph n) (v i) (v (i-1)) c := by
  intro x hx hc
  rcases (adj_v hn i x).mp hx with rfl | rfl | rfl | rfl | rfl
  · exact (hb hc).elim
  · rfl
  · exact (hui hc).elim
  · exact (hup hc).elim
  · exact (hvp hc).elim

lemma tight_force (rho tau x : Colour) (hr0 : rho ≠ 0) (hr1 : rho ≠ 1)
    (ht0 : tau ≠ 0) (ht1 : tau ≠ 1) (hrt : rho ≠ tau)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxt : x ≠ tau) : x=rho := by
  exact (tight_remaining tau rho x ht0 ht1 hr0 hr1 hrt.symm hx1 hxt).resolve_left hx0

lemma tight_zero (rho tau x : Colour) (hr0 : rho ≠ 0) (hr1 : rho ≠ 1)
    (ht0 : tau ≠ 0) (ht1 : tau ≠ 1) (hrt : rho ≠ tau)
    (hx1 : x ≠ 1) (hxr : x ≠ rho) (hxt : x ≠ tau) : x=0 := by
  exact (tight_remaining rho tau x hr0 hr1 ht0 ht1 hrt hx1 hxr).resolve_right hxt

lemma minus_offset_ne {n : Nat} (i : ZMod n) (k : Nat) (hk : 0 < k) (hkn : k < n) :
    i-(k : ZMod n) ≠ i := by
  intro he
  have he' : i+(k : ZMod n)=i := ((sub_eq_iff_eq_add).mp he).symm
  exact offset_ne i k hk hkn he'

/-- The actual A_tau two-slide return. Original input properness forces the
previous zero; the transition itself is a constructed SlidePath. -/
lemma a_tau_return {n : Nat} (hn : 5 ≤ n) (i : ZMod n)
    (c : Vertex n → Colour) (rho tau : Colour)
    (hc : ProperOff (graph n) (v i) c) (ca : c a=0) (cb : c b=1)
    (cvm : c (v (i-1))=tau) (cui : c (u i)=1)
    (cup : c (u (i+1))=rho) (cvp : c (v (i+1))=0)
    (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (ht0 : tau ≠ 0)
    (ht1 : tau ≠ 1) (hrt : rho ≠ tau) :
    ∃ d, SlidePath 2 (v i,c) (v (i-2),d) ∧ d a=0 ∧ d b=1 ∧
      d (u (i-1))=rho ∧ d (v (i-1))=0 ∧
      d = slide (v (i-1)) (v (i-2)) (slide (v i) (v (i-1)) c) := by
  have hm1 : i-1 ≠ i := minus_ne hn i
  have hm2 : i-2 ≠ i := minus_offset_ne i 2 (by decide) (by omega)
  have hmm : (i-1)-1=i-2 := by ring
  have hmp : (i-1)+1=i := by ring
  have cum : c (u (i-1))=rho := by
    apply tight_force rho tau _ hr0 hr1 ht0 ht1 hrt
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (i-1)).1 (by simp)
    · have adj : (graph n).Adj (u (i-1)) (u i) := by
        apply (adj_u hn (i-1) _).mpr
        right; left; rw [hmp]
      simpa [cui] using hc adj (by simp) (by simp)
    · have adj : (graph n).Adj (u (i-1)) (v (i-1)) :=
        (adj_u hn (i-1) _).mpr (Or.inr (Or.inr (Or.inl rfl)))
      simpa [cvm] using hc adj (by simp) (by simpa using hm1)
  have cvmm : c (v (i-2))=0 := by
    apply tight_zero rho tau _ hr0 hr1 ht0 ht1 hrt
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (i-2)).2 (by simpa using hm2)
    · have adj : (graph n).Adj (v (i-2)) (u (i-1)) := by
        apply Adj.symm
        apply (adj_u hn (i-1) _).mpr
        right; right; right; left; rw [hmm]
      simpa [cum] using hc adj (by simpa using hm2) (by simp)
    · have adj : (graph n).Adj (v (i-2)) (v (i-1)) := by
        apply Adj.symm
        apply (adj_v hn (i-1) _).mpr
        right; left; rw [hmm]
      simpa [cvm] using hc adj (by simpa using hm2) (by simpa using hm1)
  let c1 := slide (v i) (v (i-1)) c
  let d := slide (v (i-1)) (v (i-2)) c1
  have unique1 : UniqueAt (graph n) (v i) (v (i-1)) c := by
    apply unique_v_vprev hn i c
    · rw [cb,cvm]; exact ht1.symm
    · rw [cui,cvm]; exact ht1.symm
    · rw [cup,cvm]; exact hrt
    · rw [cvp,cvm]; exact ht0.symm
  have unique2 : UniqueAt (graph n) (v (i-1)) (v (i-2)) c1 := by
    rw [←hmm]
    apply unique_v_vprev hn (i-1) c1
    · simp [c1,cb,hmm,hm2,cvmm]
    · simpa [c1,slide,cum,hmm,hm2,cvmm] using hr0
    · simp [c1,cui,hmp,hmm,hm2,cvmm]
    · simpa [c1,slide,cvm,hmp,hmm,hm2,cvmm] using ht0
  have adj1 : (graph n).Adj (v i) (v (i-1)) :=
    (adj_v hn i _).mpr (Or.inr (Or.inl rfl))
  have adj2 : (graph n).Adj (v (i-1)) (v (i-2)) := by
    apply (adj_v hn (i-1) _).mpr
    right; left; rw [hmm]
  refine ⟨d,.cons adj1 unique1 (.cons adj2 unique2 (.nil _)),?_,?_,?_,?_,rfl⟩
  · simp [d,c1,slide,ca]
  · simp [d,c1,slide,cb]
  · simp [d,c1,slide,cum]
  · simp [d,c1,slide,cvmm,hm2]

lemma unique_v_u {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (c : Vertex n → Colour)
    (hb : c b ≠ c (u i)) (hvm : c (v (i-1)) ≠ c (u i))
    (hup : c (u (i+1)) ≠ c (u i)) (hvp : c (v (i+1)) ≠ c (u i)) :
    UniqueAt (graph n) (v i) (u i) c := by
  intro x hx hc
  rcases (adj_v hn i x).mp hx with rfl | rfl | rfl | rfl | rfl
  · exact (hb hc).elim
  · exact (hvm hc).elim
  · rfl
  · exact (hup hc).elim
  · exact (hvp hc).elim

lemma unique_u_uprev {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (c : Vertex n → Colour)
    (ha : c a ≠ c (u (i-1))) (hup : c (u (i+1)) ≠ c (u (i-1)))
    (hvi : c (v i) ≠ c (u (i-1))) (hvm : c (v (i-1)) ≠ c (u (i-1))) :
    UniqueAt (graph n) (u i) (u (i-1)) c := by
  intro x hx hc
  rcases (adj_u hn i x).mp hx with rfl | rfl | rfl | rfl | rfl
  · exact (ha hc).elim
  · exact (hup hc).elim
  · exact (hvi hc).elim
  · exact (hvm hc).elim
  · rfl

lemma target_u {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (c : Vertex n → Colour) (x : Colour)
    (ha : c a ≠ x) (hup : c (u (i+1)) ≠ x) (hvi : c (v i) ≠ x)
    (hvm : c (v (i-1)) ≠ x) (hum : c (u (i-1)) ≠ x) : Target (u i) c := by
  refine ⟨x,?_⟩
  intro y hy
  rcases (adj_u hn i y).mp hy with rfl | rfl | rfl | rfl | rfl
  · exact ha
  · exact hup
  · exact hvi
  · exact hvm
  · exact hum

/-- The common first two actual slides of A_rho/B_tau, before branching. -/
lemma s_rho_tau_first_two {n : Nat} (hn : 5 ≤ n) (i : ZMod n)
    (c : Vertex n → Colour) (rho tau : Colour)
    (hc : ProperOff (graph n) (v i) c) (ca : c a=0) (cb : c b=1)
    (cvm : c (v (i-1))=rho) (cui : c (u i)=tau)
    (cup : c (u (i+1))=rho) (cvp : c (v (i+1))=0)
    (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (ht0 : tau ≠ 0)
    (ht1 : tau ≠ 1) (hrt : rho ≠ tau) :
    ∃ d, SlidePath 2 (v i,c) (u (i-1),d) ∧ d a=0 ∧ d b=1 ∧
      d (u i)=1 ∧ d (v (i-1))=rho ∧
      d (v (i-2))=c (v (i-2)) ∧ d (u (i-2))=c (u (i-2)) ∧
      d (v i)=tau ∧ c (u (i-1))=1 ∧
      d = slide (u i) (u (i-1)) (slide (v i) (u i) c) := by
  have hm1 := minus_ne hn i
  have hm2 : i-2 ≠ i := minus_offset_ne i 2 (by decide) (by omega)
  have hmp : (i-1)+1=i := by ring
  have cum : c (u (i-1))=1 := by
    apply tight_one rho tau _ hr0 hr1 ht0 ht1 hrt
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (i-1)).1 (by simp)
    · have adj : (graph n).Adj (u (i-1)) (v (i-1)) :=
        (adj_u hn (i-1) _).mpr (Or.inr (Or.inr (Or.inl rfl)))
      simpa [cvm] using hc adj (by simp) (by simpa using hm1)
    · have adj : (graph n).Adj (u (i-1)) (u i) := by
        apply (adj_u hn (i-1) _).mpr
        right; left; rw [hmp]
      simpa [cui] using hc adj (by simp) (by simp)
  let c1 := slide (v i) (u i) c
  let d := slide (u i) (u (i-1)) c1
  have unique1 : UniqueAt (graph n) (v i) (u i) c := by
    apply unique_v_u hn i c
    · rw [cb,cui]; exact ht1.symm
    · rw [cvm,cui]; exact hrt
    · rw [cup,cui]; exact hrt
    · rw [cvp,cui]; exact ht0.symm
  have unique2 : UniqueAt (graph n) (u i) (u (i-1)) c1 := by
    apply unique_u_uprev hn i c1
    · simp [c1,ca,cum]
    · simpa [c1,cup,cum] using hr1
    · simpa [c1,cui,cum] using ht1
    · simpa [c1,cvm,cum,slide,hm1] using hr1
  have adj1 : (graph n).Adj (v i) (u i) :=
    (adj_v hn i _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have adj2 : (graph n).Adj (u i) (u (i-1)) :=
    (adj_u hn i _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  refine ⟨d,.cons adj1 unique1 (.cons adj2 unique2 (.nil _)),?_,?_,?_,?_,?_,?_,?_,cum,rfl⟩
  · simp [d,c1,slide,ca]
  · simp [d,c1,slide,cb]
  · simp [d,c1,slide,cum]
  · simp [d,c1,slide,cvm,hm1]
  · simp [d,c1,slide,hm2]
  · simp [d,c1,slide,hm2]
  · simp [d,c1,slide,cui]

/-- A_rho outer-tau branch fills after its first two actual slides. -/
lemma a_rho_fill {n : Nat} (hn : 5 ≤ n) (i : ZMod n)
    (c : Vertex n → Colour) (rho tau : Colour)
    (hc : ProperOff (graph n) (v i) c) (ca : c a=0) (cb : c b=1)
    (cvm : c (v (i-1))=rho) (cui : c (u i)=tau)
    (cup : c (u (i+1))=rho) (cvp : c (v (i+1))=0)
    (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (ht0 : tau ≠ 0)
    (ht1 : tau ≠ 1) (hrt : rho ≠ tau)
    (cvmm : c (v (i-2))=0) (cumm : c (u (i-2))=rho) :
    ∃ d, SlidePath 2 (v i,c) (u (i-1),d) ∧ Target (u (i-1)) d := by
  obtain ⟨d,path,da,db,dui,dvm,dvmm,dumm,dvi,cum,deq⟩ :=
    s_rho_tau_first_two hn i c rho tau hc ca cb cvm cui cup cvp hr0 hr1 ht0 ht1 hrt
  have hmm : (i-1)-1=i-2 := by ring
  have hmp : (i-1)+1=i := by ring
  refine ⟨d,path,?_⟩
  apply target_u hn (i-1) d tau
  · rw [da]; exact ht0.symm
  · rw [hmp,dui]; exact ht1.symm
  · rw [dvm]; exact hrt
  · rw [hmm,dvmm,cvmm]; exact ht0.symm
  · rw [hmm,dumm,cumm]; exact hrt

/-- A_rho outer-tau branch returns through exactly four actual slides. -/
lemma a_rho_return {n : Nat} (hn : 5 ≤ n) (i : ZMod n)
    (c : Vertex n → Colour) (rho tau : Colour)
    (hc : ProperOff (graph n) (v i) c) (ca : c a=0) (cb : c b=1)
    (cvm : c (v (i-1))=rho) (cui : c (u i)=tau)
    (cup : c (u (i+1))=rho) (cvp : c (v (i+1))=0)
    (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (ht0 : tau ≠ 0)
    (ht1 : tau ≠ 1) (hrt : rho ≠ tau)
    (cvmm : c (v (i-2))=0) (cumm : c (u (i-2))=tau) :
    ∃ e, SlidePath 4 (v i,c) (v (i-2),e) ∧ e a=0 ∧ e b=1 ∧
      e (u (i-1))=rho ∧ e (v (i-1))=0 ∧
      e = slide (v (i-1)) (v (i-2))
        (slide (u (i-1)) (v (i-1)) (slide (u i) (u (i-1)) (slide (v i) (u i) c))) := by
  obtain ⟨d,path,da,db,dui,dvm,dvmm,dumm,dvi,cum,deq⟩ :=
    s_rho_tau_first_two hn i c rho tau hc ca cb cvm cui cup cvp hr0 hr1 ht0 ht1 hrt
  have hm1 := minus_ne hn i
  have hm2 : i-2 ≠ i := minus_offset_ne i 2 (by decide) (by omega)
  have hmm : (i-1)-1=i-2 := by ring
  have hmp : (i-1)+1=i := by ring
  let d1 := slide (u (i-1)) (v (i-1)) d
  let e := slide (v (i-1)) (v (i-2)) d1
  have unique3 : UniqueAt (graph n) (u (i-1)) (v (i-1)) d := by
    apply unique_u_v hn (i-1) d
    · rw [da,dvm]; exact hr0.symm
    · rw [hmp,dui,dvm]; exact hr1.symm
    · rw [hmm,dvmm,cvmm,dvm]; exact hr0.symm
    · rw [hmm,dumm,cumm,dvm]; exact hrt.symm
  have unique4 : UniqueAt (graph n) (v (i-1)) (v (i-2)) d1 := by
    rw [←hmm]
    apply unique_v_vprev hn (i-1) d1
    · simp [d1,db,hmm,dvmm,cvmm]
    · simpa [d1,slide,dvm,hmm,dvmm,cvmm] using hr0
    · simp [d1,hmp,dui,hmm,dvmm,cvmm,hm1.symm]
    · simpa [d1,slide,hmp,dvi,hmm,dvmm,cvmm] using ht0
  have adj3 : (graph n).Adj (u (i-1)) (v (i-1)) :=
    (adj_u hn (i-1) _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have adj4 : (graph n).Adj (v (i-1)) (v (i-2)) := by
    apply (adj_v hn (i-1) _).mpr
    right; left; rw [hmm]
  refine ⟨e,path.append (.cons adj3 unique3 (.cons adj4 unique4 (.nil _))),?_,?_,?_,?_,?_⟩
  · simp [e,d1,slide,da]
  · simp [e,d1,slide,db]
  · simp [e,d1,slide,dvm]
  · simp [e,d1,slide,dvmm,cvmm]
  · simp [e,d1,deq]

lemma unique_u_vprev {n : Nat} (hn : 5 ≤ n) (i : ZMod n) (c : Vertex n → Colour)
    (ha : c a ≠ c (v (i-1))) (hup : c (u (i+1)) ≠ c (v (i-1)))
    (hvi : c (v i) ≠ c (v (i-1))) (hum : c (u (i-1)) ≠ c (v (i-1))) :
    UniqueAt (graph n) (u i) (v (i-1)) c := by
  intro x hx hc
  rcases (adj_u hn i x).mp hx with rfl | rfl | rfl | rfl | rfl
  · exact (ha hc).elim
  · exact (hup hc).elim
  · exact (hvi hc).elim
  · rfl
  · exact (hum hc).elim

/-- Actual B_tau return, with its low upper colour and far zero forced. -/
lemma b_tau_return {n : Nat} (hn : 5 ≤ n) (i : ZMod n)
    (c : Vertex n → Colour) (rho tau : Colour)
    (hc : ProperOff (graph n) (v i) c) (ca : c a=0) (cb : c b=1)
    (cvm : c (v (i-1))=rho) (cui : c (u i)=tau)
    (cup : c (u (i+1))=rho) (cvp : c (v (i+1))=0)
    (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (ht0 : tau ≠ 0)
    (ht1 : tau ≠ 1) (hrt : rho ≠ tau) (cvmm : c (v (i-2))=tau) :
    ∃ e, SlidePath 4 (v i,c) (v (i-3),e) ∧ e a=0 ∧ e b=1 ∧
      e (u (i-2))=rho ∧ e (v (i-2))=0 ∧
      e = slide (v (i-2)) (v (i-3))
        (slide (u (i-1)) (v (i-2)) (slide (u i) (u (i-1)) (slide (v i) (u i) c))) := by
  obtain ⟨d,path,da,db,dui,dvm,dvmm,dumm,dvi,cum,deq⟩ :=
    s_rho_tau_first_two hn i c rho tau hc ca cb cvm cui cup cvp hr0 hr1 ht0 ht1 hrt
  have hm1 := minus_ne hn i
  have hm2 : i-2 ≠ i := minus_offset_ne i 2 (by decide) (by omega)
  have hm3 : i-3 ≠ i := minus_offset_ne i 3 (by decide) (by omega)
  have hmm : (i-1)-1=i-2 := by ring
  have hmp : (i-1)+1=i := by ring
  have hkp : (i-2)+1=i-1 := by ring
  have hkm : (i-2)-1=i-3 := by ring
  have hm21 : i-2 ≠ i-1 := by simpa [hmm] using minus_ne hn (i-1)
  have cumm : c (u (i-2))=rho := by
    apply tight_force rho tau _ hr0 hr1 ht0 ht1 hrt
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (i-2)).1 (by simp)
    · have adj : (graph n).Adj (u (i-2)) (u (i-1)) := by
        apply (adj_u hn (i-2) _).mpr
        right; left; rw [hkp]
      simpa [cum] using hc adj (by simp) (by simp)
    · have adj : (graph n).Adj (u (i-2)) (v (i-2)) :=
        (adj_u hn (i-2) _).mpr (Or.inr (Or.inr (Or.inl rfl)))
      simpa [cvmm] using hc adj (by simp) (by simpa using hm2)
  have cvmmm : c (v (i-3))=0 := by
    apply tight_zero rho tau _ hr0 hr1 ht0 ht1 hrt
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (i-3)).2 (by simpa using hm3)
    · have adj : (graph n).Adj (v (i-3)) (u (i-2)) := by
        apply Adj.symm
        apply (adj_u hn (i-2) _).mpr
        right; right; right; left; rw [hkm]
      simpa [cumm] using hc adj (by simpa using hm3) (by simp)
    · have adj : (graph n).Adj (v (i-3)) (v (i-2)) := by
        apply Adj.symm
        apply (adj_v hn (i-2) _).mpr
        right; left; rw [hkm]
      simpa [cvmm] using hc adj (by simpa using hm3) (by simpa using hm2)
  have dvmmm : d (v (i-3))=0 := by rw [deq]; simp [slide,hm3,cvmmm]
  let d1 := slide (u (i-1)) (v (i-2)) d
  let e := slide (v (i-2)) (v (i-3)) d1
  have unique3 : UniqueAt (graph n) (u (i-1)) (v (i-2)) d := by
    rw [←hmm]
    apply unique_u_vprev hn (i-1) d
    · rw [da,hmm,dvmm,cvmm]; exact ht0.symm
    · rw [hmp,dui,hmm,dvmm,cvmm]; exact ht1.symm
    · rw [dvm,hmm,dvmm,cvmm]; exact hrt
    · rw [hmm,dumm,cumm,dvmm,cvmm]; exact hrt
  have unique4 : UniqueAt (graph n) (v (i-2)) (v (i-3)) d1 := by
    rw [←hkm]
    apply unique_v_vprev hn (i-2) d1
    · simp [d1,db,hkm,dvmmm]
    · simpa [d1,slide,dumm,cumm,hkm,dvmmm,hm21] using hr0
    · simpa [d1,slide,hkp,dvmm,cvmm,hkm,dvmmm] using ht0
    · simpa [d1,hkp,dvm,hkm,dvmmm] using hr0
  have adj3 : (graph n).Adj (u (i-1)) (v (i-2)) := by
    apply (adj_u hn (i-1) _).mpr
    right; right; right; left; rw [hmm]
  have adj4 : (graph n).Adj (v (i-2)) (v (i-3)) := by
    apply (adj_v hn (i-2) _).mpr
    right; left; rw [hkm]
  refine ⟨e,path.append (.cons adj3 unique3 (.cons adj4 unique4 (.nil _))),?_,?_,?_,?_,?_⟩
  · simp [e,d1,slide,da]
  · simp [e,d1,slide,db]
  · simp [e,d1,slide,dumm,cumm,hm21]
  · simp [e,d1,slide,dvmmm]
  · simp [e,d1,deq]

/-- The immediate S0 branch fills by one actual slide. -/
lemma s_zero_fill {n : Nat} (hn : 5 ≤ n) (i : ZMod n)
    (c : Vertex n → Colour) (rho tau : Colour)
    (ca : c a=0) (cb : c b=1) (cvm : c (v (i-1))=0)
    (cui : c (u i)=tau) (cup : c (u (i+1))=rho) (cvp : c (v (i+1))=0)
    (cum : c (u (i-1))=rho) (hr1 : rho ≠ 1) (ht0 : tau ≠ 0)
    (ht1 : tau ≠ 1) (hrt : rho ≠ tau) :
    ∃ d, SlidePath 1 (v i,c) (u i,d) ∧ Target (u i) d := by
  let d := slide (v i) (u i) c
  have unique : UniqueAt (graph n) (v i) (u i) c := by
    apply unique_v_u hn i c
    · rw [cb,cui]; exact ht1.symm
    · rw [cvm,cui]; exact ht0.symm
    · rw [cup,cui]; exact hrt
    · rw [cvp,cui]; exact ht0.symm
  refine ⟨d,.cons ((adj_v hn i _).mpr (Or.inr (Or.inr (Or.inl rfl)))) unique (.nil _),?_⟩
  apply target_u hn i d 1
  · simp [d,ca]
  · simpa [d,cup] using hr1
  · simpa [d,cui] using ht1
  · simp [d,cvm,minus_ne hn i]
  · simpa [d,cum] using hr1

/-- The S0 three-slide return, with both new tight colours forced. -/
lemma s_zero_return {n : Nat} (hn : 5 ≤ n) (i : ZMod n)
    (c : Vertex n → Colour) (rho tau : Colour)
    (hc : ProperOff (graph n) (v i) c) (ca : c a=0) (cb : c b=1)
    (cvm : c (v (i-1))=0) (cui : c (u i)=tau)
    (cup : c (u (i+1))=rho) (cvp : c (v (i+1))=0) (cum : c (u (i-1))=1)
    (_hr0 : rho ≠ 0) (hr1 : rho ≠ 1) (ht0 : tau ≠ 0)
    (ht1 : tau ≠ 1) (hrt : rho ≠ tau) :
    ∃ d p q, SlidePath 3 (v i,c) (v (i-2),d) ∧ d a=0 ∧ d b=1 ∧
      d (v (i-3))=0 ∧ d (u (i-2))=q ∧ d (u (i-1))=p ∧ d (v (i-1))=0 ∧
      p ≠ 0 ∧ p ≠ 1 ∧ q ≠ 0 ∧ q ≠ 1 ∧ p ≠ q ∧
      d = slide (u (i-1)) (v (i-2)) (slide (u i) (u (i-1)) (slide (v i) (u i) c)) := by
  let p := c (v (i-2))
  let q := c (u (i-2))
  have hm1 := minus_ne hn i
  have hm2 : i-2 ≠ i := minus_offset_ne i 2 (by decide) (by omega)
  have hm3 : i-3 ≠ i := minus_offset_ne i 3 (by decide) (by omega)
  have h20 : (2 : ZMod n) ≠ 0 := by simpa using offset_ne (0 : ZMod n) 2 (by decide) (by omega)
  have hmm : (i-1)-1=i-2 := by ring
  have hmp : (i-1)+1=i := by ring
  have hkp : (i-2)+1=i-1 := by ring
  have hkm : (i-2)-1=i-3 := by ring
  have hm21 : i-2 ≠ i-1 := by simpa [hmm] using minus_ne hn (i-1)
  have hp1 : p ≠ 1 := (pole_exclusion hc (by simp) (by simp) ca cb (i-2)).2 (by simpa using hm2)
  have hp0 : p ≠ 0 := by
    have adj : (graph n).Adj (v (i-2)) (v (i-1)) := by
      apply Adj.symm
      apply (adj_v hn (i-1) _).mpr
      right; left; rw [hmm]
    simpa [p,cvm] using hc adj (by simpa using hm2) (by simpa using hm1)
  have hq0 : q ≠ 0 := (pole_exclusion hc (by simp) (by simp) ca cb (i-2)).1 (by simp)
  have hq1 : q ≠ 1 := by
    have adj : (graph n).Adj (u (i-2)) (u (i-1)) := by
      apply (adj_u hn (i-2) _).mpr
      right; left; rw [hkp]
    simpa [q,cum] using hc adj (by simp) (by simp)
  have hpq : p ≠ q := by
    exact hc ((adj_u hn (i-2) _).mpr (Or.inr (Or.inr (Or.inl rfl)))).symm
      (by simpa using hm2) (by simp)
  have cvmmm : c (v (i-3))=0 := by
    apply tight_zero p q _ hp0 hp1 hq0 hq1 hpq
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (i-3)).2 (by simpa using hm3)
    · have adj : (graph n).Adj (v (i-3)) (v (i-2)) := by
        apply Adj.symm
        apply (adj_v hn (i-2) _).mpr
        right; left; rw [hkm]
      exact hc adj (by simpa using hm3) (by simpa using hm2)
    · have adj : (graph n).Adj (v (i-3)) (u (i-2)) := by
        apply Adj.symm
        apply (adj_u hn (i-2) _).mpr
        right; right; right; left; rw [hkm]
      exact hc adj (by simpa using hm3) (by simp)
  let c1 := slide (v i) (u i) c
  let c2 := slide (u i) (u (i-1)) c1
  let d := slide (u (i-1)) (v (i-2)) c2
  have unique1 : UniqueAt (graph n) (v i) (u i) c := by
    apply unique_v_u hn i c
    · rw [cb,cui]; exact ht1.symm
    · rw [cvm,cui]; exact ht0.symm
    · rw [cup,cui]; exact hrt
    · rw [cvp,cui]; exact ht0.symm
  have unique2 : UniqueAt (graph n) (u i) (u (i-1)) c1 := by
    apply unique_u_uprev hn i c1
    · simp [c1,ca,cum]
    · simpa [c1,cup,cum] using hr1
    · simpa [c1,cui,cum] using ht1
    · simp [c1,cvm,cum,hm1]
  have unique3 : UniqueAt (graph n) (u (i-1)) (v (i-2)) c2 := by
    rw [←hmm]
    apply unique_u_vprev hn (i-1) c2
    · simpa [c2,c1,slide,ca,hmm,p,hm2,h20] using hp0.symm
    · simpa [c2,c1,slide,hmp,cum,hmm,p,hm2,h20] using hp1.symm
    · simpa [c2,c1,slide,cvm,hmm,p,hm1,h20] using hp0.symm
    · simpa [c2,c1,slide,hmm,p,q,hm2,hm21] using hpq.symm
  have adj1 : (graph n).Adj (v i) (u i) :=
    (adj_v hn i _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have adj2 : (graph n).Adj (u i) (u (i-1)) :=
    (adj_u hn i _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have adj3 : (graph n).Adj (u (i-1)) (v (i-2)) := by
    apply (adj_u hn (i-1) _).mpr
    right; right; right; left; rw [hmm]
  refine ⟨d,p,q,.cons adj1 unique1 (.cons adj2 unique2 (.cons adj3 unique3 (.nil _))),
    ?_,?_,?_,?_,?_,?_,hp0,hp1,hq0,hq1,hpq,rfl⟩
  · simp [d,c2,c1,slide,ca]
  · simp [d,c2,c1,slide,cb]
  · simp [d,c2,c1,slide,cvmmm,hm3]
  · simp [d,c2,c1,slide,q,hm21,hm2]
  · simp [d,c2,c1,slide,p,h20]
  · simp [d,c2,c1,slide,cvm,hm1]

end SimpleGraph.TwoPoleBelt
