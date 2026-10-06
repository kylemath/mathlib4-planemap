/-
Unequal-pole belt proof, based on Long Table's complete draft and Math's
internal Team A graph/move proofs. Reviewed and integrated by Math.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TwoPoleBelt
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyPotential
public import Mathlib.Tactic

@[expose] public section
namespace SimpleGraph.TwoPoleBeltWalk
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

variable {n : ℕ}

/-! ## §1 The graph `G_n` (reused from Team A) -/

/-- `G_n`: poles `a, b`, belt `u i, v i` (`i : ZMod n`), edges `a u_i`, `b v_i`,
`u_i u_{i+1}`, `v_i v_{i+1}`, `u_i v_i`, `u_i v_{i-1}`; no edge `a b`. -/
abbrev G (n : ℕ) : SimpleGraph (Vertex n) := TwoPoleBelt.graph n

/-- Neighbour list `N(u_i) = {a, u_{i+1}, v_i, v_{i-1}, u_{i-1}}` (Team A, proved). -/
theorem nbr_u (hn : 5 ≤ n) (i : ZMod n) (x : Vertex n) :
    (G n).Adj (u i) x ↔ x = a ∨ x = u (i+1) ∨ x = v i ∨ x = v (i-1) ∨ x = u (i-1) :=
  adj_u hn i x

/-- Neighbour list `N(v_i) = {b, v_{i-1}, u_i, u_{i+1}, v_{i+1}}` (Team A, proved). -/
theorem nbr_v (hn : 5 ≤ n) (i : ZMod n) (x : Vertex n) :
    (G n).Adj (v i) x ↔ x = b ∨ x = v (i-1) ∨ x = u i ∨ x = u (i+1) ∨ x = v (i+1) :=
  adj_v hn i x

theorem nbr_a (i : ZMod n) : (G n).Adj a (u i) := by simp [graph, TwoPoleBelt.edge]
theorem nbr_b (i : ZMod n) : (G n).Adj b (v i) := by simp [graph, TwoPoleBelt.edge]
theorem not_adj_ab : ¬ (G n).Adj a b := by simp [graph, TwoPoleBelt.edge]

/-- A belt vertex: neither pole. -/
def IsBelt (x : Vertex n) : Prop := x ≠ a ∧ x ≠ b

@[simp] theorem isBelt_u (i : ZMod n) : IsBelt (u i) := by simp [IsBelt]
@[simp] theorem isBelt_v (i : ZMod n) : IsBelt (v i) := by simp [IsBelt]

/-! ## §1 Automorphisms -/

/-- Rotation by `k`: `u_i ↦ u_{i+k}`, `v_i ↦ v_{i+k}`, poles fixed. -/
def rotFun (k : ZMod n) : Vertex n → Vertex n
  | a => a | b => b | u i => u (i+k) | v i => v (i+k)

/-- Ring swap `s`: `a ↔ b`, `u_i ↦ v_{-i}`, `v_i ↦ u_{-i}`. -/
def swapFun : Vertex n → Vertex n
  | a => b | b => a | u i => v (-i) | v i => u (-i)

/-- Reflection `R`: `u_i ↦ u_{-i}`, `v_i ↦ v_{-1-i}`, poles fixed. -/
def reflFun : Vertex n → Vertex n
  | a => a | b => b | u i => u (-i) | v i => v (-1-i)

theorem rotFun_rotFun (k l : ZMod n) (x : Vertex n) :
    rotFun l (rotFun k x) = rotFun (k+l) x := by
  cases x <;> simp [rotFun, add_assoc]

theorem swapFun_invol (x : Vertex n) : swapFun (swapFun x) = x := by
  cases x <;> simp [swapFun]

theorem reflFun_invol (x : Vertex n) : reflFun (reflFun x) = x := by
  cases x <;> simp [reflFun]

/-- The rotation as a permutation of vertices. -/
def rotEquiv (k : ZMod n) : Vertex n ≃ Vertex n where
  toFun := rotFun k
  invFun := rotFun (-k)
  left_inv x := by rw [rotFun_rotFun]; cases x <;> simp [rotFun]
  right_inv x := by rw [rotFun_rotFun]; cases x <;> simp [rotFun]

def swapEquiv : Vertex n ≃ Vertex n :=
  ⟨swapFun, swapFun, swapFun_invol, swapFun_invol⟩

def reflEquiv : Vertex n ≃ Vertex n :=
  ⟨reflFun, reflFun, reflFun_invol, reflFun_invol⟩

/-- Rotation preserves the raw edge relation. -/
theorem edge_rot (k : ZMod n) (x y : Vertex n) : TwoPoleBelt.edge (rotFun k x) (rotFun k y) ↔ TwoPoleBelt.edge x y := by
  cases x <;> cases y <;> simp only [rotFun, TwoPoleBelt.edge] <;>
    first
    | exact Iff.rfl
    | (constructor <;> rintro (h | h) <;>
        first
        | (left; linear_combination h)
        | (right; linear_combination h))

/-- The ring swap preserves the raw edge relation. -/
theorem edge_swap (x y : Vertex n) : TwoPoleBelt.edge (swapFun x) (swapFun y) ↔ TwoPoleBelt.edge x y := by
  cases x <;> cases y <;> simp only [swapFun, TwoPoleBelt.edge] <;>
    first
    | exact Iff.rfl
    | (constructor <;> rintro (h | h) <;>
        first
        | (left; linear_combination h)
        | (right; linear_combination h))

/-- The reflection preserves the raw edge relation. -/
theorem edge_refl (x y : Vertex n) : TwoPoleBelt.edge (reflFun x) (reflFun y) ↔ TwoPoleBelt.edge x y := by
  cases x <;> cases y <;> simp only [reflFun, TwoPoleBelt.edge] <;>
    first
    | exact Iff.rfl
    | (constructor <;> rintro (h | h) <;>
        first
        | (left; linear_combination h)
        | (right; linear_combination h)
        | (left; linear_combination -h)
        | (right; linear_combination -h))

/-- Rotation `r^k` is a graph automorphism of `G_n`. -/
def rot (k : ZMod n) : G n ≃g G n where
  toEquiv := rotEquiv k
  map_rel_iff' {x y} := by
    change (rotFun k x ≠ rotFun k y ∧ TwoPoleBelt.edge (rotFun k x) (rotFun k y)) ↔ (x ≠ y ∧ TwoPoleBelt.edge x y)
    have hne : rotFun k x ≠ rotFun k y ↔ x ≠ y := (rotEquiv k).injective.ne_iff
    rw [edge_rot, hne]

/-- The ring swap `s` is a graph automorphism of `G_n`. -/
def ringSwap : G n ≃g G n where
  toEquiv := swapEquiv
  map_rel_iff' {x y} := by
    change (swapFun x ≠ swapFun y ∧ TwoPoleBelt.edge (swapFun x) (swapFun y)) ↔ (x ≠ y ∧ TwoPoleBelt.edge x y)
    have hne : swapFun x ≠ swapFun y ↔ x ≠ y := (swapEquiv (n := n)).injective.ne_iff
    rw [edge_swap, hne]

/-- The reflection `R` is a graph automorphism of `G_n`. It fixes `u_0`,
swaps `u_1 ↔ u_{-1}` and `v_0 ↔ v_{-1}`. -/
def reflection : G n ≃g G n where
  toEquiv := reflEquiv
  map_rel_iff' {x y} := by
    change (reflFun x ≠ reflFun y ∧ TwoPoleBelt.edge (reflFun x) (reflFun y)) ↔ (x ≠ y ∧ TwoPoleBelt.edge x y)
    have hne : reflFun x ≠ reflFun y ↔ x ≠ y := (reflEquiv (n := n)).injective.ne_iff
    rw [edge_refl, hne]

@[simp] theorem reflection_u0 : (reflection : G n ≃g G n) (u 0) = u 0 := by
  change reflFun (u 0) = u 0; simp [reflFun]

/-! ## §1 Moves commute with automorphisms -/

/-- Transport of a partial colouring along a graph automorphism. -/
def transport (φ : G n ≃g G n) (c : Vertex n → Colour) : Vertex n → Colour :=
  fun x => c (φ.symm x)

theorem properOff_transport (φ : G n ≃g G n) {h : Vertex n} {c : Vertex n → Colour}
    (hc : ProperOff (G n) h c) : ProperOff (G n) (φ h) (transport φ c) := by
  intro x y hxy hx hy
  apply hc ((φ.symm.map_rel_iff').mpr hxy)
  · intro e; apply hx; rw [← e]; simp
  · intro e; apply hy; rw [← e]; simp

theorem target_transport (φ : G n ≃g G n) {h : Vertex n} {c : Vertex n → Colour}
    (ht : Target h c) : Target (φ h) (transport φ c) := by
  obtain ⟨x, hx⟩ := ht
  refine ⟨x, fun y hy => hx _ ?_⟩
  have := (φ.symm.map_rel_iff').mpr hy
  simpa using this

/-- Slides commute with automorphisms (proved). -/
theorem slidePath_transport (φ : G n ≃g G n) {k : ℕ} {s t : State n}
    (p : SlidePath k s t) :
    SlidePath k (φ s.1, transport φ s.2) (φ t.1, transport φ t.2) := by
  induction p with
  | nil s => exact .nil _
  | @cons k h x c t adj uniq _ ih =>
    have hs : transport φ (slide h x c) = slide (φ h) (φ x) (transport φ c) := by
      funext y
      by_cases hy : y = φ h
      · subst hy; simp [transport, slide]
      · have hy' : φ.symm y ≠ h := by
          intro e; apply hy; rw [← e]; simp
        simp [transport, slide, hy, hy']
    refine .cons ((φ.map_rel_iff').mpr adj) ?_ (by simpa [hs] using ih)
    intro y hy hc
    have hy' : (G n).Adj h (φ.symm y) := by
      have := (φ.symm.map_rel_iff').mpr hy
      simpa using this
    have := uniq hy' (by simpa [transport] using hc)
    rw [← this]; simp

/-! ## §1 Moves as a relation for `VacancyPotential.Path` -/

/-- One singleton slide `h → x`, as a relation on states (hole, colouring). -/
def SlideStep (s t : State n) : Prop :=
  ∃ x, (G n).Adj s.1 x ∧ UniqueAt (G n) s.1 x s.2 ∧ t = (x, slide s.1 x s.2)

/-- Team A's `SlidePath` is exactly `VacancyPotential.Path SlideStep`. -/
theorem path_of_slidePath {k : ℕ} {s t : State n} (p : SlidePath k s t) :
    VacancyPotential.Path SlideStep k s t := by
  induction p with
  | nil s => exact .nil s
  | cons adj uniq _ ih => exact .cons ⟨_, adj, uniq, rfl⟩ ih

theorem slidePath_of_path {k : ℕ} {s t : State n}
    (p : VacancyPotential.Path SlideStep k s t) : SlidePath k s t := by
  induction p with
  | nil s => exact .nil s
  | cons step _ ih =>
    obtain ⟨x, adj, uniq, rfl⟩ := step
    exact .cons adj uniq ih

theorem Path.proper {k : ℕ} {s t : State n} (p : VacancyPotential.Path SlideStep k s t)
    (hc : ProperOff (G n) s.1 s.2) : ProperOff (G n) t.1 t.2 :=
  (slidePath_of_path p).proper hc

/-! ## §1 Pole invariant -/

/-- Normalised unequal poles: `c(a) = 0`, `c(b) = 1`. -/
def UnequalPoles (c : Vertex n → Colour) : Prop := c a = 0 ∧ c b = 1

/-- Pole invariant (§1): with `c(a)=0`, `c(b)=1`, every coloured `u` lies in
`{1,2,3}` and every coloured `v` lies in `{0,2,3}`. -/
def PoleInvariant (h : Vertex n) (c : Vertex n → Colour) : Prop :=
  UnequalPoles c ∧ (∀ i, u i ≠ h → c (u i) ≠ 0) ∧ (∀ i, v i ≠ h → c (v i) ≠ 1)

/-- The pole invariant follows from properness and the pole colours (proved). -/
theorem poleInvariant_of_proper {h : Vertex n} {c : Vertex n → Colour}
    (hc : ProperOff (G n) h c) (hh : IsBelt h) (hp : UnequalPoles c) :
    PoleInvariant h c :=
  ⟨hp, fun i => (pole_exclusion hc hh.1 hh.2 hp.1 hp.2 i).1,
       fun i => (pole_exclusion hc hh.1 hh.2 hp.1 hp.2 i).2⟩

/-- A slide between belt vertices leaves the pole colours unchanged (proved). -/
theorem unequalPoles_slide {h x : Vertex n} {c : Vertex n → Colour} (hh : IsBelt h)
    (hp : UnequalPoles c) : UnequalPoles (slide h x c) := by
  obtain ⟨ha, hb⟩ := slide_poles (x := x) (c := c) hh.1 hh.2
  exact ⟨ha.trans hp.1, hb.trans hp.2⟩

/-- A filled state: the link of the hole misses a colour (Team A's `Target`). -/
abbrev Filled (s : State n) : Prop := Target s.1 s.2

end SimpleGraph.TwoPoleBeltWalk
