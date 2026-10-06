/-
Unequal-pole belt proof, based on Long Table's complete draft and Math's
internal Team A graph/move proofs. Reviewed and integrated by Math.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TwoPoleBeltTransport
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.BeltOpeningWords
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TwoPoleBeltCaps

@[expose] public section
namespace SimpleGraph.TwoPoleBeltWalk
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex VacancyPotential

variable {n : ℕ}

/-! ## Colour bookkeeping -/

/-- `ρ, τ` are the two non-pole colours `{2,3}` in some order. -/
def Pair (rho tau : Colour) : Prop :=
  rho ≠ 0 ∧ rho ≠ 1 ∧ tau ≠ 0 ∧ tau ≠ 1 ∧ rho ≠ tau

instance (rho tau : Colour) : Decidable (Pair rho tau) := by unfold Pair; infer_instance

theorem Pair.symm {rho tau : Colour} (h : Pair rho tau) : Pair tau rho :=
  ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2.symm⟩

/-! ## Adjacency and distinctness helpers (proved) -/

theorem adj_uu (hn : 5 ≤ n) (i : ZMod n) : (G n).Adj (u i) (u (i+1)) :=
  (adj_u hn i _).mpr (Or.inr (Or.inl rfl))
theorem adj_vv (hn : 5 ≤ n) (i : ZMod n) : (G n).Adj (v i) (v (i+1)) :=
  (adj_v hn i _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
theorem adj_uv (hn : 5 ≤ n) (i : ZMod n) : (G n).Adj (u i) (v i) :=
  (adj_u hn i _).mpr (Or.inr (Or.inr (Or.inl rfl)))
theorem adj_uv_prev (hn : 5 ≤ n) (i : ZMod n) : (G n).Adj (u i) (v (i-1)) :=
  (adj_u hn i _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem v_sub_ne (i : ZMod n) (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (v (i - k) : Vertex n) ≠ v i := by
  simpa using minus_offset_ne i k hk hkn

theorem u_sub_ne (i : ZMod n) (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (u (i - k) : Vertex n) ≠ u i := by
  simpa using minus_offset_ne i k hk hkn

theorem natCast_inj {j k : ℕ} (hj : j < n) (hk : k < n) (h : (j : ZMod n) = (k : ZMod n)) :
    j = k := TwoPoleBeltCaps.bounded_cast_injective hj hk h

theorem sub_ne_sub (i : ZMod n) {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    i - (a : ZMod n) ≠ i - (b : ZMod n) := by
  intro h
  exact hab (natCast_inj ha hb (by linear_combination -h))

/-- `Target` is invariant under a colour permutation (proved). -/
theorem target_recolour (π : Equiv.Perm Colour) {h : Vertex n} {c : Vertex n → Colour}
    (ht : Target h c) : Target h (π ∘ c) := by
  obtain ⟨x, hx⟩ := ht
  exact ⟨π x, fun y hy e => hx y hy (π.injective e)⟩

theorem properOff_recolour (π : Equiv.Perm Colour) {h : Vertex n} {c : Vertex n → Colour}
    (hc : ProperOff (G n) h c) : ProperOff (G n) h (π ∘ c) :=
  fun _ _ hxy hx hy e => hc hxy hx hy (π.injective e)

theorem transport_reflection_apply (c : Vertex n → Colour) (x : Vertex n) :
    transport reflection c x = c (reflFun x) := rfl

theorem transport_reflection_invol (c : Vertex n → Colour) :
    transport reflection (transport reflection c) = c := by
  funext x; simp [transport_reflection_apply, reflFun_invol]

theorem isBelt_reflection {x : Vertex n} (hx : IsBelt x) : IsBelt (reflection x) := by
  change IsBelt (reflFun x)
  cases x <;> simp_all [IsBelt, reflFun]

/-- §5, row exhaustiveness (finite, `decide`). At a Z-state with `x = c(v_{i-1}) ≠ 1`,
`y = c(u_i) ∉ {0, ρ}`, `x ≠ y`, the state is filled (τ missing) or is one of
`S_τ1`, `S_ρτ`, `S_0`. -/
theorem zrow_cases : ∀ rho tau x y : Colour, Pair rho tau → x ≠ 1 → y ≠ 0 → y ≠ rho →
    x ≠ y →
    (x ≠ tau ∧ y ≠ tau) ∨ (x = tau ∧ y = 1) ∨ (x = rho ∧ y = tau) ∨ (x = 0 ∧ y = tau) := by
  unfold Pair; decide

/-- §5 `S_ρτ` branching (finite, `decide`): `c(v_{i-2})` meets `b = 1`, `u_{i-1} = 1`
and `v_{i-1} = ρ`, so it is `0` or `τ`; when it is `0`, `c(u_{i-2}) ∈ {ρ, τ}`. -/
theorem rhotau_branch : ∀ rho tau x : Colour, Pair rho tau → x ≠ 1 → x ≠ rho →
    x = 0 ∨ x = tau := by
  unfold Pair; decide

theorem upper_branch : ∀ rho tau y : Colour, Pair rho tau → y ≠ 0 → y ≠ 1 →
    y = rho ∨ y = tau := by
  unfold Pair; decide

/-- §5 `S_0` landing colours (finite, `decide`): the two non-pole colours are a `Pair`. -/
theorem pair_of_ne : ∀ p q : Colour, p ≠ 0 → p ≠ 1 → q ≠ 0 → q ≠ 1 → p ≠ q → Pair p q := by
  unfold Pair; decide

/-! ## §5 Z-states and §6 D-states -/

/-- `Z(i)`: hole `v_i`, `c(v_{i+1}) = 0`, `c(u_{i+1}) = ρ ≠ 1`, poles `0, 1`. The link is
`(1, x, y, ρ, 0)` with `x = c(v_{i-1})`, `y = c(u_i)`. -/
structure ZState (i : ZMod n) (c : Vertex n → Colour) (rho tau : Colour) : Prop where
  proper : ProperOff (G n) (v i) c
  poles : UnequalPoles c
  pair : Pair rho tau
  vnext : c (v (i+1)) = 0
  unext : c (u (i+1)) = rho

/-- `D(i)`: hole `u_i`, link `(0, 1, ρ, τ, 1)` on `(a, u_{i+1}, v_i, v_{i-1}, u_{i-1})`. -/
structure DState (i : ZMod n) (c : Vertex n → Colour) (rho tau : Colour) : Prop where
  proper : ProperOff (G n) (u i) c
  poles : UnequalPoles c
  pair : Pair rho tau
  unext : c (u (i+1)) = 1
  uprev : c (u (i-1)) = 1
  vi : c (v i) = rho
  vprev : c (v (i-1)) = tau

/-! ## §5 Step rows, as `Path SlideStep` between explicit states -/

/-- Fill rows `S_ρ1`, `S_{0,1}` (and every Z-state with `τ ∉ {x, y}`): fill `v_i` with `τ`. -/
theorem row_fill {hn : 5 ≤ n} {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (z : ZState i c rho tau) (hx : c (v (i-1)) ≠ tau) (hy : c (u i) ≠ tau) :
    Filled (v i, c) := by
  obtain ⟨_, ⟨_, cb⟩, ⟨_, _, ht0, ht1, hrt⟩, hv, hu⟩ := z
  exact target_v hn i c tau (by rw [cb]; exact ht1.symm) hx hy (by rw [hu]; exact hrt)
    (by rw [hv]; exact ht0.symm)

/-- Row `S_τ1` (`A_τ`): link `(1, τ, 1, ρ, 0)`; two slides `v_i → v_{i-1} → v_{i-2}` to
`Z(i-2)` with the same `ρ`. Wrapper of Team A's `a_tau_return`. -/
theorem row_tau1 (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (z : ZState i c rho tau) (hx : c (v (i-1)) = tau) (hy : c (u i) = 1) :
    ∃ d, VacancyPotential.Path SlideStep 2 (v i, c) (v (i-2), d) ∧ ZState (i-2) d rho tau ∧
      d = slide (v (i-1)) (v (i-2)) (slide (v i) (v (i-1)) c) := by
  obtain ⟨hc, ⟨ca, cb⟩, hp, hv, hu⟩ := z
  obtain ⟨hr0, hr1, ht0, ht1, hrt⟩ := hp
  obtain ⟨d, p, da, db, du, dv, rfl⟩ :=
    a_tau_return hn i c rho tau hc ca cb hx hy hu hv hr0 hr1 ht0 ht1 hrt
  have e : i - 2 + 1 = i - 1 := by ring
  refine ⟨_, path_of_slidePath p, ⟨p.proper hc, ⟨da, db⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩, ?_, ?_⟩, rfl⟩
  · rw [e]; exact dv
  · rw [e]; exact du

/-- `S_ρτ` forced colour: `c(u_{i-1}) = 1` (`u_{i-1}` meets `a = 0`, `u_i = τ`, `v_{i-1} = ρ`). -/
theorem rhotau_forced_u (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (z : ZState i c rho tau) (hx : c (v (i-1)) = rho) (hy : c (u i) = tau) :
    c (u (i-1)) = 1 := by
  obtain ⟨hc, ⟨ca, cb⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩, hv, hu⟩ := z
  exact (s_rho_tau_first_two hn i c rho tau hc ca cb hx hy hu hv hr0 hr1 ht0 ht1 hrt).choose_spec.2.2.2.2.2.2.2.2.1

/-- `S_ρτ` branch A, filling sub-case `u_{i-2} = ρ`: filled after 2 slides at `u_{i-1}`.
Wrapper of Team A's `a_rho_fill`. -/
theorem row_rhotau_fill (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (z : ZState i c rho tau) (hx : c (v (i-1)) = rho) (hy : c (u i) = tau)
    (hv2 : c (v (i-2)) = 0) (hu2 : c (u (i-2)) = rho) :
    ∃ d, VacancyPotential.Path SlideStep 2 (v i, c) (u (i-1), d) ∧ Filled (u (i-1), d) ∧
      ProperOff (G n) (u (i-1)) d ∧ UnequalPoles d := by
  obtain ⟨hc, ⟨ca, cb⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩, hv, hu⟩ := z
  -- Team A's `a_rho_fill` exports only the path and the target; we re-read its
  -- target argument from `s_rho_tau_first_two` to keep the pole colours.
  obtain ⟨d, path, da, db, dui, dvm, dvmm, dumm, _, _, _⟩ :=
    s_rho_tau_first_two hn i c rho tau hc ca cb hx hy hu hv hr0 hr1 ht0 ht1 hrt
  have hmm : (i-1)-1 = i-2 := by ring
  have hmp : (i-1)+1 = i := by ring
  refine ⟨d, path_of_slidePath path, ?_, path.proper hc, ⟨da, db⟩⟩
  apply target_u hn (i-1) d tau
  · rw [da]; exact ht0.symm
  · rw [hmp, dui]; exact ht1.symm
  · rw [dvm]; exact hrt
  · rw [hmm, dvmm, hv2]; exact ht0.symm
  · rw [hmm, dumm, hu2]; exact hrt

/-- `S_ρτ` branch A (`A_ρ`, outer `τ`): 4 slides to `Z(i-2)`, same `ρ`.
Wrapper of Team A's `a_rho_return`. -/
theorem row_rhotau_A (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (z : ZState i c rho tau) (hx : c (v (i-1)) = rho) (hy : c (u i) = tau)
    (hv2 : c (v (i-2)) = 0) (hu2 : c (u (i-2)) = tau) :
    ∃ d, VacancyPotential.Path SlideStep 4 (v i, c) (v (i-2), d) ∧ ZState (i-2) d rho tau ∧
      d = slide (v (i-1)) (v (i-2))
        (slide (u (i-1)) (v (i-1)) (slide (u i) (u (i-1)) (slide (v i) (u i) c))) := by
  obtain ⟨hc, ⟨ca, cb⟩, hp, hv, hu⟩ := z
  obtain ⟨hr0, hr1, ht0, ht1, hrt⟩ := hp
  obtain ⟨d, p, da, db, du, dv, rfl⟩ :=
    a_rho_return hn i c rho tau hc ca cb hx hy hu hv hr0 hr1 ht0 ht1 hrt hv2 hu2
  have e : i - 2 + 1 = i - 1 := by ring
  refine ⟨_, path_of_slidePath p, ⟨p.proper hc, ⟨da, db⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩, ?_, ?_⟩, rfl⟩
  · rw [e]; exact dv
  · rw [e]; exact du

/-- `S_ρτ` branch B (`B_τ`): `c(v_{i-2}) = τ`; 4 slides to `Z(i-3)`, same `ρ`.
Wrapper of Team A's `b_tau_return`. -/
theorem row_rhotau_B (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (z : ZState i c rho tau) (hx : c (v (i-1)) = rho) (hy : c (u i) = tau)
    (hv2 : c (v (i-2)) = tau) :
    ∃ d, VacancyPotential.Path SlideStep 4 (v i, c) (v (i-3), d) ∧ ZState (i-3) d rho tau ∧
      d = slide (v (i-2)) (v (i-3))
        (slide (u (i-1)) (v (i-2)) (slide (u i) (u (i-1)) (slide (v i) (u i) c))) := by
  obtain ⟨hc, ⟨ca, cb⟩, hp, hv, hu⟩ := z
  obtain ⟨hr0, hr1, ht0, ht1, hrt⟩ := hp
  obtain ⟨d, p, da, db, du, dv, rfl⟩ :=
    b_tau_return hn i c rho tau hc ca cb hx hy hu hv hr0 hr1 ht0 ht1 hrt hv2
  have e : i - 3 + 1 = i - 2 := by ring
  refine ⟨_, path_of_slidePath p, ⟨p.proper hc, ⟨da, db⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩, ?_, ?_⟩, rfl⟩
  · rw [e]; exact dv
  · rw [e]; exact du

/-- Row `S_0` branching (forced): `u_{i-1}` meets `a = 0`, `u_i = τ`, `v_{i-1} = 0`,
so `c(u_{i-1}) ∈ {1, ρ}`. -/
theorem row_S0_branch (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (z : ZState i c rho tau) (hy : c (u i) = tau) :
    c (u (i-1)) = 1 ∨ c (u (i-1)) = rho := by
  obtain ⟨hc, ⟨ca, cb⟩, hp, _, _⟩ := z
  have h0 : c (u (i-1)) ≠ 0 := (pole_exclusion hc (by simp) (by simp) ca cb (i-1)).1 (by simp)
  have ht : c (u (i-1)) ≠ tau := by
    rw [← hy]; have a := adj_uu hn (i-1); rw [show i - 1 + 1 = i by ring] at a
    exact hc a (by simp) (by simp)
  have := upper_branch tau rho (c (u (i-1))) hp.symm h0
  unfold Pair at hp
  rcases (show c (u (i-1)) = 1 ∨ c (u (i-1)) ≠ 1 by tauto) with h | h
  · exact Or.inl h
  · rcases this h with h' | h'
    · exact (ht h').elim
    · exact Or.inr h'

/-- Row `S_0`, filling branch: link `(1, 0, τ, ρ, 0)` and `c(u_{i-1}) = ρ`. Slide
`v_i → u_i` [τ]; the new link `(0, ρ, τ, 0, ρ)` misses `1`. -/
theorem row_S0_fill (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (z : ZState i c rho tau) (hx : c (v (i-1)) = 0) (hy : c (u i) = tau)
    (hu : c (u (i-1)) = rho) :
    ∃ d, VacancyPotential.Path SlideStep 1 (v i, c) (u i, d) ∧ Filled (u i, d) ∧
      ProperOff (G n) (u i) d ∧ UnequalPoles d := by
  obtain ⟨hc, ⟨ca, cb⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩, hv, hup⟩ := z
  have uniq : UniqueAt (G n) (v i) (u i) c := by
    apply unique_v_u hn i c
    · rw [cb, hy]; exact ht1.symm
    · rw [hx, hy]; exact ht0.symm
    · rw [hup, hy]; exact hrt
    · rw [hv, hy]; exact ht0.symm
  have adj : (G n).Adj (v i) (u i) := (adj_uv hn i).symm
  have hm1 : i - 1 ≠ i := minus_ne hn i
  refine ⟨_, path_of_slidePath (.cons adj uniq (.nil _)), ?_, properOff_slide _ hc uniq,
    unequalPoles_slide (isBelt_v i) ⟨ca, cb⟩⟩
  apply target_u hn i _ 1
  · simp [slide, ca]
  · simpa [slide, hup] using hr1
  · simpa [slide, hy] using ht1
  · simp [slide, hx, hm1]
  · simpa [slide, hu] using hr1

/-- Row `S_0`, return branch: `c(u_{i-1}) = 1`. `u_i → u_{i-1}` [1], giving link
`(0, 1, 0, p, q)` with `{p, q} = {2, 3}`; `u_{i-1} → v_{i-2}` [p], and `c(v_{i-3}) = 0`
is forced. Lands in `Z(i-2)` of type `S_0` with `(ρ, τ) := (p, q)`; 3 slides in all. -/
theorem row_S0_return (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (z : ZState i c rho tau) (hx : c (v (i-1)) = 0) (hy : c (u i) = tau)
    (hu : c (u (i-1)) = 1) :
    ∃ d p q, VacancyPotential.Path SlideStep 3 (v i, c) (v (i-2), d) ∧ ZState (i-2) d p q ∧
      d (v (i-3)) = 0 ∧ d (u (i-2)) = q ∧
      d = slide (u (i-1)) (v (i-2)) (slide (u i) (u (i-1)) (slide (v i) (u i) c)) := by
  obtain ⟨hc, ⟨ca, cb⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩, hv, hup⟩ := z
  have n10 : i - 1 ≠ i := minus_ne hn i
  have n20 : i - 2 ≠ i := minus_offset_ne i 2 (by omega) (by omega)
  have n30 : i - 3 ≠ i := minus_offset_ne i 3 (by omega) (by omega)
  have n21 : i - 2 ≠ i - 1 := by
    simpa using sub_ne_sub i (a := 2) (b := 1) (by omega) (by omega) (by omega)
  have hv1 : (v (i-1) : Vertex n) ≠ v i := by simpa using n10
  have hv2 : (v (i-2) : Vertex n) ≠ v i := by simpa using n20
  have hv3 : (v (i-3) : Vertex n) ≠ v i := by simpa using n30
  -- forced colours `p = c(v_{i-2})`, `q = c(u_{i-2})`, `c(v_{i-3}) = 0`
  set p := c (v (i-2)) with hpdef
  set q := c (u (i-2)) with hqdef
  have e21 : i - 2 + 1 = i - 1 := by ring
  have e32 : i - 3 + 1 = i - 2 := by ring
  have hp1 : p ≠ 1 := (pole_exclusion hc (by simp) (by simp) ca cb (i-2)).2 hv2
  have hp0 : p ≠ 0 := by
    rw [← hx]; have a := adj_vv hn (i-2); rw [e21] at a; exact hc a hv2 hv1
  have hq0 : q ≠ 0 := (pole_exclusion hc (by simp) (by simp) ca cb (i-2)).1 (by simp)
  have hq1 : q ≠ 1 := by
    rw [← hu]; have a := adj_uu hn (i-2); rw [e21] at a; exact hc a (by simp) (by simp)
  have hpq : p ≠ q := fun e => hc (adj_uv hn (i-2)) (by simp) hv2 e.symm
  have hz : c (v (i-3)) = 0 := by
    apply tight_zero p q _ hp0 hp1 hq0 hq1 hpq
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (i-3)).2 hv3
    · have a := adj_vv hn (i-3); rw [e32] at a; exact hc a hv3 hv2
    · have a := adj_uv_prev hn (i-2)
      rw [show i - 2 - 1 = i - 3 by ring] at a
      exact fun e => hc a (by simp) hv3 e.symm
  -- the three slides
  let c1 := slide (v i) (u i) c
  let c2 := slide (u i) (u (i-1)) c1
  have uniq1 : UniqueAt (G n) (v i) (u i) c := by
    apply unique_v_u hn i c
    · rw [cb, hy]; exact ht1.symm
    · rw [hx, hy]; exact ht0.symm
    · rw [hup, hy]; exact hrt
    · rw [hv, hy]; exact ht0.symm
  have uniq2 : UniqueAt (G n) (u i) (u (i-1)) c1 := by
    apply unique_u_uprev hn i c1
    · simp [c1, ca, hu]
    · simpa [c1, slide, hup, hu] using hr1
    · simpa [c1, slide, hy, hu] using ht1
    · simp [c1, hx, hu, n10]
  have uniq3 : UniqueAt (G n) (u (i-1)) (v (i-2)) c2 := by
    have := unique_u_vprev hn (i-1) c2
    rw [show i - 1 - 1 = i - 2 by ring, show i - 1 + 1 = i by ring] at this
    apply this
    · simpa [c2, c1, slide, ca, n20] using hp0.symm
    · simpa [c2, c1, slide, n20, hu] using hp1.symm
    · simpa [c2, c1, slide, n10, n20, hx] using hp0.symm
    · simpa [c2, c1, slide, n20, n21] using hpq.symm
  have adj1 : (G n).Adj (v i) (u i) := (adj_uv hn i).symm
  have adj2 : (G n).Adj (u i) (u (i-1)) :=
    (adj_u hn i _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have adj3 : (G n).Adj (u (i-1)) (v (i-2)) := by
    have a := adj_uv_prev hn (i-1); rwa [show i - 1 - 1 = i - 2 by ring] at a
  have path : SlidePath 3 (v i, c) (v (i-2), slide (u (i-1)) (v (i-2)) c2) :=
    .cons adj1 uniq1 (.cons adj2 uniq2 (.cons adj3 uniq3 (.nil _)))
  refine ⟨_, p, q, path_of_slidePath path, ⟨path.proper hc, ⟨?_, ?_⟩, ⟨hp0, hp1, hq0, hq1, hpq⟩,
    ?_, ?_⟩, ?_, ?_, rfl⟩
  · simp [c2, c1, slide, ca]
  · simp [c2, c1, slide, cb]
  · rw [e21]; simp [c2, c1, slide, hx, n10]
  · rw [e21]; simp [c2, c1, slide, n20, hpdef]
  · simp [c2, c1, slide, hz, n30]
  · simp [c2, c1, slide, n20, n21, hqdef]

/-! ## §6 The doubled-1 recurrence D -/

/-- D, first slide `u_i → v_i` [ρ]; if `c(v_{i+1}) ≠ 0` the new hole is filled.
Wrapper of Team A's `doubled_one_first`. -/
theorem rowD_fill (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (d : DState i c rho tau) (hx : c (v (i+1)) ≠ 0) :
    ∃ e, VacancyPotential.Path SlideStep 1 (u i, c) (v i, e) ∧ Filled (v i, e) ∧ ProperOff (G n) (v i) e ∧
      UnequalPoles e := by
  obtain ⟨hc, ⟨ca, cb⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩, hup, hum, hvi, hvm⟩ := d
  obtain ⟨p, ht⟩ := doubled_one_first hn i c rho tau hc ca cb hup hum hvi hvm hr0 hr1 ht0 ht1 hrt
  refine ⟨_, path_of_slidePath p, ht.resolve_right hx, p.proper hc,
    unequalPoles_slide (isBelt_u i) ⟨ca, cb⟩⟩

/-- D return: `c(v_{i+1}) = 0`; 3 slides `u_i → v_i → v_{i+1} → u_{i+2}` to `D(i+2)`.
Wrapper of Team A's `doubled_one_return`. -/
theorem rowD_return (hn : 5 ≤ n) {i : ZMod n} {c : Vertex n → Colour} {rho tau : Colour}
    (d : DState i c rho tau) (hx : c (v (i+1)) = 0) :
    ∃ e p q, VacancyPotential.Path SlideStep 3 (u i, c) (u (i+2), e) ∧ DState (i+2) e q p ∧
      e = slide (v (i+1)) (u (i+2)) (slide (v i) (v (i+1)) (slide (u i) (v i) c)) := by
  obtain ⟨hc, ⟨ca, cb⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩, hup, hum, hvi, hvm⟩ := d
  obtain ⟨e, p, q, path, ea, eb, eu3, eu1, ev2, ev1, hp0, hp1, hq0, hq1, hpq, rfl⟩ :=
    doubled_one_return hn i c rho tau hc ca cb hup hum hvi hvm hr0 hr1 ht0 ht1 hrt hx
  have e3 : i + 2 + 1 = i + 3 := by ring
  have e1 : i + 2 - 1 = i + 1 := by ring
  refine ⟨_, p, q, path_of_slidePath path,
    ⟨path.proper hc, ⟨ea, eb⟩, ⟨hq0, hq1, hp0, hp1, hpq.symm⟩, ?_, ?_, ev2, ?_⟩, rfl⟩
  · rw [e3]; exact eu3
  · rw [e1]; exact eu1
  · rw [e1]; exact ev1

/-! ## §7 Linear interval, potential -/

/-- `I_j` for the Z-walk: `v_0..v_{j-1}` and `u_1..u_j` carry their input colours. -/
def ZInterval (c0 c : Vertex n → Colour) (j : ℕ) : Prop :=
  ∀ k : ℕ, k < j → c (v (k : ZMod n)) = c0 (v (k : ZMod n)) ∧
    c (u ((k+1 : ℕ) : ZMod n)) = c0 (u ((k+1 : ℕ) : ZMod n))

/-- `I_i` for the D-walk: `v_i..v_{n-1}` and `u_{i+1}..u_{n-1}` carry their input colours. -/
def DInterval (c0 c : Vertex n → Colour) (i : ℕ) : Prop :=
  ∀ k : ℕ, i ≤ k → k < n → c (v (k : ZMod n)) = c0 (v (k : ZMod n)) ∧
    (i < k → c (u (k : ZMod n)) = c0 (u (k : ZMod n)))

/-- `Φ = |I|`: `2j` at a Z-state `v_j`, `2(n-i)-1` at a D-state `u_i`. -/
def potential (s : State n) : ℕ :=
  match s.1 with
  | v j => 2 * j.val
  | u i => 2 * (n - i.val) - 1
  | _ => 0

theorem potential_v {j : ℕ} (hj : j < n) (c : Vertex n → Colour) :
    potential (v (j : ZMod n), c) = 2 * j := by
  simp [potential, ZMod.val_natCast_of_lt hj]

theorem potential_u {i : ℕ} (hi : i < n) (c : Vertex n → Colour) :
    potential (u (i : ZMod n), c) = 2 * (n - i) - 1 := by
  simp [potential, ZMod.val_natCast_of_lt hi]

/-- A slide whose old hole lies outside `I_{j'}` preserves `I_{j'}` (proved). -/
theorem zInterval_slide {c0 c : Vertex n → Colour} {j j' : ℕ} (hI : ZInterval c0 c j)
    (hj : j' ≤ j) {h x : Vertex n}
    (hh : ∀ k : ℕ, k < j' → h ≠ v (k : ZMod n) ∧ h ≠ u ((k+1 : ℕ) : ZMod n)) :
    ZInterval c0 (slide h x c) j' := by
  intro k hk
  obtain ⟨h1, h2⟩ := hh k hk
  obtain ⟨e1, e2⟩ := hI k (by omega)
  exact ⟨by rw [slide_away _ _ _ (Ne.symm h1), e1], by rw [slide_away _ _ _ (Ne.symm h2), e2]⟩

theorem dInterval_slide {c0 c : Vertex n → Colour} {i i' : ℕ} (hI : DInterval c0 c i)
    (hi : i ≤ i') {h x : Vertex n}
    (hh : ∀ k : ℕ, i' ≤ k → k < n → h ≠ v (k : ZMod n) ∧ (i' < k → h ≠ u (k : ZMod n))) :
    DInterval c0 (slide h x c) i' := by
  intro k hk hkn
  obtain ⟨h1, h2⟩ := hh k hk hkn
  obtain ⟨e1, e2⟩ := hI k (by omega) hkn
  exact ⟨by rw [slide_away _ _ _ (Ne.symm h1), e1],
    fun hlt => by rw [slide_away _ _ _ (Ne.symm (h2 hlt)), e2 (by omega)]⟩

/-! ## §7 Good states, one predicate per family -/

/-- S-family (after O1, O3a): family colour `ρ` with `c⁰(u_1) = 1`, `c⁰(v_0) = ρ`;
the walk never meets an `S_0` row (`x = 0 → y = 1`). -/
def GoodS (c0 : Vertex n → Colour) (rho tau : Colour) (s : State n) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 2 ∧ s.1 = v (j : ZMod n) ∧ ZState (j : ZMod n) s.2 rho tau ∧
    ZInterval c0 s.2 j ∧ c0 (u 1) = 1 ∧ c0 (v 0) = rho ∧
    (s.2 (v ((j : ZMod n) - 1)) = 0 → s.2 (u (j : ZMod n)) = 1)

/-- S0-family (after O3b): every state is an `S_0` row `(1, 0, τ, ρ, 0)`;
`c⁰(v_0), c⁰(u_1)` are the two non-pole colours. -/
def GoodS0 (c0 : Vertex n → Colour) (s : State n) : Prop :=
  ∃ j : ℕ, ∃ rho tau : Colour, 2 ≤ j ∧ j ≤ n - 2 ∧ s.1 = v (j : ZMod n) ∧
    ZState (j : ZMod n) s.2 rho tau ∧ ZInterval c0 s.2 j ∧ Pair (c0 (v 0)) (c0 (u 1)) ∧
    s.2 (v ((j : ZMod n) - 1)) = 0 ∧ s.2 (u (j : ZMod n)) = tau

/-- D-family (after O2): `c⁰(u_{n-1}) = 1`, `c⁰(v_{n-1}) ≠ 0`. -/
def GoodD (c0 : Vertex n → Colour) (s : State n) : Prop :=
  ∃ i : ℕ, ∃ rho tau : Colour, i ≤ n - 2 ∧ s.1 = u (i : ZMod n) ∧
    DState (i : ZMod n) s.2 rho tau ∧ DInterval c0 s.2 i ∧
    c0 (u ((n-1 : ℕ) : ZMod n)) = 1 ∧ c0 (v ((n-1 : ℕ) : ZMod n)) ≠ 0

/-- The target: a proper, filled belt hole with the poles still `0, 1`. -/
def Done (s : State n) : Prop :=
  Filled s ∧ ProperOff (G n) s.1 s.2 ∧ IsBelt s.1 ∧ UnequalPoles s.2

/-- The controller shape required by `VacancyPotential.budget` (slack 0). -/
def Controls (good : State n → Prop) : Prop :=
  ∀ s, good s →
    (∃ k t, VacancyPotential.Path SlideStep k s t ∧ Done t ∧ k ≤ potential s + 0) ∨
    (∃ k t, VacancyPotential.Path SlideStep k s t ∧ good t ∧ potential t < potential s ∧
      k + potential t ≤ potential s)

/-! ## Reading a good state at a named index (proved) -/

theorem cast_sub_nat {m k : ℕ} (h : k ≤ m) : ((m - k : ℕ) : ZMod n) = (m : ZMod n) - k := by
  rw [Nat.cast_sub h]

theorem cast_n_sub (k : ℕ) (h : k ≤ n) : ((n - k : ℕ) : ZMod n) = -(k : ZMod n) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, zero_sub]

theorem GoodS.at {c0 : Vertex n → Colour} {rho tau : Colour} {s : State n} {j : ℕ}
    (hs : GoodS c0 rho tau s) (hj : s.1 = v (j : ZMod n)) (hjn : j ≤ n - 2) (hn : 5 ≤ n) :
    1 ≤ j ∧ ZState (j : ZMod n) s.2 rho tau ∧ ZInterval c0 s.2 j ∧ c0 (u 1) = 1 ∧
      c0 (v 0) = rho ∧ (s.2 (v ((j : ZMod n) - 1)) = 0 → s.2 (u (j : ZMod n)) = 1) := by
  obtain ⟨j', h1, h2, hh, rest⟩ := hs
  rw [hh] at hj
  have := natCast_inj (by omega) (by omega) (Vertex.v.inj hj)
  subst this
  exact ⟨h1, rest⟩

theorem GoodS0.at {c0 : Vertex n → Colour} {s : State n} {j : ℕ}
    (hs : GoodS0 c0 s) (hj : s.1 = v (j : ZMod n)) (hjn : j ≤ n - 2) (hn : 5 ≤ n) :
    ∃ rho tau, 2 ≤ j ∧ ZState (j : ZMod n) s.2 rho tau ∧ ZInterval c0 s.2 j ∧
      Pair (c0 (v 0)) (c0 (u 1)) ∧ s.2 (v ((j : ZMod n) - 1)) = 0 ∧ s.2 (u (j : ZMod n)) = tau := by
  obtain ⟨j', rho, tau, h1, h2, hh, rest⟩ := hs
  rw [hh] at hj
  have := natCast_inj (by omega) (by omega) (Vertex.v.inj hj)
  subst this
  exact ⟨rho, tau, h1, rest⟩

theorem GoodD.at {c0 : Vertex n → Colour} {s : State n} {i : ℕ}
    (hs : GoodD c0 s) (hi : s.1 = u (i : ZMod n)) (hin : i ≤ n - 2) (hn : 5 ≤ n) :
    ∃ rho tau, DState (i : ZMod n) s.2 rho tau ∧ DInterval c0 s.2 i ∧
      c0 (u ((n-1 : ℕ) : ZMod n)) = 1 ∧ c0 (v ((n-1 : ℕ) : ZMod n)) ≠ 0 := by
  obtain ⟨i', rho, tau, h1, hh, rest⟩ := hs
  rw [hh] at hi
  have := natCast_inj (by omega) (by omega) (Vertex.u.inj hi)
  subst this
  exact ⟨rho, tau, rest⟩

theorem v_ne_nat {j k : ℕ} (hj : j < n) (hk : k < n) (h : j ≠ k) :
    (v (j : ZMod n) : Vertex n) ≠ v (k : ZMod n) :=
  fun e => h (natCast_inj hj hk (Vertex.v.inj e))

theorem u_ne_nat {j k : ℕ} (hj : j < n) (hk : k < n) (h : j ≠ k) :
    (u (j : ZMod n) : Vertex n) ≠ u (k : ZMod n) :=
  fun e => h (natCast_inj hj hk (Vertex.u.inj e))

/-- The two input entries at the bottom of `I_j` (proved). -/
theorem ZInterval.bottom {c0 c : Vertex n → Colour} {j : ℕ} (hI : ZInterval c0 c j)
    (hj : 1 ≤ j) : c (v 0) = c0 (v 0) ∧ c (u 1) = c0 (u 1) := by
  simpa using hI 0 hj

/-! ## §7 Caps -/

/-- **Cap S, short cap.** At `j = 1` the link is `(1, ρ, 1, ρ, 0)`: filled (proved). -/
theorem capS_short (hn : 5 ≤ n) {c0 : Vertex n → Colour} {rho tau : Colour} {s : State n}
    (hs : GoodS c0 rho tau s) (hj : s.1 = v 1) : Filled s := by
  obtain ⟨h, c⟩ := s
  obtain ⟨j, hj1, hjn, hh, z, hI, h01, h0r, _⟩ := hs
  simp only at hh hj z hI
  subst hh
  have e : j = 1 := by
    have := TwoPoleBeltCaps.bounded_cast_injective (n := n) (a := j) (b := 1) (by omega) (by omega)
      (by simpa using Vertex.v.inj hj)
    exact this
  subst e
  obtain ⟨hv0, hu1⟩ := hI 0 (by omega)
  simp only [Nat.cast_zero, zero_add, Nat.cast_one] at hv0 hu1
  have ht := z.pair
  apply row_fill (hn := hn) z
  · simp only [Nat.cast_one, sub_self]; rw [hv0, h0r]; exact ht.2.2.2.2
  · simp only [Nat.cast_one]; rw [hu1, h01]; exact ht.2.2.2.1.symm

/-- **Cap S, landings stay in range.** In the S-family, a row from `j ≤ 3` never lands
at or below `v_0`: `S_τ1` and A need `j ≥ 3`, B needs `j ≥ 4`. The witnesses are
`c⁰(v_0) = ρ` and `c⁰(u_1) = 1`, current by the interval invariant. -/
theorem capS_tau1 (hn : 5 ≤ n) {c0 : Vertex n → Colour} {rho tau : Colour} {s : State n}
    {j : ℕ} (hs : GoodS c0 rho tau s) (hj : s.1 = v (j : ZMod n)) (hjn : j ≤ n - 2)
    (hx : s.2 (v ((j : ZMod n) - 1)) = tau) (hy : s.2 (u (j : ZMod n)) = 1) : 3 ≤ j := by
  obtain ⟨hj1, z, hI, h01, h0r, _⟩ := hs.at hj hjn hn
  obtain ⟨hv0, hu1⟩ := hI.bottom hj1
  have hc := z.proper
  have hp := z.pair
  by_contra hlt
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · simp only [Nat.cast_one, sub_self] at hx
    exact hp.2.2.2.2 (h0r.symm.trans (hv0.symm.trans hx))
  · have a := adj_uu hn 1
    rw [one_add_one_eq_two] at a
    simp only [Nat.cast_ofNat] at hy hc
    exact hc a (by simp) (by simp) (hu1.trans (h01.trans hy.symm))

theorem capS_A (hn : 5 ≤ n) {c0 : Vertex n → Colour} {rho tau : Colour} {s : State n}
    {j : ℕ} (hs : GoodS c0 rho tau s) (hj : s.1 = v (j : ZMod n)) (hjn : j ≤ n - 2)
    (hx : s.2 (v ((j : ZMod n) - 1)) = rho) (hy : s.2 (u (j : ZMod n)) = tau)
    (hv2 : s.2 (v ((j : ZMod n) - 2)) = 0) : 3 ≤ j := by
  obtain ⟨hj1, z, hI, h01, h0r, _⟩ := hs.at hj hjn hn
  obtain ⟨hv0, hu1⟩ := hI.bottom hj1
  have hp := z.pair
  by_contra hlt
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · simp only [Nat.cast_one] at hy
    exact hp.2.2.2.1 (hy.symm.trans (hu1.trans h01))
  · simp only [Nat.cast_ofNat, sub_self] at hv2
    exact hp.1 (h0r.symm.trans (hv0.symm.trans hv2))

theorem capS_B (hn : 5 ≤ n) {c0 : Vertex n → Colour} {rho tau : Colour} {s : State n}
    {j : ℕ} (hs : GoodS c0 rho tau s) (hj : s.1 = v (j : ZMod n)) (hjn : j ≤ n - 2)
    (hx : s.2 (v ((j : ZMod n) - 1)) = rho) (hy : s.2 (u (j : ZMod n)) = tau)
    (hv2 : s.2 (v ((j : ZMod n) - 2)) = tau) : 4 ≤ j := by
  obtain ⟨hj1, z, hI, h01, h0r, _⟩ := hs.at hj hjn hn
  obtain ⟨hv0, hu1⟩ := hI.bottom hj1
  have hp := z.pair
  have hc := z.proper
  have hf := rhotau_forced_u hn z hx hy
  by_contra hlt
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl
  · simp only [Nat.cast_one] at hy
    exact hp.2.2.2.1 (hy.symm.trans (hu1.trans h01))
  · simp only [Nat.cast_ofNat, sub_self] at hv2
    exact hp.2.2.2.2 (h0r.symm.trans (hv0.symm.trans hv2))
  · -- B forces `u_{j-1} = 1`, i.e. `u_2 = 1`, next to `u_1 = 1`
    have e : ((3 : ℕ) : ZMod n) - 1 = 2 := by norm_num
    rw [e] at hf
    have a := adj_uu hn 1
    rw [one_add_one_eq_two] at a
    exact hc a (by simp) (by simp) (hu1.trans (h01.trans hf.symm))

/-- **Cap S, long cap** (`c⁰(v_1) = τ`): a landing at `v_2` would put `ρ` on `u_3` next to
`u_2 = ρ` (forced by `a = 0`, `u_1 = 1`, `v_1 = τ`). Not needed by the budget proof below,
which only needs landings to stay at `j ≥ 1`; kept as the §7 statement. The final step is
Math's `TwoPoleBeltCaps.z_long_cap_impossible` (proved). -/
theorem capS_long (hn : 5 ≤ n) {c0 : Vertex n → Colour} {rho tau : Colour} {s : State n}
    (hs : GoodS c0 rho tau s) (hj : s.1 = v 2) (hv1 : c0 (v 1) = tau) : False := by
  obtain ⟨h, c⟩ := s
  obtain ⟨_, z, hI, h01, _, _⟩ := GoodS.at (j := 2) hs (by simpa using hj) (by omega) hn
  simp only at hj z hI
  subst hj
  have z' : ZState (2 : ZMod n) c rho tau := by simpa using z
  obtain ⟨-, hu1⟩ := hI.bottom (by omega)
  obtain ⟨hv1', hu2'⟩ := hI 1 (by omega)
  simp only [Nat.cast_one, Nat.reduceAdd, Nat.cast_ofNat] at hv1' hu2'
  have hc := z'.proper
  obtain ⟨ca, cb⟩ := z'.poles
  obtain ⟨hr0, hr1, ht0, ht1, hrt⟩ := z'.pair
  have h3 : c (u 3) = rho := by
    have := z'.unext; rwa [show (2 : ZMod n) + 1 = 3 by norm_num] at this
  have h2 : c (u 2) = rho := by
    apply tight_force rho tau _ hr0 hr1 ht0 ht1 hrt
    · exact (pole_exclusion hc (by simp) (by simp) ca cb 2).1 (by simp)
    · have a := adj_uu hn 1; rw [one_add_one_eq_two] at a
      rw [← h01, ← hu1]; exact fun e => hc a (by simp) (by simp) e.symm
    · have a := adj_uv_prev hn 2; rw [show (2 : ZMod n) - 1 = 1 by norm_num] at a
      have hne : (v 1 : Vertex n) ≠ v 2 := by
        intro e; have := natCast_inj (n := n) (j := 1) (k := 2) (by omega) (by omega)
          (by simpa using Vertex.v.inj e); omega
      rw [← hv1, ← hv1']; exact hc a (by simp) hne
  exact TwoPoleBeltCaps.z_long_cap_impossible hn c hc rho h2 h3

/-- **Cap S0.** `S_0(2)` fills at its first slide (`c⁰(u_1) = ρ_2`), and an `S_0` state at
`j = 3` would need `v_2 = 0` next to `v_1 = 0`; so S0-landings from `j ≥ 4` stay at `j ≥ 2`
and `j = 2, 3` give no return. -/
theorem capS0_two (hn : 5 ≤ n) {c0 : Vertex n → Colour} {s : State n} (hs : GoodS0 c0 s)
    (hj : s.1 = v 2) :
    ∃ t, VacancyPotential.Path SlideStep 1 s t ∧ Done t := by
  obtain ⟨h, c⟩ := s
  obtain ⟨rho, tau, _, z, hI, hp0, hx, hy⟩ := GoodS0.at (j := 2) hs (by simpa using hj) (by omega) hn
  simp only at hj z hx hy hI
  subst hj
  obtain ⟨-, hu1⟩ := hI.bottom (by omega)
  have e : ((2 : ℕ) : ZMod n) - 1 = 1 := by norm_num
  rw [e] at hx
  have z' : ZState (2 : ZMod n) c rho tau := by simpa using z
  have hy' : c (u 2) = tau := by simpa using hy
  rcases row_S0_branch hn z' hy' with h1 | hr
  · rw [show (2 : ZMod n) - 1 = 1 by norm_num, hu1] at h1
    exact (hp0.2.2.2.1 h1).elim
  · obtain ⟨d, p, hf, hpr, hpo⟩ := row_S0_fill hn z' (by rw [show (2 : ZMod n) - 1 = 1 by norm_num]; exact hx) hy' hr
    exact ⟨_, p, hf, hpr, isBelt_u _, hpo⟩

theorem capS0_three (hn : 5 ≤ n) {c0 : Vertex n → Colour} {s : State n} (hs : GoodS0 c0 s)
    (hj : s.1 = v 3) : False := by
  obtain ⟨rho, tau, _, z, hI, hp0, hx, _⟩ := hs.at (j := 3) (by simpa using hj) (by omega) hn
  obtain ⟨hv0, hu1⟩ := hI.bottom (by omega)
  obtain ⟨hv1, -⟩ := hI 1 (by omega)
  have hc := z.proper
  obtain ⟨ca, cb⟩ := z.poles
  simp only [Nat.cast_one] at hv1
  have e : ((3 : ℕ) : ZMod n) - 1 = 2 := by norm_num
  rw [e] at hx
  -- `v_1` meets `b = 1`, `v_0 = σ`, `u_1 = σ'`, so it is 0, next to `v_2 = 0`
  have hne3 : ∀ k : ℕ, 0 < k → k < 3 → (v (k : ZMod n) : Vertex n) ≠ v ((3 : ℕ) : ZMod n) := by
    intro k hk hk3 e; have := natCast_inj (by omega) (by omega) (Vertex.v.inj e); omega
  have hv1ne : (v 1 : Vertex n) ≠ v ((3 : ℕ) : ZMod n) := by simpa using hne3 1 (by omega) (by omega)
  have hv2ne : (v 2 : Vertex n) ≠ v ((3 : ℕ) : ZMod n) := by simpa using hne3 2 (by omega) (by omega)
  have hv0ne : (v 0 : Vertex n) ≠ v ((3 : ℕ) : ZMod n) := by
    intro e; have := natCast_inj (n := n) (j := 0) (k := 3) (by omega) (by omega)
      (by simpa using Vertex.v.inj e); omega
  have n1 : s.2 (v 1) ≠ 1 := (pole_exclusion hc (by simp) (by simp) ca cb 1).2 hv1ne
  have n2 : s.2 (v 1) ≠ s.2 (v 0) := by
    have a := adj_vv hn 0; rw [zero_add] at a; exact hc a.symm hv1ne hv0ne
  have n3 : s.2 (v 1) ≠ s.2 (u 1) := by
    exact fun e => hc (adj_uv hn 1) (by simp) hv1ne e.symm
  rw [hv0] at n2; rw [hu1] at n3
  have hz : s.2 (v 1) = 0 := by
    revert n1 n2 n3 hp0; generalize s.2 (v 1) = x; generalize c0 (v 0) = p;
    generalize c0 (u 1) = q; unfold Pair; decide +revert
  have a := adj_vv hn 1; rw [one_add_one_eq_two] at a
  exact hc a hv1ne hv2ne (hz.trans hx.symm)

/-- **Cap D.** `D(n-3)` is impossible (Math's `TwoPoleBeltCaps.d_prelast_impossible`), and at
`D(n-2)` the first slide fills because `c(v_{n-1}) = c⁰(v_{n-1}) ≠ 0`. -/
theorem capD_prelast (hn : 5 ≤ n) {c0 : Vertex n → Colour} {s : State n} (hs : GoodD c0 s)
    (hj : s.1 = u ((n-3 : ℕ) : ZMod n)) : False := by
  obtain ⟨rho, tau, d, hI, hcu, _⟩ := hs.at hj (by omega) hn
  have e : ((n-3 : ℕ) : ZMod n) + 1 = ((n-2 : ℕ) : ZMod n) := by
    rw [cast_n_sub 3 (by omega), cast_n_sub 2 (by omega)]; push_cast; ring
  have hl : s.2 (u ((n-2 : ℕ) : ZMod n)) = 1 := by rw [← e]; exact d.unext
  have hr : s.2 (u ((n-1 : ℕ) : ZMod n)) = 1 := by
    rw [((hI (n-1) (by omega) (by omega)).2 (by omega)), hcu]
  exact TwoPoleBeltCaps.d_prelast_impossible hn s.2 d.proper hl hr

theorem capD_last (hn : 5 ≤ n) {c0 : Vertex n → Colour} {s : State n} {i : ℕ}
    (hs : GoodD c0 s) (hi : s.1 = u (i : ZMod n)) (hin : i = n - 2) :
    s.2 (v ((i : ZMod n) + 1)) ≠ 0 := by
  obtain ⟨rho, tau, d, hI, _, hcv⟩ := hs.at hi (by omega) hn
  have e : (i : ZMod n) + 1 = ((n-1 : ℕ) : ZMod n) := by
    rw [hin, cast_n_sub 2 (by omega), cast_n_sub 1 (by omega)]; push_cast; ring
  rw [e, (hI (n-1) (by omega) (by omega)).1]
  exact hcv

/-! ## §7 Macro steps: one row + interval invariant + Φ drop + cap -/

/-- `S_τ1` as a macro step: lands in `GoodS` at `j-2`, 2 slides, `Φ` drops by 4. -/
theorem macroS_tau1 (hn : 5 ≤ n) {c0 : Vertex n → Colour} {rho tau : Colour} {s : State n}
    {j : ℕ} (hs : GoodS c0 rho tau s) (hj : s.1 = v (j : ZMod n)) (hjn : j ≤ n - 2)
    (hx : s.2 (v ((j : ZMod n) - 1)) = tau) (hy : s.2 (u (j : ZMod n)) = 1) :
    ∃ t, VacancyPotential.Path SlideStep 2 s t ∧ GoodS c0 rho tau t ∧ potential t + 4 = potential s := by
  have h3 := capS_tau1 hn hs hj hjn hx hy
  obtain ⟨h, c⟩ := s
  obtain ⟨_, z, hI, h01, h0r, _⟩ := hs.at hj hjn hn
  simp only at hj z hI hx hy
  subst hj
  have hc := z.proper
  obtain ⟨d, path, z', rfl⟩ := row_tau1 hn z hx hy
  set i : ZMod n := (j : ZMod n) with hi
  have e2 : i - 2 = ((j-2 : ℕ) : ZMod n) := by rw [cast_sub_nat (by omega), hi]; norm_num
  have e1 : i - 1 = ((j-1 : ℕ) : ZMod n) := by rw [cast_sub_nat (by omega), hi]; norm_num
  have n31 : i - 3 ≠ i - 1 := by
    have := minus_offset_ne (i-1) 2 (by omega) (by omega)
    rw [show i - 1 - ((2 : ℕ) : ZMod n) = i - 3 by push_cast; ring] at this; exact this
  have n30 : i - 3 ≠ i := minus_offset_ne i 3 (by omega) (by omega)
  have n20 : i - 2 ≠ i := minus_offset_ne i 2 (by omega) (by omega)
  have n10 : i - 1 ≠ i := minus_ne hn i
  -- the zero under the old hole: `c(v_{j-2}) = 0`
  have hz : c (v (i-2)) = 0 := by
    have := z'.vnext
    rw [show i - 2 + 1 = i - 1 by ring] at this
    simpa [slide, n20] using this
  refine ⟨_, path, ⟨j-2, by omega, by omega, by rw [← e2], by rw [← e2]; exact z', ?_, h01, h0r, ?_⟩, ?_⟩
  · refine zInterval_slide (zInterval_slide hI (by omega) ?_) le_rfl ?_
    · intro k hk; exact ⟨v_ne_nat (by omega) (by omega) (by omega), by simp⟩
    · intro k hk; rw [e1]; exact ⟨v_ne_nat (by omega) (by omega) (by omega), by simp⟩
  · -- next `x` meets the old zero, so it is not 0
    intro hx0
    exfalso
    rw [← e2, show i - 2 - 1 = i - 3 by ring] at hx0
    have hx0' : c (v (i-3)) = 0 := by simpa [slide, n31, n30] using hx0
    have a := adj_vv hn (i-3)
    rw [show i - 3 + 1 = i - 2 by ring] at a
    exact hc a (by simpa using n30) (by simpa using n20) (hx0'.trans hz.symm)
  · show potential (v (i - 2), _) + 4 = potential (v i, _)
    rw [e2, potential_v (by omega), potential_v (by omega)]
    omega

theorem macroS_A (hn : 5 ≤ n) {c0 : Vertex n → Colour} {rho tau : Colour} {s : State n}
    {j : ℕ} (hs : GoodS c0 rho tau s) (hj : s.1 = v (j : ZMod n)) (hjn : j ≤ n - 2)
    (hx : s.2 (v ((j : ZMod n) - 1)) = rho) (hy : s.2 (u (j : ZMod n)) = tau)
    (hv2 : s.2 (v ((j : ZMod n) - 2)) = 0) (hu2 : s.2 (u ((j : ZMod n) - 2)) = tau) :
    ∃ t, VacancyPotential.Path SlideStep 4 s t ∧ GoodS c0 rho tau t ∧ potential t + 4 = potential s := by
  have h3 := capS_A hn hs hj hjn hx hy hv2
  obtain ⟨h, c⟩ := s
  obtain ⟨_, z, hI, h01, h0r, _⟩ := hs.at hj hjn hn
  simp only at hj z hI hx hy hv2 hu2
  subst hj
  have hc := z.proper
  obtain ⟨d, path, z', rfl⟩ := row_rhotau_A hn z hx hy hv2 hu2
  set i : ZMod n := (j : ZMod n) with hi
  have e2 : i - 2 = ((j-2 : ℕ) : ZMod n) := by rw [cast_sub_nat (by omega), hi]; norm_num
  have e1 : i - 1 = ((j-1 : ℕ) : ZMod n) := by rw [cast_sub_nat (by omega), hi]; norm_num
  have n31 : i - 3 ≠ i - 1 := by simpa using sub_ne_sub i (a := 3) (b := 1) (by omega) (by omega) (by omega)
  have n30 : i - 3 ≠ i := minus_offset_ne i 3 (by omega) (by omega)
  have n20 : i - 2 ≠ i := minus_offset_ne i 2 (by omega) (by omega)
  refine ⟨_, path, ⟨j-2, by omega, by omega, by rw [← e2], by rw [← e2]; exact z', ?_, h01, h0r, ?_⟩, ?_⟩
  · refine zInterval_slide (zInterval_slide (zInterval_slide (zInterval_slide hI (by omega) ?_)
      le_rfl ?_) le_rfl ?_) le_rfl ?_
    · intro k hk; exact ⟨v_ne_nat (by omega) (by omega) (by omega), by simp⟩
    · intro k hk; exact ⟨by simp, u_ne_nat (by omega) (by omega) (by omega)⟩
    · intro k hk; rw [e1]; exact ⟨by simp, u_ne_nat (by omega) (by omega) (by omega)⟩
    · intro k hk; rw [e1]; exact ⟨v_ne_nat (by omega) (by omega) (by omega), by simp⟩
  · intro hx0
    exfalso
    rw [← e2, show i - 2 - 1 = i - 3 by ring] at hx0
    have hx0' : c (v (i-3)) = 0 := by simpa [slide, n31, n30] using hx0
    have a := adj_vv hn (i-3)
    rw [show i - 3 + 1 = i - 2 by ring] at a
    exact hc a (by simpa using n30) (by simpa using n20) (hx0'.trans hv2.symm)
  · show potential (v (i - 2), _) + 4 = potential (v i, _)
    rw [e2, potential_v (by omega), potential_v (by omega)]
    omega

theorem macroS_B (hn : 5 ≤ n) {c0 : Vertex n → Colour} {rho tau : Colour} {s : State n}
    {j : ℕ} (hs : GoodS c0 rho tau s) (hj : s.1 = v (j : ZMod n)) (hjn : j ≤ n - 2)
    (hx : s.2 (v ((j : ZMod n) - 1)) = rho) (hy : s.2 (u (j : ZMod n)) = tau)
    (hv2 : s.2 (v ((j : ZMod n) - 2)) = tau) :
    ∃ t, VacancyPotential.Path SlideStep 4 s t ∧ GoodS c0 rho tau t ∧ potential t + 6 = potential s := by
  have h4 := capS_B hn hs hj hjn hx hy hv2
  obtain ⟨h, c⟩ := s
  obtain ⟨_, z, hI, h01, h0r, _⟩ := hs.at hj hjn hn
  simp only at hj z hI hx hy hv2
  subst hj
  have hc := z.proper
  obtain ⟨d, path, z', rfl⟩ := row_rhotau_B hn z hx hy hv2
  set i : ZMod n := (j : ZMod n) with hi
  have e3 : i - 3 = ((j-3 : ℕ) : ZMod n) := by rw [cast_sub_nat (by omega), hi]; norm_num
  have e2 : i - 2 = ((j-2 : ℕ) : ZMod n) := by rw [cast_sub_nat (by omega), hi]; norm_num
  have e1 : i - 1 = ((j-1 : ℕ) : ZMod n) := by rw [cast_sub_nat (by omega), hi]; norm_num
  have n42 : i - 4 ≠ i - 2 := by simpa using sub_ne_sub i (a := 4) (b := 2) (by omega) (by omega) (by omega)
  have n40 : i - 4 ≠ i := minus_offset_ne i 4 (by omega) (by omega)
  have n30 : i - 3 ≠ i := minus_offset_ne i 3 (by omega) (by omega)
  -- the zero forced under the landing: `c(v_{j-3}) = 0`
  have hz : c (v (i-3)) = 0 := by
    have := z'.vnext
    rw [show i - 3 + 1 = i - 2 by ring] at this
    simpa [slide, n30] using this
  refine ⟨_, path, ⟨j-3, by omega, by omega, by rw [← e3], by rw [← e3]; exact z', ?_, h01, h0r, ?_⟩, ?_⟩
  · refine zInterval_slide (zInterval_slide (zInterval_slide (zInterval_slide hI (by omega) ?_)
      le_rfl ?_) le_rfl ?_) le_rfl ?_
    · intro k hk; exact ⟨v_ne_nat (by omega) (by omega) (by omega), by simp⟩
    · intro k hk; exact ⟨by simp, u_ne_nat (by omega) (by omega) (by omega)⟩
    · intro k hk; rw [e1]; exact ⟨by simp, u_ne_nat (by omega) (by omega) (by omega)⟩
    · intro k hk; rw [e2]; exact ⟨v_ne_nat (by omega) (by omega) (by omega), by simp⟩
  · intro hx0
    exfalso
    rw [← e3, show i - 3 - 1 = i - 4 by ring] at hx0
    have hx0' : c (v (i-4)) = 0 := by simpa [slide, n42, n40] using hx0
    have a := adj_vv hn (i-4)
    rw [show i - 4 + 1 = i - 3 by ring] at a
    exact hc a (by simpa using n40) (by simpa using n30) (hx0'.trans hz.symm)
  · show potential (v (i - 3), _) + 6 = potential (v i, _)
    rw [e3, potential_v (by omega), potential_v (by omega)]
    omega

theorem macroS0 (hn : 5 ≤ n) {c0 : Vertex n → Colour} {s : State n} {j : ℕ}
    (hs : GoodS0 c0 s) (hj : s.1 = v (j : ZMod n)) (hj4 : 4 ≤ j) (hjn : j ≤ n - 2) :
    (∃ t, VacancyPotential.Path SlideStep 1 s t ∧ Done t) ∨
    (∃ t, VacancyPotential.Path SlideStep 3 s t ∧ GoodS0 c0 t ∧ potential t + 4 = potential s) := by
  obtain ⟨h, c⟩ := s
  obtain ⟨rho, tau, _, z, hI, hp0, hx, hy⟩ := hs.at hj hjn hn
  simp only at hj z hI hx hy
  subst hj
  rcases row_S0_branch hn z hy with hu | hu
  · right
    obtain ⟨d, p, q, path, z', hz, hq, rfl⟩ := row_S0_return hn z hx hy hu
    set i : ZMod n := (j : ZMod n) with hi
    have e2 : i - 2 = ((j-2 : ℕ) : ZMod n) := by rw [cast_sub_nat (by omega), hi]; norm_num
    have e1 : i - 1 = ((j-1 : ℕ) : ZMod n) := by rw [cast_sub_nat (by omega), hi]; norm_num
    refine ⟨_, path, ⟨j-2, p, q, by omega, by omega, by rw [← e2], by rw [← e2]; exact z', ?_,
      hp0, ?_, ?_⟩, ?_⟩
    · refine zInterval_slide (zInterval_slide (zInterval_slide hI (by omega) ?_) le_rfl ?_) le_rfl ?_
      · intro k hk; exact ⟨v_ne_nat (by omega) (by omega) (by omega), by simp⟩
      · intro k hk; exact ⟨by simp, u_ne_nat (by omega) (by omega) (by omega)⟩
      · intro k hk; rw [e1]; exact ⟨by simp, u_ne_nat (by omega) (by omega) (by omega)⟩
    · rw [← e2, show i - 2 - 1 = i - 3 by ring]; exact hz
    · rw [← e2]; exact hq
    · show potential (v (i - 2), _) + 4 = potential (v i, _)
      rw [e2, potential_v (by omega), potential_v (by omega)]
      omega
  · left
    obtain ⟨d, path, hf, hp, hpo⟩ := row_S0_fill hn z hx hy hu
    exact ⟨_, path, hf, hp, isBelt_u _, hpo⟩

theorem macroD (hn : 5 ≤ n) {c0 : Vertex n → Colour} {s : State n} {i : ℕ}
    (hs : GoodD c0 s) (hi : s.1 = u (i : ZMod n)) (hin : i + 4 ≤ n)
    (hx : s.2 (v ((i : ZMod n) + 1)) = 0) :
    ∃ t, VacancyPotential.Path SlideStep 3 s t ∧ GoodD c0 t ∧ potential t + 4 = potential s := by
  obtain ⟨h, c⟩ := s
  obtain ⟨rho, tau, d, hI, hcu, hcv⟩ := GoodD.at hs hi (by omega) hn
  simp only at hi d hI hx
  subst hi
  obtain ⟨e, p, q, path, d', rfl⟩ := rowD_return hn d hx
  have c2 : (i : ZMod n) + 2 = ((i+2 : ℕ) : ZMod n) := by push_cast; ring
  have c1 : (i : ZMod n) + 1 = ((i+1 : ℕ) : ZMod n) := by push_cast; ring
  refine ⟨_, path, ⟨i+2, q, p, by omega, by rw [← c2], by rw [← c2]; exact d', ?_, hcu, hcv⟩, ?_⟩
  · rw [c1, c2]
    refine dInterval_slide (dInterval_slide (dInterval_slide hI (by omega) ?_) le_rfl ?_) le_rfl ?_
    · intro k hk hkn; exact ⟨by simp, fun _ => u_ne_nat (by omega) hkn (by omega)⟩
    · intro k hk hkn; exact ⟨v_ne_nat (by omega) hkn (by omega), fun _ => by simp⟩
    · intro k hk hkn; exact ⟨v_ne_nat (by omega) hkn (by omega), fun _ => by simp⟩
  · show potential (u ((i : ZMod n) + 2), _) + 4 = potential (u (i : ZMod n), _)
    rw [c2, potential_u (by omega), potential_u (by omega)]
    omega

/-! ## §7 Controllers: the `budget` premise, discharged by rows, caps and macros -/

theorem controls_S (hn : 5 ≤ n) (c0 : Vertex n → Colour) (rho tau : Colour) :
    Controls (GoodS c0 rho tau) := by
  rintro ⟨h, c⟩ hs
  obtain ⟨j, hj1, hjn, hh, z, _, _, _, hS⟩ := id hs
  simp only at hh z hS
  subst hh
  have hc := z.proper
  obtain ⟨ca, cb⟩ := z.poles
  obtain ⟨hr0, hr1, ht0, ht1, hrt⟩ := z.pair
  have hpot : potential (v (j : ZMod n), c) = 2 * j := potential_v (by omega) c
  set i : ZMod n := (j : ZMod n) with hi
  have hm1 : (v (i-1) : Vertex n) ≠ v i := by simpa using v_sub_ne i 1 (by omega) (by omega)
  have hm2 : (v (i-2) : Vertex n) ≠ v i := v_sub_ne i 2 (by omega) (by omega)
  have hx1 : c (v (i-1)) ≠ 1 := (pole_exclusion hc (by simp) (by simp) ca cb (i-1)).2 hm1
  have hy0 : c (u i) ≠ 0 := (pole_exclusion hc (by simp) (by simp) ca cb i).1 (by simp)
  have hyr : c (u i) ≠ rho := by
    rw [← z.unext]; exact hc (adj_uu hn i) (by simp) (by simp)
  have hxy : c (v (i-1)) ≠ c (u i) := fun e => hc (adj_uv_prev hn i) (by simp) hm1 e.symm
  rcases zrow_cases rho tau _ _ z.pair hx1 hy0 hyr hxy with
    ⟨hxt, hyt⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · -- fill rows `S_ρ1`, `S_{0,1}`
    left
    exact ⟨0, _, .nil _, ⟨row_fill (hn := hn) z hxt hyt, hc, isBelt_v _, ⟨ca, cb⟩⟩, by omega⟩
  · -- `S_τ1`
    right
    obtain ⟨t, p, ht, hdrop⟩ := macroS_tau1 hn hs rfl hjn hx hy
    exact ⟨2, t, p, ht, by omega, by omega⟩
  · -- `S_ρτ`
    have hu1 := rhotau_forced_u hn z hx hy
    have e21 : i - 2 + 1 = i - 1 := by ring
    have hv2a : c (v (i-2)) ≠ 1 := (pole_exclusion hc (by simp) (by simp) ca cb (i-2)).2 hm2
    have hv2b : c (v (i-2)) ≠ rho := by
      rw [← hx]; have a := adj_vv hn (i-2); rw [e21] at a; exact hc a hm2 hm1
    rcases rhotau_branch rho tau _ z.pair hv2a hv2b with hv2 | hv2
    · have hu2a : c (u (i-2)) ≠ 0 :=
        (pole_exclusion hc (by simp) (by simp) ca cb (i-2)).1 (by simp)
      have hu2b : c (u (i-2)) ≠ 1 := by
        rw [← hu1]; have a := adj_uu hn (i-2); rw [e21] at a; exact hc a (by simp) (by simp)
      rcases upper_branch rho tau _ z.pair hu2a hu2b with hu2 | hu2
      · -- branch A, filled after two slides
        left
        obtain ⟨d, p, hf, hp, hpd⟩ := row_rhotau_fill hn z hx hy hv2 hu2
        exact ⟨2, _, p, ⟨hf, hp, isBelt_u _, hpd⟩, by omega⟩
      · -- branch A, return
        right
        obtain ⟨t, p, ht, hdrop⟩ := macroS_A hn hs rfl hjn hx hy hv2 hu2
        exact ⟨4, t, p, ht, by omega, by omega⟩
    · -- branch B
      right
      obtain ⟨t, p, ht, hdrop⟩ := macroS_B hn hs rfl hjn hx hy hv2
      exact ⟨4, t, p, ht, by omega, by omega⟩
  · -- `S_0` cannot occur in the S-family
    exact absurd ((hy.symm.trans (hS hx))) ht1

theorem controls_S0 (hn : 5 ≤ n) (c0 : Vertex n → Colour) :
    Controls (GoodS0 c0) := by
  rintro ⟨h, c⟩ hs
  obtain ⟨j, rho, tau, hj2, hjn, hh, _⟩ := id hs
  simp only at hh
  subst hh
  have hpot : potential (v (j : ZMod n), c) = 2 * j := potential_v (by omega) c
  rcases (show j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | h4
  · left
    obtain ⟨t, p, ht⟩ := capS0_two hn hs (by simp)
    exact ⟨1, t, p, ht, by omega⟩
  · exact (capS0_three hn hs (by simp)).elim
  · rcases macroS0 hn hs rfl h4 hjn with ⟨t, p, ht⟩ | ⟨t, p, ht, hdrop⟩
    · left; exact ⟨1, t, p, ht, by omega⟩
    · right; exact ⟨3, t, p, ht, by omega, by omega⟩

theorem controls_D (hn : 5 ≤ n) (c0 : Vertex n → Colour) : Controls (GoodD c0) := by
  rintro ⟨h, c⟩ hs
  obtain ⟨i, rho, tau, hin, hh, dst, _⟩ := id hs
  simp only at hh dst
  subst hh
  have hpot : potential (u (i : ZMod n), c) = 2 * (n - i) - 1 := potential_u (by omega) c
  by_cases hx : c (v ((i : ZMod n) + 1)) = 0
  · right
    rcases (show i = n - 2 ∨ i = n - 3 ∨ i + 4 ≤ n by omega) with h2 | h3 | h4
    · exact absurd hx (capD_last hn hs rfl h2)
    · exact (capD_prelast hn hs (by rw [h3])).elim
    · obtain ⟨t, p, ht, hdrop⟩ := macroD hn hs rfl h4 hx
      exact ⟨3, t, p, ht, by omega, by omega⟩
  · left
    obtain ⟨e, p, hf, hp, hpe⟩ := rowD_fill hn dst hx
    exact ⟨1, _, p, ⟨hf, hp, isBelt_v _, hpe⟩, by omega⟩

/-- Every good state of a controlled family reaches `Done` within `Φ` slides.
This is `VacancyPotential.budget` with slack 0 (proved). -/
theorem walk_of_controls {good : State n → Prop} (h : Controls good) (s : State n)
    (hs : good s) : ∃ k t, VacancyPotential.Path SlideStep k s t ∧ Done t ∧ k ≤ potential s := by
  have := budget good Done potential 0 h s hs
  simpa using this

/-! ## §4 Openings -/

/-- An unequal-pole start at `u_0`: properness off `u_0`, poles `0, 1`. -/
structure Start (c : Vertex n → Colour) : Prop where
  proper : ProperOff (G n) (u 0) c
  poles : UnequalPoles c

/-- O1: link `(0, 1, ρ, τ, ρ)` on `(a, u_1, v_0, v_{-1}, u_{-1})`. -/
def O1 (c : Vertex n → Colour) (rho tau : Colour) : Prop :=
  c (u 1) = 1 ∧ c (v 0) = rho ∧ c (v (-1)) = tau ∧ c (u (-1)) = rho
/-- O2: link `(0, 1, ρ, τ, 1)`, which is `D(0)`. -/
def O2 (c : Vertex n → Colour) (rho tau : Colour) : Prop :=
  c (u 1) = 1 ∧ c (v 0) = rho ∧ c (v (-1)) = tau ∧ c (u (-1)) = 1
/-- O3a: link `(0, 1, σ, 0, σ')`, written with `σ = ρ`, `σ' = τ`. -/
def O3a (c : Vertex n → Colour) (rho tau : Colour) : Prop :=
  c (u 1) = 1 ∧ c (v 0) = rho ∧ c (v (-1)) = 0 ∧ c (u (-1)) = tau
/-- O3b: link `(0, σ', σ, 0, 1)`, written with `σ = ρ`, `σ' = τ`. -/
def O3b (c : Vertex n → Colour) (rho tau : Colour) : Prop :=
  c (u 1) = tau ∧ c (v 0) = rho ∧ c (v (-1)) = 0 ∧ c (u (-1)) = 1

def Opening (c : Vertex n → Colour) : Prop :=
  ∃ rho tau, Pair rho tau ∧ (O1 c rho tau ∨ O2 c rho tau ∨ O3a c rho tau ∨ O3b c rho tau)

/-- The four classes on a bare link word `(0, p, q, r, s)`. -/
def WordClass (p q r s rho tau : Colour) : Prop :=
  (p = 1 ∧ q = rho ∧ r = tau ∧ s = rho) ∨ (p = 1 ∧ q = rho ∧ r = tau ∧ s = 1) ∨
  (p = 1 ∧ q = rho ∧ r = 0 ∧ s = tau) ∨ (p = tau ∧ q = rho ∧ r = 0 ∧ s = 1)

set_option synthInstance.maxSize 1000 in
/-- §4 class table (finite, `decide`): each of Math's 14 opening words is O1, O2, O3a or
O3b, either directly or after the reflection `(p,q,r,s) ↦ (s,r,q,p)`. -/
theorem openings_classes : ∀ p q r s : Colour,
    (p, q, r, s) ∈ BeltOpeningWords.openings →
    (∃ rho tau, Pair rho tau ∧ WordClass p q r s rho tau) ∨
    (∃ rho tau, Pair rho tau ∧ WordClass s r q p rho tau) := by
  unfold BeltOpeningWords.openings WordClass Pair
  decide

/-- §4 classification on the graph, from `BeltOpeningWords.classification` and the
reflection `R : (p,q,r,s) ↦ (s,r,q,p)`: an unfilled start is one of the four classes,
possibly after `R` (proved). -/
theorem opening_classes (hn : 5 ≤ n) {c : Vertex n → Colour} (hs : Start c)
    (hnf : ¬ Filled (u 0, c)) :
    Opening c ∨ Opening (transport reflection c) := by
  obtain ⟨hc, ca, cb⟩ := hs
  have m10 : (-1 : ZMod n) ≠ 0 := by
    simpa using sub_ne_sub (n := n) 0 (a := 1) (b := 0) (by omega) (by omega) (by omega)
  have h1 : (G n).Adj (u 0) (u 1) := by simpa using adj_uu hn 0
  have h2 : (G n).Adj (u 0) (v 0) := adj_uv hn 0
  have h3 : (G n).Adj (u 0) (v (-1)) := by simpa using adj_uv_prev hn 0
  have h4 : (G n).Adj (u 0) (u (-1)) := by
    have := (adj_u hn 0 (u (0-1))).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    rwa [zero_sub] at this
  have hw : BeltOpeningWords.ProperWord (c (u 1)) (c (v 0)) (c (v (-1))) (c (u (-1))) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (pole_exclusion hc (by simp) (by simp) ca cb 1).1
        (by simpa using TwoPoleBelt.one_ne_zero hn)
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (-1)).1 (by simpa using m10)
    · exact (pole_exclusion hc (by simp) (by simp) ca cb 0).2 (by simp)
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (-1)).2 (by simp)
    · have a := adj_uv_prev hn 1; rw [sub_self] at a
      exact hc a (by simpa using TwoPoleBelt.one_ne_zero hn) (by simp)
    · have a := adj_vv hn (-1); rw [neg_add_cancel] at a
      exact fun e => hc a (by simp) (by simp) e.symm
    · exact fun e => hc (adj_uv hn (-1)) (by simpa using m10) (by simp) e.symm
  have hu : BeltOpeningWords.UnfilledWord (c (u 1)) (c (v 0)) (c (v (-1))) (c (u (-1))) := by
    intro x
    by_contra hx
    push Not at hx
    apply hnf
    refine ⟨x, fun y hy => ?_⟩
    simp only at hy ⊢
    rcases (adj_u hn 0 y).mp hy with rfl | rfl | rfl | rfl | rfl
    · rw [ca]; exact hx.1.symm
    · simpa using hx.2.1.symm
    · exact hx.2.2.1.symm
    · simpa using hx.2.2.2.1.symm
    · simpa using hx.2.2.2.2.symm
  have hm := (BeltOpeningWords.classification _ _ _ _).mp ⟨hw, hu⟩
  rcases openings_classes _ _ _ _ hm with ⟨rho, tau, hp, hcl⟩ | ⟨rho, tau, hp, hcl⟩
  · left
    refine ⟨rho, tau, hp, ?_⟩
    simpa [WordClass, O1, O2, O3a, O3b] using hcl
  · right
    refine ⟨rho, tau, hp, ?_⟩
    simpa [WordClass, O1, O2, O3a, O3b, transport_reflection_apply, reflFun] using hcl

theorem neg_ne_neg {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    -(a : ZMod n) ≠ -(b : ZMod n) := by
  simpa using sub_ne_sub (0 : ZMod n) ha hb hab

/-- Small index facts used by the openings (proved). -/
theorem open_facts (hn : 5 ≤ n) :
    (-1 : ZMod n) ≠ 0 ∧ (-2 : ZMod n) ≠ 0 ∧ (-3 : ZMod n) ≠ 0 ∧ (-2 : ZMod n) ≠ -1 ∧
    (-3 : ZMod n) ≠ -1 ∧ (-3 : ZMod n) ≠ -2 ∧ (1 : ZMod n) ≠ 0 ∧ (1 : ZMod n) ≠ -1 ∧
    ((n - 2 : ℕ) : ZMod n) = -2 ∧ (-2 : ZMod n) + 1 = -1 ∧ (-3 : ZMod n) + 1 = -2 ∧
    (-1 : ZMod n) - 1 = -2 ∧ (-2 : ZMod n) - 1 = -3 ∧ (-1 : ZMod n) + 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by ring, by ring, by ring, by ring, by ring⟩
  · simpa using neg_ne_neg (n := n) (a := 1) (b := 0) (by omega) (by omega) (by omega)
  · simpa using neg_ne_neg (n := n) (a := 2) (b := 0) (by omega) (by omega) (by omega)
  · simpa using neg_ne_neg (n := n) (a := 3) (b := 0) (by omega) (by omega) (by omega)
  · simpa using neg_ne_neg (n := n) (a := 2) (b := 1) (by omega) (by omega) (by omega)
  · simpa using neg_ne_neg (n := n) (a := 3) (b := 1) (by omega) (by omega) (by omega)
  · simpa using neg_ne_neg (n := n) (a := 3) (b := 2) (by omega) (by omega) (by omega)
  · exact TwoPoleBelt.one_ne_zero hn
  · intro h
    have := sub_ne_sub (n := n) 0 (a := 1) (b := n - 1) (by omega) (by omega) (by omega)
    rw [cast_n_sub 1 (by omega)] at this
    apply this; simp only [zero_sub, neg_neg, Nat.cast_one]; rw [← h]
  · rw [cast_n_sub 2 (by omega)]; norm_num

/-- `I_{n-2}` holds after an opening whose old holes are `u_0` and one vertex of index
`n-1` (proved). -/
theorem zInterval_opening (hn : 5 ≤ n) (c : Vertex n → Colour) (x y z : Vertex n)
    (hx : x = v (-1) ∨ x = u (-1)) :
    ZInterval c (slide x z (slide (u 0) y c)) (n - 2) := by
  have hN : ((n - 1 : ℕ) : ZMod n) = -1 := by rw [cast_n_sub 1 (by omega)]; simp
  refine zInterval_slide (zInterval_slide (fun _ _ => ⟨rfl, rfl⟩) le_rfl ?_) le_rfl ?_
  · intro k hk
    refine ⟨by simp, ?_⟩
    have := u_ne_nat (n := n) (j := 0) (k := k + 1) (by omega) (by omega) (by omega)
    simpa using this
  · intro k hk
    rcases hx with rfl | rfl
    · refine ⟨?_, by simp⟩
      rw [← hN]; exact v_ne_nat (by omega) (by omega) (by omega)
    · refine ⟨by simp, ?_⟩
      rw [← hN]; exact u_ne_nat (by omega) (by omega) (by omega)

/-- O1: `u_0 → v_{-1}` [τ], `v_{-1} → v_{-2}` [0]; arrives at `GoodS` at `j = n-2`. -/
theorem opening_O1 (hn : 5 ≤ n) {c : Vertex n → Colour} {rho tau : Colour} (hs : Start c)
    (hp : Pair rho tau) (ho : O1 c rho tau) :
    ∃ t, VacancyPotential.Path SlideStep 2 (u 0, c) t ∧ GoodS c rho tau t ∧ potential t = 2 * (n - 2) := by
  obtain ⟨hu1, hv0, hv1, hum⟩ := ho
  obtain ⟨hc, ca, cb⟩ := hs
  obtain ⟨hr0, hr1, ht0, ht1, hrt⟩ := hp
  obtain ⟨m10, m20, m30, m21, m31, m32, p10, p1m, eN, e21, e32, f12, f23, e10⟩ := open_facts hn
  -- forced: `c(v_{-2}) = 0`
  have hz : c (v (-2)) = 0 := by
    apply tight_zero rho tau _ hr0 hr1 ht0 ht1 hrt
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (-2)).2 (by simp)
    · have a := adj_uv_prev hn (-1); rw [f12] at a
      rw [← hum]; exact fun e => hc a (by simpa using m10) (by simp) e.symm
    · have a := adj_vv hn (-2); rw [e21] at a
      rw [← hv1]; exact hc a (by simp) (by simp)
  let c1 := slide (u 0) (v (-1)) c
  have uniq1 : UniqueAt (G n) (u 0) (v (-1)) c := by
    have := unique_u_vprev hn 0 c; rw [zero_sub, zero_add] at this
    apply this
    · rw [ca, hv1]; exact ht0.symm
    · rw [hu1, hv1]; exact ht1.symm
    · rw [hv0, hv1]; exact hrt
    · rw [hum, hv1]; exact hrt
  have uniq2 : UniqueAt (G n) (v (-1)) (v (-2)) c1 := by
    have := unique_v_vprev hn (-1) c1; rw [f12, e10] at this
    apply this
    · simp [c1, cb, hz]
    · simpa [c1, slide, hum, hz, m20, p10] using hr0
    · simpa [c1, slide, hv1, hz, m20] using ht0
    · simpa [c1, slide, hv0, hz, m20] using hr0
  have adj1 : (G n).Adj (u 0) (v (-1)) := by
    have a := adj_uv_prev hn 0; rwa [zero_sub] at a
  have adj2 : (G n).Adj (v (-1)) (v (-2)) := by
    have a := adj_vv hn (-2); rw [e21] at a; exact a.symm
  have path : SlidePath 2 (u 0, c) (v (-2), slide (v (-1)) (v (-2)) c1) :=
    .cons adj1 uniq1 (.cons adj2 uniq2 (.nil _))
  have hc' := path.proper hc
  refine ⟨_, path_of_slidePath path, ⟨n - 2, by omega, le_rfl, by simp [eN], ?_,
    zInterval_opening hn c _ _ _ (Or.inl rfl), hu1, hv0, ?_⟩, ?_⟩
  · rw [eN]
    refine ⟨hc', ⟨by simp [c1, slide, ca], by simp [c1, slide, cb]⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩,
      ?_, ?_⟩
    · rw [e21]; simp [c1, slide, hz]
    · rw [e21]; simp [c1, slide, hum, p10]
  · -- `x = c(v_{-3}) ≠ 0`, since `v_{-3}` meets the old zero `v_{-2}`
    intro hx0; exfalso
    rw [eN, f23] at hx0
    have hx0' : c (v (-3)) = 0 := by simpa [c1, slide, m31, m30] using hx0
    have a := adj_vv hn (-3); rw [e32] at a
    exact hc a (by simp) (by simp) (hx0'.trans hz.symm)
  · show potential (v (-2), _) = _
    rw [← eN, potential_v (by omega)]

/-- O3a: `u_0 → u_{-1}` [τ], `u_{-1} → v_{-2}` [ρ]; arrives at `Z(n-2)` with `u_{n-2} = 1`.
Either already filled there, or `GoodS` (row `S_τ1`). -/
theorem opening_O3a (hn : 5 ≤ n) {c : Vertex n → Colour} {rho tau : Colour} (hs : Start c)
    (hp : Pair rho tau) (ho : O3a c rho tau) :
    ∃ t, VacancyPotential.Path SlideStep 2 (u 0, c) t ∧ GoodS c rho tau t ∧ potential t = 2 * (n - 2) := by
  obtain ⟨hu1, hv0, hv1, hum⟩ := ho
  obtain ⟨hc, ca, cb⟩ := hs
  obtain ⟨hr0, hr1, ht0, ht1, hrt⟩ := hp
  obtain ⟨m10, m20, m30, m21, m31, m32, p10, p1m, eN, e21, e32, f12, f23, e10⟩ := open_facts hn
  have a12 : (G n).Adj (u (-1)) (v (-2)) := by have a := adj_uv_prev hn (-1); rwa [f12] at a
  have a22 : (G n).Adj (u (-2)) (u (-1)) := by have a := adj_uu hn (-2); rwa [e21] at a
  have b21 : (G n).Adj (v (-2)) (v (-1)) := by have a := adj_vv hn (-2); rwa [e21] at a
  -- forced: `c(v_{-2}) = ρ`, `c(u_{-2}) = 1`
  have hv2 : c (v (-2)) = rho := by
    apply tight_force rho tau _ hr0 hr1 ht0 ht1 hrt
    · rw [← hv1]; exact hc b21 (by simp) (by simp)
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (-2)).2 (by simp)
    · rw [← hum]; exact fun e => hc a12 (by simpa using m10) (by simp) e.symm
  have hu2 : c (u (-2)) = 1 := by
    apply tight_one rho tau _ hr0 hr1 ht0 ht1 hrt
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (-2)).1 (by simpa using m20)
    · rw [← hv2]; exact hc (adj_uv hn (-2)) (by simpa using m20) (by simp)
    · rw [← hum]; exact hc a22 (by simpa using m20) (by simpa using m10)
  let c1 := slide (u 0) (u (-1)) c
  have uniq1 : UniqueAt (G n) (u 0) (u (-1)) c := by
    have := unique_u_uprev hn 0 c; rw [zero_sub, zero_add] at this
    apply this
    · rw [ca, hum]; exact ht0.symm
    · rw [hu1, hum]; exact ht1.symm
    · rw [hv0, hum]; exact hrt
    · rw [hv1, hum]; exact ht0.symm
  have uniq2 : UniqueAt (G n) (u (-1)) (v (-2)) c1 := by
    have := unique_u_vprev hn (-1) c1; rw [f12, e10] at this
    apply this
    · simpa [c1, slide, ca, hv2] using hr0.symm
    · simpa [c1, slide, hum, hv2] using hrt.symm
    · simpa [c1, slide, hv1, hv2] using hr0.symm
    · simpa [c1, slide, hu2, hv2, m21, m20] using hr1.symm
  have adj1 : (G n).Adj (u 0) (u (-1)) := by
    have := (adj_u hn 0 (u (0-1))).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    rwa [zero_sub] at this
  have path : SlidePath 2 (u 0, c) (v (-2), slide (u (-1)) (v (-2)) c1) :=
    .cons adj1 uniq1 (.cons a12 uniq2 (.nil _))
  have hc' := path.proper hc
  refine ⟨_, path_of_slidePath path, ⟨n - 2, by omega, le_rfl, by simp [eN], ?_,
    zInterval_opening hn c _ _ _ (Or.inr rfl), hu1, hv0, ?_⟩, ?_⟩
  · rw [eN]
    refine ⟨hc', ⟨by simp [c1, slide, ca], by simp [c1, slide, cb]⟩, ⟨hr0, hr1, ht0, ht1, hrt⟩,
      ?_, ?_⟩
    · rw [e21]; simp [c1, slide, hv1]
    · rw [e21]; simp [c1, slide, hv2]
  · intro _
    rw [eN]; simp [c1, slide, hu2, m21, m20]
  · show potential (v (-2), _) = _
    rw [← eN, potential_v (by omega)]

/-- O3b: `u_0 → u_{-1}` [1], `u_{-1} → v_{-2}` [x]; arrives at an `S_0` state at `n-2`. -/
theorem opening_O3b (hn : 5 ≤ n) {c : Vertex n → Colour} {rho tau : Colour} (hs : Start c)
    (hp : Pair rho tau) (ho : O3b c rho tau) :
    (∃ t, VacancyPotential.Path SlideStep 2 (u 0, c) t ∧ GoodS0 c t ∧ potential t = 2 * (n - 2)) ∨
    (∃ k t, VacancyPotential.Path SlideStep k (u 0, c) t ∧ Done t ∧ k ≤ 2) := by
  left
  obtain ⟨hu1, hv0, hv1, hum⟩ := ho
  obtain ⟨hc, ca, cb⟩ := hs
  have hp' := hp
  obtain ⟨hr0, hr1, ht0, ht1, hrt⟩ := hp
  obtain ⟨m10, m20, m30, m21, m31, m32, p10, p1m, eN, e21, e32, f12, f23, e10⟩ := open_facts hn
  have a12 : (G n).Adj (u (-1)) (v (-2)) := by have a := adj_uv_prev hn (-1); rwa [f12] at a
  have a22 : (G n).Adj (u (-2)) (u (-1)) := by have a := adj_uu hn (-2); rwa [e21] at a
  have b21 : (G n).Adj (v (-2)) (v (-1)) := by have a := adj_vv hn (-2); rwa [e21] at a
  have b32 : (G n).Adj (v (-3)) (v (-2)) := by have a := adj_vv hn (-3); rwa [e32] at a
  have a23 : (G n).Adj (u (-2)) (v (-3)) := by have a := adj_uv_prev hn (-2); rwa [f23] at a
  -- forced: `x = c(v_{-2})`, `y = c(u_{-2})` are the two non-pole colours, `c(v_{-3}) = 0`
  set x := c (v (-2)) with hxdef
  set y := c (u (-2)) with hydef
  have hx1 : x ≠ 1 := (pole_exclusion hc (by simp) (by simp) ca cb (-2)).2 (by simp)
  have hx0 : x ≠ 0 := by rw [← hv1]; exact hc b21 (by simp) (by simp)
  have hy0 : y ≠ 0 := (pole_exclusion hc (by simp) (by simp) ca cb (-2)).1 (by simpa using m20)
  have hy1 : y ≠ 1 := by rw [← hum]; exact hc a22 (by simpa using m20) (by simpa using m10)
  have hxy : x ≠ y := fun e => hc (adj_uv hn (-2)) (by simpa using m20) (by simp) e.symm
  have hz : c (v (-3)) = 0 := by
    apply tight_zero x y _ hx0 hx1 hy0 hy1 hxy
    · exact (pole_exclusion hc (by simp) (by simp) ca cb (-3)).2 (by simp)
    · exact hc b32 (by simp) (by simp)
    · exact fun e => hc a23 (by simpa using m20) (by simp) e.symm
  let c1 := slide (u 0) (u (-1)) c
  have uniq1 : UniqueAt (G n) (u 0) (u (-1)) c := by
    have := unique_u_uprev hn 0 c; rw [zero_sub, zero_add] at this
    apply this
    · rw [ca, hum]; decide
    · rw [hu1, hum]; exact ht1
    · rw [hv0, hum]; exact hr1
    · rw [hv1, hum]; decide
  have uniq2 : UniqueAt (G n) (u (-1)) (v (-2)) c1 := by
    have := unique_u_vprev hn (-1) c1; rw [f12, e10] at this
    apply this
    · simpa [c1, slide, ca, m20] using hx0.symm
    · simpa [c1, slide, hum, m20] using hx1.symm
    · simpa [c1, slide, hv1, m20] using hx0.symm
    · simpa [c1, slide, m21, m20] using hxy.symm
  have adj1 : (G n).Adj (u 0) (u (-1)) := by
    have := (adj_u hn 0 (u (0-1))).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    rwa [zero_sub] at this
  have path : SlidePath 2 (u 0, c) (v (-2), slide (u (-1)) (v (-2)) c1) :=
    .cons adj1 uniq1 (.cons a12 uniq2 (.nil _))
  have hc' := path.proper hc
  refine ⟨_, path_of_slidePath path, ⟨n - 2, x, y, by omega, le_rfl, by simp [eN], ?_,
    zInterval_opening hn c _ _ _ (Or.inr rfl), ?_, ?_, ?_⟩, ?_⟩
  · rw [eN]
    refine ⟨hc', ⟨by simp [c1, slide, ca], by simp [c1, slide, cb]⟩, ⟨hx0, hx1, hy0, hy1, hxy⟩,
      ?_, ?_⟩
    · rw [e21]; simp [c1, slide, hv1]
    · rw [e21]; simp [c1, slide, hxdef]
  · rw [hv0, hu1]; exact hp'
  · rw [eN, f23]; simp [c1, slide, hz]
  · rw [eN]; simp [c1, slide, m21, m20, hydef]
  · show potential (v (-2), _) = _
    rw [← eN, potential_v (by omega)]

/-- O2 is `D(0)`, with no slide. -/
theorem opening_O2 (hn : 5 ≤ n) {c : Vertex n → Colour} {rho tau : Colour} (hs : Start c)
    (hp : Pair rho tau) (ho : O2 c rho tau) :
    GoodD c (u 0, c) ∧ potential (u 0, c) = 2 * n - 1 := by
  obtain ⟨h1, hq, hr, hs1⟩ := ho
  have e1 : ((n-1 : ℕ) : ZMod n) = -1 := by rw [cast_n_sub 1 (by omega)]; simp
  refine ⟨⟨0, rho, tau, by omega, by simp, ?_, fun _ _ _ => ⟨rfl, fun _ => rfl⟩, ?_, ?_⟩, ?_⟩
  · simp only [Nat.cast_zero]
    exact ⟨hs.proper, hs.poles, hp, by simpa using h1, by simpa using hs1, hq, by simpa using hr⟩
  · rw [e1]; exact hs1
  · rw [e1, hr]; exact hp.2.2.1
  · simpa using potential_u (n := n) (i := 0) (by omega) c

/-! ## §0 / §7 The theorem -/

/-- One unreflected opening class, then the budget walk (proved from the lemmas above). -/
theorem walk_of_opening (hn : 5 ≤ n) {c : Vertex n → Colour} (hs : Start c) (ho : Opening c) :
    ∃ k t, VacancyPotential.Path SlideStep k (u 0, c) t ∧ Done t ∧ k ≤ 2 * n := by
  obtain ⟨rho, tau, hp, h1 | h2 | h3a | h3b⟩ := ho
  · obtain ⟨t, p, ht, hpot⟩ := opening_O1 hn hs hp h1
    obtain ⟨k, w, q, hw, hk⟩ := walk_of_controls (controls_S hn c rho tau) t ht
    exact ⟨2 + k, w, p.append q, hw, by omega⟩
  · obtain ⟨hg, hpot⟩ := opening_O2 hn hs hp h2
    obtain ⟨k, w, q, hw, hk⟩ := walk_of_controls (controls_D hn c) _ hg
    exact ⟨k, w, q, hw, by omega⟩
  · obtain ⟨t, p, ht, hpot⟩ := opening_O3a hn hs hp h3a
    obtain ⟨k, w, q, hw, hk⟩ := walk_of_controls (controls_S hn c rho tau) t ht
    exact ⟨2 + k, w, p.append q, hw, by omega⟩
  · rcases opening_O3b hn hs hp h3b with ⟨t, p, ht, hpot⟩ | ⟨k, w, q, hw, hk⟩
    · obtain ⟨k, w, q, hw, hk⟩ := walk_of_controls (controls_S0 hn c) t ht
      exact ⟨2 + k, w, p.append q, hw, by omega⟩
    · exact ⟨k, w, q, hw, by omega⟩

/-- Normalised form: poles `0, 1`, hole `u_0`. At most `2n` slides, poles fixed.
Proved from the opening, cap, row and macro lemmas, `budget`, and the reflection `R`. -/
theorem belt_unequal_normalised (hn : 5 ≤ n) (c : Vertex n → Colour) (hs : Start c) :
    ∃ k t, VacancyPotential.Path SlideStep k (u 0, c) t ∧ Done t ∧ k ≤ 2 * n := by
  by_cases hf : Filled (u 0, c)
  · exact ⟨0, _, .nil _, ⟨hf, hs.proper, isBelt_u 0, hs.poles⟩, by omega⟩
  rcases opening_classes hn hs hf with ho | ho
  · exact walk_of_opening hn hs ho
  · -- reflect, walk, reflect back
    have hs' : Start (transport reflection c) := by
      refine ⟨by simpa using properOff_transport reflection hs.proper, ?_⟩
      exact ⟨by simpa [transport_reflection_apply, reflFun] using hs.poles.1,
        by simpa [transport_reflection_apply, reflFun] using hs.poles.2⟩
    obtain ⟨k, t, p, ⟨hf', hp', hb', hpo'⟩, hk⟩ := walk_of_opening hn hs' ho
    have q := slidePath_transport reflection (slidePath_of_path p)
    simp only [reflection_u0, transport_reflection_invol] at q
    refine ⟨k, _, path_of_slidePath q, ⟨target_transport reflection hf',
      properOff_transport reflection hp', isBelt_reflection hb', ?_⟩, hk⟩
    exact ⟨by simpa [transport_reflection_apply, reflFun] using hpo'.1,
      by simpa [transport_reflection_apply, reflFun] using hpo'.2⟩

/-- Colour permutations commute with slides. -/
theorem slidePath_recolour (π : Equiv.Perm Colour) {k : ℕ} {s t : State n}
    (p : SlidePath k s t) : SlidePath k (s.1, π ∘ s.2) (t.1, π ∘ t.2) := by
  induction p with
  | nil s => exact .nil _
  | @cons k h x c t adj uniq _ ih =>
    have hs : π ∘ slide h x c = slide h x (π ∘ c) := by
      funext y; by_cases hy : y = h <;> simp [slide, hy]
    refine .cons adj (fun y hy e => uniq hy (π.injective e)) ?_
    simpa [hs] using ih

/-- Two distinct pole colours can be renamed `0, 1` (proved). -/
theorem exists_perm_poles {x y : Colour} (hxy : x ≠ y) :
    ∃ π : Equiv.Perm Colour, π x = 0 ∧ π y = 1 := by
  let π₁ : Equiv.Perm Colour := Equiv.swap 0 x
  have h1 : π₁ x = 0 := Equiv.swap_apply_right 0 x
  have h2 : π₁ y ≠ 0 := by rw [← h1]; exact fun e => hxy (π₁.injective e).symm
  refine ⟨π₁.trans (Equiv.swap 1 (π₁ y)), ?_, ?_⟩
  · simp only [Equiv.trans_apply, h1]
    exact Equiv.swap_apply_of_ne_of_ne (by decide) h2.symm
  · simp only [Equiv.trans_apply]
    exact Equiv.swap_apply_right _ _

/-- **Theorem (belt vacancy, unequal poles).** For every `n ≥ 5` and every proper colouring
of `G_n − u_0` with `c(a) ≠ c(b)`, at most `2n` singleton slides reach a filled hole;
the poles are never the hole and keep their colours. -/
theorem belt_unequal (hn : 5 ≤ n) (c : Vertex n → Colour) (hc : ProperOff (G n) (u 0) c)
    (hab : c a ≠ c b) :
    ∃ k t, VacancyPotential.Path SlideStep k (u 0, c) t ∧ k ≤ 2 * n ∧ Filled t ∧ ProperOff (G n) t.1 t.2 ∧
      IsBelt t.1 ∧ t.2 a = c a ∧ t.2 b = c b := by
  -- normalise the pole colours to `0, 1` by a colour permutation
  obtain ⟨π, hπa, hπb⟩ := exists_perm_poles hab
  have hs : Start (π ∘ c) := ⟨properOff_recolour π hc, hπa, hπb⟩
  obtain ⟨k, t, p, ⟨hf, hp, hbt, hpo⟩, hk⟩ := belt_unequal_normalised hn _ hs
  have q := slidePath_recolour π.symm (slidePath_of_path p)
  have hcc : π.symm ∘ (π ∘ c) = c := by funext x; simp
  simp only [hcc] at q
  refine ⟨k, _, path_of_slidePath q, hk, target_recolour π.symm hf,
    properOff_recolour π.symm hp, hbt, ?_, ?_⟩
  · change π.symm (t.2 a) = c a; rw [hpo.1, ← hπa]; simp
  · change π.symm (t.2 b) = c b; rw [hpo.2, ← hπb]; simp

end SimpleGraph.TwoPoleBeltWalk
