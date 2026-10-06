module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyMobility

/-!
# Unrestricted vacancy mobility by transport

The normalized theorem `vacancy_mobility_normalized` assumes the ring colours are exactly
`gapWord`.  Here the pattern assumption is removed: rotate the ports cyclically and rename colours.
Either some colour is missing on the ring (a zero-move pure fill) or, when consecutive ring
ports are adjacent in the map (the ring is a 5-cycle), a proper 4-colouring of the ring has exactly
one repeated colour, at cyclic distance two, and a rotation plus colour renaming gives `Pattern`.
-/

@[expose] public section
namespace SimpleGraph.VacancyMobility
open VacancySlide VacancyShortFill

section Transport
variable {V C D : Type*} [DecidableEq V] [DecidableEq C] [DecidableEq D] (G : SimpleGraph V)

lemma properOff_rename {h : V} {c : V → C} (τ : C ≃ D) (hc : ProperOff G h c) :
    ProperOff G h (fun v => τ (c v)) :=
  fun _ _ e hu hv => τ.injective.ne (hc e hu hv)

lemma uniqueAt_rename {r x : V} {c : V → C} (τ : C ≃ D) (hu : UniqueAt G r x c) :
    UniqueAt G r x (fun v => τ (c v)) :=
  fun _ e eq => hu e (τ.injective eq)

lemma pairGraph_rename (h : V) (c : V → C) (τ : C ≃ D) (a b : C) :
    pairGraph G h (fun v => τ (c v)) (τ a) (τ b) = pairGraph G h c a b := by
  ext u v
  simp [pairGraph, Active]

lemma whole_rename {h : V} {c : V → C} {a b : C} {S : Set V} (τ : C ≃ D)
    (w : Whole G h c a b S) : Whole G h (fun v => τ (c v)) (τ a) (τ b) S := by
  obtain ⟨s, hs, hmem⟩ := w
  refine ⟨s, ?_, ?_⟩
  · simpa [Active] using hs
  · rw [pairGraph_rename]; exact hmem

lemma swap_rename (c : V → C) (τ : C ≃ D) (a b : C) (S : Set V) :
    swap (fun v => τ (c v)) (τ a) (τ b) S = fun v => τ (swap c a b S v) := by
  funext v
  by_cases hv : v ∈ S
  · rw [swap_in hv, swap_in hv]; simp only [Equiv.swap_apply_def, τ.apply_eq_iff_eq]
    split_ifs <;> rfl
  · rw [swap_out hv, swap_out hv]

lemma kempeStep_rename {h : V} {c d : V → C} (τ : C ≃ D) (k : KempeStep G h c d) :
    KempeStep G h (fun v => τ (c v)) (fun v => τ (d v)) := by
  obtain ⟨a, b, S, hab, w, rfl⟩ := k
  exact ⟨τ a, τ b, S, τ.injective.ne hab, whole_rename G τ w, (swap_rename c τ a b S).symm⟩

lemma target_rename {h : V} {c : V → C} (τ : C ≃ D) (t : Target G h c) :
    Target G h (fun v => τ (c v)) := by
  obtain ⟨x, hx⟩ := t
  exact ⟨τ x, fun v e eq => hx e (τ.injective eq)⟩

lemma purePath_rename {h : V} {n : Nat} {c d : V → C} (τ : C ≃ D)
    (p : PurePath G h n c d) :
    PurePath G h n (fun v => τ (c v)) (fun v => τ (d v)) := by
  induction p with
  | nil c => exact PurePath.nil _
  | cons k _ ih => exact PurePath.cons (kempeStep_rename G τ k) ih

lemma pureFill_rename {h : V} {c : V → C} {m : Nat} (τ : C ≃ D)
    (p : PureFill G h c m) : PureFill G h (fun v => τ (c v)) m := by
  obtain ⟨n, hn, d, pp, t⟩ := p
  exact ⟨n, hn, _, purePath_rename G τ pp, target_rename G τ t⟩

lemma approach_rename {h u : V} {c : V → Fin 4} (τ : Fin 4 ≃ Fin 4) (ap : Approach G h c u) :
    Approach G h (fun v => τ (c v)) u := by
  obtain ⟨d, first, proper, adj, uniq⟩ := ap
  refine ⟨fun v => τ (d v), ?_, properOff_rename G τ proper, adj, uniqueAt_rename G τ uniq⟩
  rcases first with rfl | k
  · exact Or.inl rfl
  · exact Or.inr (kempeStep_rename G τ k)

end Transport

section Combinatorics

/-- Colour renaming sending the repeated colour at position `k` to `0`, and the colours at
`k+1, k+3, k+4` to `1, 2, 3`. -/
def ringRename (f : Fin 5 → Fin 4) (k : Fin 5) (x : Fin 4) : Fin 4 :=
  if x = f k then 0 else if x = f (k+1) then 1 else if x = f (k+3) then 2 else 3

lemma ring_normalize :
    ∀ f : Fin 5 → Fin 4, (∀ i, f i ≠ f (i+1)) → (∀ x, ∃ i, f i = x) →
      ∃ k : Fin 5, Function.Injective (ringRename f k) ∧
        ∀ i, ringRename f k (f (i+k)) = gapWord i := by
  decide +kernel

end Combinatorics
end SimpleGraph.VacancyMobility

namespace SimpleGraph.SphericalMap
open VacancySlide VacancyShortFill VacancyMobility
variable {n : Nat} (M : SphericalMap n)

/-- Cyclic shift of the ports, preserving the rotation hypothesis. -/
def FiveLink.shift {h : Fin n} (L : FiveLink M.graph h) (k : Fin 5) : FiveLink M.graph h where
  port i := L.port (i + k)
  injective a b e := by
    have := L.injective e
    simpa using this
  neighbours v := by
    rw [L.neighbours v]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i - k, by simp⟩
    · rintro ⟨i, rfl⟩; exact ⟨i + k, rfl⟩

/-- Unrestricted native spherical degree-five mobility. If consecutive ring ports are adjacent
(the link of the hole is a 5-cycle), no pattern hypothesis is needed. -/
theorem vacancy_mobility_general {h : Fin n} (L : FiveLink M.graph h)
    {c : Fin n → Fin 4} (hc : ProperOff M.graph h c)
    (ring : ∀ i : Fin 5, M.graph.Adj (L.port i) (L.port (i+1)))
    (rot : ∀ i : Fin 5,
      M.rotation.next ⟨(h,L.port i),port_adj M.graph L i⟩ =
        ⟨(h,L.port (i+1)),port_adj M.graph L (i+1)⟩) :
    PureFill M.graph h c 1 ∨ ∀ u, M.Adj h u → Approach M.graph h c u := by
  classical
  by_cases surj : ∀ x : Fin 4, ∃ i, c (L.port i) = x
  · obtain ⟨k, inj, hk⟩ := ring_normalize (fun i => c (L.port i))
      (fun i => hc (ring i) (port_adj M.graph L i).ne.symm (port_adj M.graph L _).ne.symm)
      surj
    let σ : Fin 4 ≃ Fin 4 := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp inj)
    let L' := FiveLink.shift M L k
    have pat : Pattern M.graph L' (fun v => σ (c v)) := fun i => hk i
    have rot' : ∀ i : Fin 5,
        M.rotation.next ⟨(h, L'.port i), port_adj M.graph L' i⟩ =
          ⟨(h, L'.port (i+1)), port_adj M.graph L' (i+1)⟩ := by
      intro i
      have key : ∀ j j' : Fin 5, j' = j + 1 →
          M.rotation.next ⟨(h, L.port j), port_adj M.graph L j⟩ =
            ⟨(h, L.port j'), port_adj M.graph L j'⟩ := by
        rintro j j' rfl; exact rot j
      exact key (i + k) (i + 1 + k) (by abel)
    rcases vacancy_mobility_normalized M L' (properOff_rename _ σ hc) pat rot' with fill | mv
    · left
      have := pureFill_rename M.graph σ.symm fill
      simpa using this
    · right
      intro u hu
      have := approach_rename M.graph σ.symm (mv u hu)
      simpa using this
  · left
    push Not at surj
    obtain ⟨x, hx⟩ := surj
    refine ⟨0, by decide, c, PurePath.nil _, x, ?_⟩
    intro v ev
    obtain ⟨i, rfl⟩ := (L.neighbours v).mp ev
    exact hx i

end SimpleGraph.SphericalMap
