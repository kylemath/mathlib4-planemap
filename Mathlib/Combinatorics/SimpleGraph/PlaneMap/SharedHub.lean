/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.RotationSystem

/-!
# One singleton colour per hub (Lemma S)

Let `R` be a rotation system whose faces are all triangles, `r` a deleted root, and
`h` a vertex of degree at least five that is neither `r` nor adjacent to `r`. For
any colouring that is proper on the edges avoiding `r`, at most one neighbour of `h`
carries a colour used by no other neighbour of `h`.

Consecutive neighbours in the rotation at `h` are adjacent
(`RotationSystem.neighbor_rotation_adj`), so a set of neighbours containing no
rotation-consecutive pair has at most half of them (`two_mul_card_le_degree`). Two
singleton colours would force every other neighbour into the single remaining
colour, hence into such a set of size `degree - 2`, which is impossible from degree
five on.

Consequence: a two-vertex bichromatic component `{h, x}` requires `x` to be the
unique neighbour of `h` in its colour, so at most one such component contains `h`.
Toggles at a common hub therefore cannot coexist.
-/

@[expose] public section
namespace SimpleGraph.RotationSystem

variable {V : Type*} {G : SimpleGraph V} (R : RotationSystem G)
variable [Fintype V] [DecidableRel G.Adj]

/-- A set of neighbours with no rotation-consecutive pair has at most half of them. -/
theorem two_mul_card_le_degree (h : V) (S : Finset (G.neighborSet h))
    (hS : ∀ z ∈ S, R.neighborRotation h z ∉ S) :
    2 * S.card ≤ G.degree h := by
  classical
  have hdisj : Disjoint S (S.map (R.neighborRotation h).toEmbedding) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨w, hw, hwz⟩ := Finset.mem_map.1 hz'
    exact hS w hw (by simpa [← hwz] using hz)
  have hunion := Finset.card_union_of_disjoint hdisj
  have hle : (S ∪ S.map (R.neighborRotation h).toEmbedding).card ≤
      Fintype.card (G.neighborSet h) := Finset.card_le_univ _
  rw [card_neighborSet_eq_degree, hunion, Finset.card_map] at hle
  omega

private theorem fin4_eq_of_avoid (p q t s u : Fin 4) (h1 : p ≠ q) (h2 : p ≠ t) (h3 : q ≠ t)
    (hs1 : s ≠ p) (hs2 : s ≠ q) (hs3 : s ≠ t)
    (hu1 : u ≠ p) (hu2 : u ≠ q) (hu3 : u ≠ t) : s = u := by
  revert p q t s u
  decide

/-- **Lemma S.** At most one neighbour of a degree-at-least-five hub, away from the
deleted root, has a colour used by no other neighbour of the hub. -/
theorem singleton_colour_neighbour_unique
    (hfaces : ∀ f : R.Face, R.faceLength f = 3)
    (r h : V) (hhr : h ≠ r) (hadj : ¬ G.Adj h r) (hdeg : 5 ≤ G.degree h)
    (c : V → Fin 4) (hc : ∀ u v, G.Adj u v → u ≠ r → v ≠ r → c u ≠ c v)
    {x y : V} (hx : G.Adj h x) (hy : G.Adj h y)
    (hux : ∀ z, G.Adj h z → c z = c x → z = x)
    (huy : ∀ z, G.Adj h z → c z = c y → z = y) : x = y := by
  classical
  by_contra hxy
  have hne_r : ∀ z, G.Adj h z → z ≠ r := fun z hz hzr => hadj (hzr ▸ hz)
  have hab : c x ≠ c y := fun h' => hxy (huy x hx h')
  have hxh : c h ≠ c x := hc h x hx hhr (hne_r x hx)
  have hyh : c h ≠ c y := hc h y hy hhr (hne_r y hy)
  let xs : G.neighborSet h := ⟨x, hx⟩
  let ys : G.neighborSet h := ⟨y, hy⟩
  let S : Finset (G.neighborSet h) := Finset.univ.filter (fun z => z.val ≠ x ∧ z.val ≠ y)
  have hcolour : ∀ z ∈ S, c z.val ≠ c h ∧ c z.val ≠ c x ∧ c z.val ≠ c y := by
    intro z hz
    have hz' := (Finset.mem_filter.1 hz).2
    refine ⟨fun e => hc h z.val z.property hhr (hne_r _ z.property) e.symm, ?_, ?_⟩
    · exact fun e => hz'.1 (hux z.val z.property e)
    · exact fun e => hz'.2 (huy z.val z.property e)
  have hS : ∀ z ∈ S, R.neighborRotation h z ∉ S := by
    intro z hz hz2
    have hzz := R.neighbor_rotation_adj hfaces h z
    have hneq := hc _ _ hzz (hne_r _ z.property) (hne_r _ (R.neighborRotation h z).property)
    obtain ⟨a1, a2, a3⟩ := hcolour z hz
    obtain ⟨b1, b2, b3⟩ := hcolour _ hz2
    exact hneq (fin4_eq_of_avoid (c h) (c x) (c y) _ _ hxh hyh hab a1 a2 a3 b1 b2 b3)
  have hcard : S.card = G.degree h - 2 := by
    have hS' : S = (Finset.univ \ {xs, ys}) := by
      ext z
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton, xs, ys]
      constructor
      · rintro ⟨h1, h2⟩ (h3 | h3) <;> simp_all
      · intro h3
        exact ⟨fun e => h3 (Or.inl (Subtype.ext e)), fun e => h3 (Or.inr (Subtype.ext e))⟩
    have hpair : ({xs, ys} : Finset (G.neighborSet h)).card = 2 :=
      Finset.card_pair (fun e => hxy (congrArg Subtype.val e))
    rw [hS', Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      card_neighborSet_eq_degree, hpair]
  have hbound := R.two_mul_card_le_degree h S hS
  omega

end SimpleGraph.RotationSystem
