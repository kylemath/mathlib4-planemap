/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic.Push

/-!
# Graph-theoretic Kempe swaps and five-colour extension

Ported from the local GraphColour KempeReconfiguration package (Basic,
Degree4Extend, and FiveColor), keeping its Lean 4.15 source unchanged.
Only the swap and extension lemmas needed by PlaneMap are included.
These lemmas are independent of PlaneMap.
-/

@[expose] public section
namespace SimpleGraph.Kempe

variable {V : Type*}
variable {k : ℕ}

/-- A proper k-colouring assigns each vertex a colour in Fin k such that
    adjacent vertices get different colours. -/
def IsProperColouring (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- The bichromatic subgraph B_{a,b}(G,c): the subgraph of G induced by
    vertices coloured a or b. Two such vertices are adjacent in B_{a,b}
    iff they are adjacent in G. -/
def bichromaticAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (u v : V) : Prop :=
  G.Adj u v ∧ (c u = a ∨ c u = b) ∧ (c v = a ∨ c v = b)

/-- Keep the edges between the two selected colours; all other vertices are isolated. -/
def bichromaticSubgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) : SimpleGraph V where
  Adj u v := bichromaticAdj G c a b u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- A Kempe chain is a set of vertices forming a connected component
    of the bichromatic subgraph B_{a,b}(G,c). We represent it as
    the connected component containing a given vertex. -/
def inSameKempeChain (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (u v : V) : Prop :=
  (bichromaticSubgraph G c a b).Reachable u v

/-- Kempe swap: exchange colours a ↔ b on all vertices in a set S. -/
def kempeSwap (c : V → Fin k) (S : Set V) [DecidablePred (· ∈ S)]
    (a b : Fin k) : V → Fin k :=
  fun v =>
    if v ∈ S then
      if c v = a then b
      else if c v = b then a
      else c v
    else c v

/-- Key property: Kempe swap only modifies colours within {a, b}. -/
theorem kempeSwap_colour_cases (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b : Fin k) (v : V) :
    kempeSwap c S a b v = a ∨ kempeSwap c S a b v = b ∨
    kempeSwap c S a b v = c v := by
  by_cases hv : v ∈ S
  · by_cases ha : c v = a
    · simp [kempeSwap, hv, ha]
    · by_cases hb : c v = b
      · simp [kempeSwap, hv, ha, hb]
      · simp [kempeSwap, hv, ha, hb]
  · simp [kempeSwap, hv]

/-- If a colour is not in {a, b}, Kempe swap doesn't change it. -/
theorem kempeSwap_preserves_other (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b : Fin k) (v : V)
    (hva : c v ≠ a) (hvb : c v ≠ b) :
    kempeSwap c S a b v = c v := by
  by_cases hv : v ∈ S
  · simp [kempeSwap, hv, hva, hvb]
  · simp [kempeSwap, hv]

/-- Vertices outside the swap set keep their colour. -/
theorem kempeSwap_outside (c : V → Fin k) (S : Set V)
    [DecidablePred (· ∈ S)] (a b : Fin k) (v : V)
    (hv : v ∉ S) :
    kempeSwap c S a b v = c v := by
  simp only [kempeSwap, ite_eq_right hv]

/-- Kempe swap on a Kempe chain preserves proper colouring.

    The key insight: within the chain, adjacent vertices have opposite
    colours (one a, one b), so swapping preserves this opposition.
    Across the chain boundary, the exterior vertex keeps its original
    colour and the boundary vertex switches, but they were in {a,b}
    and the exterior vertex is NOT in {a,b} (by definition of bichromatic
    subgraph), so they remain properly coloured. -/
theorem kempeSwap_preserves_proper
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (hab : a ≠ b)
    (S : Set V) [DecidablePred (· ∈ S)]
    (hS_ab : ∀ v ∈ S, c v = a ∨ c v = b)
    (hS_closed : ∀ u v : V, G.Adj u v → u ∈ S → (c v = a ∨ c v = b) → v ∈ S)
    (hproper : IsProperColouring G c) :
    IsProperColouring G (kempeSwap c S a b) := by
  intro u v huv
  simp only [kempeSwap]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
  · -- Both in S: they had opposite colours in {a,b}, swap preserves this
    have hcu := hS_ab u hu
    have hcv := hS_ab v hv
    have hne := hproper u v huv
    rcases hcu with hcu | hcu <;> rcases hcv with hcv | hcv
    · exact absurd (hcu.trans hcv.symm) hne
    · -- u has colour a and becomes b; v has colour b and becomes a.
      simp [hu, hv, hcu, hcv, Ne.symm hab]
    · simp [hu, hv, hcu, hcv]
      exact ⟨Ne.symm hab, hab⟩
    · exact absurd (hcu.trans hcv.symm) hne
  · -- u in S, v not: v's colour is not in {a,b} (since S is closed)
    have hcv_not : ¬(c v = a ∨ c v = b) := fun h => hv (hS_closed u v huv hu h)
    push Not at hcv_not
    simp [ite_eq_right hv]
    have hcu := hS_ab u hu
    rcases hcu with hcu | hcu
    · simp [hu, hv, hcu]
      exact Ne.symm hcv_not.2
    · simp [hu, hv, hcu, Ne.symm hab]
      exact Ne.symm hcv_not.1
  · -- u not in S, v in S: symmetric to previous case
    have hcu_not : ¬(c u = a ∨ c u = b) :=
      fun h => hu (hS_closed v u huv.symm hv h)
    push Not at hcu_not
    simp [ite_eq_right hu]
    have hcv := hS_ab v hv
    rcases hcv with hcv | hcv
    · simp [hu, hv, hcv]
      exact hcu_not.2
    · simp [hu, hv, hcv, Ne.symm hab]
      exact hcu_not.1
  · -- Neither in S: both keep original colours
    simp [ite_eq_right hu, ite_eq_right hv]
    exact hproper u v huv


noncomputable section

/-- The (a,b)-Kempe chain of `u`: the reachable component of `u` in the
bichromatic subgraph `B_{a,b}(G,c)`. -/
abbrev kempeChain (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (u : V) : Set V :=
  {v | (bichromaticSubgraph G c a b).Reachable u v}

instance kempeChain_decidablePred
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (u : V) :
    DecidablePred (fun v => v ∈ kempeChain G c a b u) :=
  fun v => Classical.propDecidable (v ∈ kempeChain G c a b u)

lemma walk_colours_ab
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) {u v : V}
    (p : (bichromaticSubgraph G c a b).Walk u v) :
    c u = a ∨ c u = b → c v = a ∨ c v = b := by
  induction p with
  | nil =>
      intro hu
      exact hu
  | cons h _ ih =>
      intro _
      exact ih h.2.2

lemma reachable_colours_ab
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) {u v : V}
    (h : (bichromaticSubgraph G c a b).Reachable u v)
    (hu : c u = a ∨ c u = b) :
    c v = a ∨ c v = b := by
  rcases h with ⟨p⟩
  exact walk_colours_ab G c a b p hu

lemma mem_kempeChain_self
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (u : V) :
    u ∈ kempeChain G c a b u :=
  SimpleGraph.Reachable.refl u

lemma kempeChain_colours
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (x v : V)
    (hx : c x = a ∨ c x = b)
    (hv : v ∈ kempeChain G c a b x) :
    c v = a ∨ c v = b :=
  reachable_colours_ab G c a b hv hx

/-- An (a,b)-chain is closed under edges of G that land on an {a,b}-vertex.
This is the saturation hypothesis of `kempeSwap_preserves_proper`. -/
lemma kempeChain_closed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (x u v : V)
    (hx : c x = a ∨ c x = b)
    (huv : G.Adj u v)
    (hu : u ∈ kempeChain G c a b x)
    (hvcol : c v = a ∨ c v = b) :
    v ∈ kempeChain G c a b x := by
  have hcu : c u = a ∨ c u = b := kempeChain_colours G c a b x u hx hu
  exact SimpleGraph.Reachable.trans hu
    ⟨SimpleGraph.Walk.cons ⟨huv, hcu, hvcol⟩ SimpleGraph.Walk.nil⟩

lemma adjacent_ab_same_chain
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (x y : V)
    (hxy : G.Adj x y) (hx : c x = a) (hy : c y = b) :
    inSameKempeChain G c a b x y :=
  ⟨SimpleGraph.Walk.cons ⟨hxy, Or.inl hx, Or.inr hy⟩ SimpleGraph.Walk.nil⟩

/-- If the (a,b)-chain of `x` misses `y`, then `x` and `y` are not adjacent.
In particular a chain-separated pair of neighbours is a non-adjacent pair. -/
lemma separated_chain_not_adj
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (x y : V)
    (hx : c x = a) (hy : c y = b)
    (hsep : ¬ inSameKempeChain G c a b x y) :
    ¬ G.Adj x y := by
  intro hxy
  exact hsep (adjacent_ab_same_chain G c a b x y hxy hx hy)

theorem kempeSwap_chain_proper
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin k) (a b : Fin k) (hab : a ≠ b) (x : V)
    (hx : c x = a)
    (hproper : IsProperColouring G c) :
    IsProperColouring G (kempeSwap c (kempeChain G c a b x) a b) :=
  kempeSwap_preserves_proper G c a b hab (kempeChain G c a b x)
    (fun v hv => kempeChain_colours G c a b x v (Or.inl hx) hv)
    (fun u v huv hu hvcol => kempeChain_closed G c a b x u v (Or.inl hx) huv hu hvcol)
    hproper

lemma kempeSwap_flips_a
    (c : V → Fin k) (S : Set V) [DecidablePred (· ∈ S)]
    (a b : Fin k) (x : V) (hxS : x ∈ S) (hx : c x = a) :
    kempeSwap c S a b x = b := by
  simp [kempeSwap, hxS, hx]

lemma kempeSwap_exchanges_b
    (c : V → Fin k) (S : Set V) [DecidablePred (· ∈ S)]
    (a b : Fin k) (hab : a ≠ b) (y : V)
    (hyS : y ∈ S) (hy : c y = b) :
    kempeSwap c S a b y = a := by
  have hya : c y ≠ a := by
    intro h
    exact hab (h.symm.trans hy)
  simp [kempeSwap, hyS, hy, hya]

/-- A subset of `Fin 5` of size at most 4 omits a colour. This is the
pigeonhole fact used when at most four colours appear on a finite set. -/
theorem exists_missing_colour {s : Finset (Fin 5)} (hs : s.card ≤ 4) :
    ∃ α : Fin 5, α ∉ s := by
  by_contra h
  have hall : ∀ col : Fin 5, col ∈ s := by
    intro col
    by_contra hnin
    exact h ⟨col, hnin⟩
  have hsub : (Finset.univ : Finset (Fin 5)) ⊆ s := fun col _ => hall col
  have hle : 5 ≤ s.card := by
    have hcard := Finset.card_le_card hsub
    simpa [Finset.card_univ, Fintype.card_fin] using hcard
  exact Nat.not_le_of_lt (Nat.lt_succ_of_le hs) hle

/-- At most four colours on the image of a finite set leaves a free colour. -/
theorem exists_missing_colour_on {α : Type*} [DecidableEq α]
    (f : α → Fin 5) (s : Finset α) (hs : (s.image f).card ≤ 4) :
    ∃ col : Fin 5, ∀ a ∈ s, f a ≠ col := by
  obtain ⟨col, hcol⟩ := exists_missing_colour hs
  refine ⟨col, fun a ha hf => ?_⟩
  exact hcol (Finset.mem_image.mpr ⟨a, ha, hf⟩)

variable [Fintype V] [DecidableEq V]

/-- Colours appearing on `N(x)` under `c`. This Finset is `c '' neighborSet x`. -/
def neighbourColourFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (c : V → Fin 5) : Finset (Fin 5) :=
  (G.neighborFinset x).image c

lemma coe_neighbourColourFinset
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (c : V → Fin 5) :
    (neighbourColourFinset G x c : Set (Fin 5)) = c '' G.neighborSet x := by
  ext col
  simp [neighbourColourFinset, Finset.mem_image, mem_neighborFinset, Set.mem_image,
    mem_neighborSet]

lemma neighbourColourFinset_card_le_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (c : V → Fin 5) :
    (neighbourColourFinset G x c).card ≤ G.degree x :=
  Finset.card_image_le

lemma neighbourColourFinset_card_le_of_degree_le_four
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (c : V → Fin 5)
    (hdeg : G.degree x ≤ 4) :
    (neighbourColourFinset G x c).card ≤ 4 :=
  Nat.le_trans (neighbourColourFinset_card_le_degree G x c) hdeg

/-- Properness of `c` on `G - x` as an induced subgraph is properness of every
edge that misses `x`. -/
theorem isProperColouring_induce_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (c : V → Fin 5) :
    IsProperColouring (G.induce {v | v ≠ x}) (fun y : {v : V // v ≠ x} => c y.val) ↔
      ∀ u v : V, G.Adj u v → u ≠ x → v ≠ x → c u ≠ c v := by
  constructor
  · intro h u v huv hu hv
    exact h ⟨u, hu⟩ ⟨v, hv⟩ huv
  · intro h u v huv
    exact h u.val v.val huv u.property v.property

/-- If `c` is a proper `Fin 5` colouring of the induced subgraph `G - x`, and
either `deg(x) ≤ 4` or at most four colours appear on `N(x)`, then `c`
extends to a proper 5-colouring of `G` that agrees with `c` off `x`. -/
theorem five_color_degree_at_most_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (c : V → Fin 5)
    (hproper : IsProperColouring (G.induce {v | v ≠ x})
      (fun y : {v : V // v ≠ x} => c y.val))
    (hbound : G.degree x ≤ 4 ∨ ((G.neighborFinset x).image c).card ≤ 4) :
    ∃ c' : V → Fin 5, IsProperColouring G c' ∧ ∀ v : V, v ≠ x → c' v = c v := by
  have hused : ((G.neighborFinset x).image c).card ≤ 4 := by
    cases hbound with
    | inl hdeg =>
        simpa [neighbourColourFinset] using
          neighbourColourFinset_card_le_of_degree_le_four G x c hdeg
    | inr hcard =>
        exact hcard
  obtain ⟨α, hα⟩ := exists_missing_colour hused
  refine ⟨fun v => if v = x then α else c v, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u = x
    · have hvx : v ≠ x := hu ▸ (G.ne_of_adj huv).symm
      have hmem : v ∈ G.neighborFinset x := by
        rw [mem_neighborFinset, ← hu]
        exact huv
      have hnc : c v ≠ α := by
        intro hcv
        exact hα (Finset.mem_image.mpr ⟨v, hmem, hcv⟩)
      simp [hu, hvx]
      exact Ne.symm hnc
    · by_cases hv : v = x
      · have hmem : u ∈ G.neighborFinset x := by
          rw [mem_neighborFinset, ← hv]
          exact huv.symm
        have hnc : c u ≠ α := by
          intro hcu
          exact hα (Finset.mem_image.mpr ⟨u, hmem, hcu⟩)
        simp [hu, hv]
        exact hnc
      · simp [hu, hv]
        exact (isProperColouring_induce_iff G x c).mp hproper u v huv hu hv
  · intro v hv
    simp [hv]

/-- Same extension, stated from a colouring of the deleted-vertex type. -/
theorem five_color_degree_at_most_four_subtype
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (c : {v : V // v ≠ x} → Fin 5)
    (hproper : IsProperColouring (G.induce {v | v ≠ x}) c)
    (hbound : G.degree x ≤ 4 ∨
      ((G.neighborFinset x).image fun y =>
        if h : y = x then (0 : Fin 5) else c ⟨y, h⟩).card ≤ 4) :
    ∃ c' : V → Fin 5, IsProperColouring G c' ∧
      ∀ v : V, (hv : v ≠ x) → c' v = c ⟨v, hv⟩ := by
  let cV : V → Fin 5 := fun y => if h : y = x then 0 else c ⟨y, h⟩
  have hproperV :
      IsProperColouring (G.induce {v | v ≠ x})
        (fun y : {v : V // v ≠ x} => cV y.val) := by
    intro u v huv
    have hu : u.val ≠ x := u.property
    have hv : v.val ≠ x := v.property
    have : cV u.val = c u := dite_eq_right hu
    have : cV v.val = c v := dite_eq_right hv
    simpa [cV, hu, hv] using hproper u v huv
  have hboundV : G.degree x ≤ 4 ∨ ((G.neighborFinset x).image cV).card ≤ 4 := by
    simpa [cV] using hbound
  obtain ⟨c', hc', hag⟩ := five_color_degree_at_most_four G x cV hproperV hboundV
  refine ⟨c', hc', fun v hv => ?_⟩
  simpa [cV, hv] using hag v hv

/-- Graphs on at most five vertices are 5-colourable: inject the vertices
into `Fin 5`. Planarity is not used. -/
theorem five_colorable_of_card_le_five
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V ≤ 5) :
    ∃ c : V → Fin 5, IsProperColouring G c := by
  let e := Fintype.equivFin V
  refine ⟨fun v => Fin.castLE hV (e v), fun u v huv => ?_⟩
  exact (Fin.castLE_injective hV).ne (e.injective.ne (G.ne_of_adj huv))


end
end SimpleGraph.Kempe
