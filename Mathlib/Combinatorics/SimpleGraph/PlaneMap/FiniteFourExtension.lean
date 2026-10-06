/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.FourColorExtension
public import Mathlib.Combinatorics.SimpleGraph.Coloring.FiniteReachability

/-! # Executable four-colour extension from finite separation certificates

Graph adjacency and rotation are explicit input data. Component search, the
choice between opposite pairs, and cyclic neighbour enumeration are executable.
Producing a complete deletion certificate remains a separate obligation.
-/

@[expose] public section
namespace SimpleGraph.SphericalMap
variable {n : ℕ} (M : SphericalMap n) [DecidableRel M.graph.Adj]

/-- Compute the finite component and extend across a pair of uniquely coloured
neighbours which the supplied certificate separates. -/
def finiteFourColorSwapPair (x : Fin n) (c : Fin n → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (e : Fin 4 ≃ M.graph.neighborSet x)
    (hinj : Function.Injective (fun i => c (e i).val))
    (i j : Fin 4) (hij : i ≠ j)
    (hsep : ¬ (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
      (fun z => c z.val) (c (e i).val) (c (e j).val)).Reachable
        ⟨(e i).val, (e i).property.ne.symm⟩
        ⟨(e j).val, (e j).property.ne.symm⟩) : M.graph.Coloring (Fin 4) := by
  let H := M.graph.induce {z | z ≠ x}
  let cH : {z : Fin n // z ≠ x} → Fin 4 := fun z => c z.val
  let B := Kempe.bichromaticSubgraph H cH (c (e i).val) (c (e j).val)
  let u : {z : Fin n // z ≠ x} := ⟨(e i).val, (e i).property.ne.symm⟩
  let v : {z : Fin n // z ≠ x} := ⟨(e j).val, (e j).property.ne.symm⟩
  let S := FiniteReachability.component B u
  apply fourColorSwapSet x c hproper e hinj i j hij S
  · intro z hz
    exact Kempe.reachable_colours_ab H cH _ _
      ((FiniteReachability.mem_component_iff B u z).mp hz) (Or.inl rfl)
  · intro a b hab ha hb
    apply (FiniteReachability.mem_component_iff B u b).mpr
    exact ((FiniteReachability.mem_component_iff B u a).mp ha).trans
      (show B.Adj a b from ⟨hab,
        Kempe.reachable_colours_ab H cH _ _
          ((FiniteReachability.mem_component_iff B u a).mp ha) (Or.inl rfl), hb⟩).reachable
  · exact (FiniteReachability.mem_component_iff B u u).mpr (.refl _)
  · exact fun hv => hsep ((FiniteReachability.mem_component_iff B u v).mp hv)

/-- A finite scan chooses a missing neighbour colour. The nonemptiness
certificate is proof data; the chosen colour is computed by `Finset.min'`. -/
def finiteFourColorMissing (x : Fin n) (c : Fin n → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (hmissing : ((Finset.univ : Finset (Fin 4)).filter
      (fun a => ∀ z : Fin n, M.Adj x z → c z ≠ a)).Nonempty) :
    M.graph.Coloring (Fin 4) := by
  let S := (Finset.univ : Finset (Fin 4)).filter
    (fun a => ∀ z : Fin n, M.Adj x z → c z ≠ a)
  let a := S.min' hmissing
  have ha : a ∈ S := Finset.min'_mem S hmissing
  apply fourColorExtendMissing x (fun z => c z.val) hproper a
  intro z hz
  exact (Finset.mem_filter.mp ha).2 z.val hz

/-- One finite reachability test chooses a separated opposite pair. The
certificate rules out simultaneous opposite connections; it must be supplied
from spherical separation, never assumed for arbitrary 4-degenerate graphs. -/
def finiteFourColorOpposite (x : Fin n) (c : Fin n → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (e : Fin 4 ≃ M.graph.neighborSet x)
    (hinj : Function.Injective (fun i => c (e i).val))
    (hseparation :
      (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
        (fun z => c z.val) (c (e 0).val) (c (e 2).val)).Reachable
          ⟨(e 0).val, (e 0).property.ne.symm⟩
          ⟨(e 2).val, (e 2).property.ne.symm⟩ →
      ¬ (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
        (fun z => c z.val) (c (e 1).val) (c (e 3).val)).Reachable
          ⟨(e 1).val, (e 1).property.ne.symm⟩
          ⟨(e 3).val, (e 3).property.ne.symm⟩) : M.graph.Coloring (Fin 4) := by
  let B := Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
    (fun z => c z.val) (c (e 0).val) (c (e 2).val)
  let u : {z : Fin n // z ≠ x} := ⟨(e 0).val, (e 0).property.ne.symm⟩
  let v : {z : Fin n // z ≠ x} := ⟨(e 2).val, (e 2).property.ne.symm⟩
  if hv : v ∈ FiniteReachability.component B u then
    exact finiteFourColorSwapPair M x c hproper e hinj 1 3 (by decide)
      (hseparation ((FiniteReachability.mem_component_iff B u v).mp hv))
  else
    exact finiteFourColorSwapPair M x c hproper e hinj 0 2 (by decide)
      (fun hr => hv ((FiniteReachability.mem_component_iff B u v).mpr hr))

theorem finite_reachable_away (x : Fin n) (c : Fin n → Fin 4) (a b : Fin 4)
    {u v : {z : Fin n // z ≠ x}}
    (hu : c u.val = a ∨ c u.val = b) (hv : c v.val = a ∨ c v.val = b)
    (h : (Kempe.bichromaticSubgraph (M.graph.induce {z | z ≠ x})
      (fun z => c z.val) a b).Reachable u v) :
    (M.graph.induce {z | z ≠ x ∧ (c z = a ∨ c z = b)}).Reachable
      ⟨u.val, u.property, hu⟩ ⟨v.val, v.property, hv⟩ := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons u v w h p ih =>
    obtain ⟨q⟩ := ih h.2.2 hv
    refine ⟨.cons (v := ⟨v.val, v.property, h.2.2⟩) ?_ q⟩
    exact h.1

/-- The complete executable distinct-colour degree-four step, with a cyclic
neighbour enumeration supplied as data. Spherical separation is proved from
`M`; the implementation searches components and returns a proper colouring. -/
def finiteFourColorCyclic (x : Fin n) (c : Fin n → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (e : Fin 4 ≃ M.graph.neighborSet x)
    (hinj : Function.Injective (fun i => c (e i).val))
    (hrot : ∀ i : Fin 4,
      M.rotation.next (M.graph.dartOfNeighborSet x (e i)) =
        M.graph.dartOfNeighborSet x (e (i + 1))) : M.graph.Coloring (Fin 4) := by
  apply finiteFourColorOpposite M x c hproper e hinj
  intro h02 h13
  exact four_colour_hopposite c x (fun i => (e i).val)
    (fun i => (e i).property) hrot hinj
    (finite_reachable_away M x c (c (e 0).val) (c (e 2).val) (Or.inl rfl) (Or.inr rfl) h02)
    (finite_reachable_away M x c (c (e 1).val) (c (e 3).val) (Or.inl rfl) (Or.inr rfl) h13)

/-- Executable extension at every vertex of degree at most four. The only
additional data input is a procedure supplying the cyclic enumeration in the
exactly-degree-four case. Existence of this enumeration alone does not supply
an executable procedure. -/
def finiteFourColorExtension (x : Fin n) (hdeg : M.graph.degree x ≤ 4)
    (c : Fin n → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val))
    (enumerate : M.graph.degree x = 4 → Fin 4 ≃ M.graph.neighborSet x)
    (hrot : ∀ hd : M.graph.degree x = 4, ∀ i : Fin 4,
      M.rotation.next (M.graph.dartOfNeighborSet x (enumerate hd i)) =
        M.graph.dartOfNeighborSet x (enumerate hd (i + 1))) :
    M.graph.Coloring (Fin 4) := by
  let S := (Finset.univ : Finset (Fin 4)).filter
    (fun a => ∀ z : Fin n, M.Adj x z → c z ≠ a)
  if hm : S.Nonempty then
    exact finiteFourColorMissing M x c hproper hm
  else
    have hlarge : ¬ ((M.graph.neighborFinset x).image c).card ≤ 3 := by
      intro hsmall
      have hlt : ((M.graph.neighborFinset x).image c).card <
          (Finset.univ : Finset (Fin 4)).card := by simpa using (show _ < 4 by omega)
      obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      apply hm
      refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      intro z hz heq
      exact ha (Finset.mem_image.mpr
        ⟨z, by simpa only [mem_neighborFinset] using hz, heq⟩)
    have himage : ((M.graph.neighborFinset x).image c).card ≤ M.graph.degree x :=
      Finset.card_image_le
    have hd : M.graph.degree x = 4 := by omega
    have hcard : ((M.graph.neighborFinset x).image c).card =
        (M.graph.neighborFinset x).card := by rw [card_neighborFinset_eq_degree]; omega
    have hinj : Set.InjOn c (M.graph.neighborSet x) := by
      simpa only [coe_neighborFinset] using Finset.injOn_of_card_image_eq hcard
    have hi : Function.Injective (fun i => c (enumerate hd i).val) := by
      intro i j hij
      exact (enumerate hd).injective (Subtype.ext
        (hinj (enumerate hd i).property (enumerate hd j).property hij))
    exact finiteFourColorCyclic M x c hproper (enumerate hd) hi (hrot hd)

/-- Enumerate the four-tuples in a fixed, executable order. -/
def finiteFourTuples (n : ℕ) : List (Fin 4 → Fin n) :=
  (List.finRange n).flatMap fun a =>
  (List.finRange n).flatMap fun b =>
  (List.finRange n).flatMap fun c =>
  (List.finRange n).map fun d => ![a, b, c, d]

theorem mem_finiteFourTuples (v : Fin 4 → Fin n) : v ∈ finiteFourTuples n := by
  simp only [finiteFourTuples, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and]
  refine ⟨v 0, v 1, v 2, v 3, ?_⟩
  funext i
  fin_cases i <;> rfl

/-- Check a candidate cyclic neighbour tuple using actual rotation data. -/
def IsFiniteFourCycle (x : Fin n) (v : Fin 4 → Fin n) : Prop :=
  if h : ∀ i, M.Adj x (v i) then
    Function.Injective v ∧ ∀ i : Fin 4,
      M.rotation.next ⟨(x, v i), h i⟩ = ⟨(x, v (i + 1)), h (i + 1)⟩
  else False

instance finiteFourCycleDecidable (x : Fin n) (v : Fin 4 → Fin n) :
    Decidable (IsFiniteFourCycle M x v) := by
  unfold IsFiniteFourCycle
  infer_instance

/-- A finite search returns a satisfying value when one occurs in the list.
The default is never used under the proved nonemptiness premise. -/
def finiteFirst {α : Type*} (P : α → Prop) [DecidablePred P]
    (L : List α) (fallback : α) : α := (L.find? (fun a => decide (P a))).getD fallback

theorem finiteFirst_spec {α : Type*} (P : α → Prop) [DecidablePred P]
    (L : List α) (fallback : α) (hex : ∃ a ∈ L, P a) :
    P (finiteFirst P L fallback) := by
  unfold finiteFirst
  cases h : L.find? (fun a => decide (P a)) with
  | none =>
    obtain ⟨a, ha, hp⟩ := hex
    have hn := List.find?_eq_none.mp h a ha
    simp [hp] at hn
  | some a =>
    simpa using List.find?_some h

def finiteCyclicTuple (x : Fin n) : Fin 4 → Fin n :=
  finiteFirst (IsFiniteFourCycle M x) (finiteFourTuples n) (fun _ => x)

theorem finiteCyclicTuple_spec (x : Fin n) (hd : M.graph.degree x = 4) :
    IsFiniteFourCycle M x (finiteCyclicTuple M x) := by
  apply finiteFirst_spec
  obtain ⟨e, he⟩ := degree_four_neighbour_rotation (M := M) x (by
    convert hd using 1
    unfold degree
    congr 1
    ext z
    simp only [mem_neighborFinset])
  refine ⟨fun i => (e i).val, mem_finiteFourTuples _, ?_⟩
  have ha : ∀ i : Fin 4, M.Adj x (e i).val := fun i => (e i).property
  simp only [IsFiniteFourCycle, dite_eq_left ha]
  refine ⟨fun i j hij => e.injective (Subtype.ext hij), he⟩

theorem finiteCyclicTuple_adj (x : Fin n) (hd : M.graph.degree x = 4) :
    ∀ i, M.Adj x (finiteCyclicTuple M x i) := by
  have hs := finiteCyclicTuple_spec M x hd
  by_cases ha : ∀ i, M.Adj x (finiteCyclicTuple M x i)
  · exact ha
  · simp [IsFiniteFourCycle, ha] at hs

def finiteCyclicNeighbor (x : Fin n) (hd : M.graph.degree x = 4)
    (i : Fin 4) : M.graph.neighborSet x :=
  ⟨finiteCyclicTuple M x i, finiteCyclicTuple_adj M x hd i⟩

theorem finiteCyclicNeighbor_bijective (x : Fin n) (hd : M.graph.degree x = 4) :
    Function.Bijective (finiteCyclicNeighbor M x hd) := by
  have hs := finiteCyclicTuple_spec M x hd
  have ha := finiteCyclicTuple_adj M x hd
  simp only [IsFiniteFourCycle, dite_eq_left ha] at hs
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨fun i j hij => hs.1 (congrArg Subtype.val hij), ?_⟩
  simp only [Fintype.card_fin, card_neighborSet_eq_degree, hd]

/-- Compute both directions of the neighbour equivalence. The inverse is a
four-index finite search, rather than `Equiv.ofBijective`'s chosen inverse. -/
def finiteCyclicEnumeration (x : Fin n) (hd : M.graph.degree x = 4) :
    Fin 4 ≃ M.graph.neighborSet x where
  toFun := finiteCyclicNeighbor M x hd
  invFun z := finiteFirst (fun i => finiteCyclicTuple M x i = z.val)
    (List.finRange 4) 0
  left_inv i := by
    apply (finiteCyclicNeighbor_bijective M x hd).1
    apply Subtype.ext
    exact finiteFirst_spec (fun j => finiteCyclicTuple M x j = finiteCyclicTuple M x i)
      (List.finRange 4) 0 ⟨i, List.mem_finRange _, rfl⟩
  right_inv z := by
    apply Subtype.ext
    apply finiteFirst_spec (fun i => finiteCyclicTuple M x i = z.val) (List.finRange 4) 0
    obtain ⟨i, hi⟩ := (finiteCyclicNeighbor_bijective M x hd).2 z
    exact ⟨i, List.mem_finRange _, congrArg Subtype.val hi⟩

theorem finiteCyclicEnumeration_rotation (x : Fin n) (hd : M.graph.degree x = 4)
    (i : Fin 4) :
    M.rotation.next (M.graph.dartOfNeighborSet x (finiteCyclicEnumeration M x hd i)) =
      M.graph.dartOfNeighborSet x (finiteCyclicEnumeration M x hd (i + 1)) := by
  have hs := finiteCyclicTuple_spec M x hd
  have ha := finiteCyclicTuple_adj M x hd
  simp only [IsFiniteFourCycle, dite_eq_left ha] at hs
  exact hs.2 i

/-- An executable degree-at-most-four extension requiring no externally
supplied neighbour enumeration. Graph adjacency and rotation remain input data. -/
def finiteFourColorExtend (x : Fin n) (hd : M.graph.degree x ≤ 4)
    (c : Fin n → Fin 4)
    (hproper : Kempe.IsProperColouring (M.graph.induce {z | z ≠ x})
      (fun z => c z.val)) : M.graph.Coloring (Fin 4) :=
  finiteFourColorExtension M x hd c hproper
    (finiteCyclicEnumeration M x) (finiteCyclicEnumeration_rotation M x)

end SimpleGraph.SphericalMap
