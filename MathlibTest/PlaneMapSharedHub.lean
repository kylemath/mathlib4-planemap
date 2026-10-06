module
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SharedHub

open SimpleGraph

/-- info: 'SimpleGraph.RotationSystem.two_mul_card_le_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RotationSystem.two_mul_card_le_degree
/--
info: 'SimpleGraph.RotationSystem.singleton_colour_neighbour_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RotationSystem.singleton_colour_neighbour_unique

namespace SharedHubRegression

-- Two neighbours of a hub that each carry a singleton colour coincide.
example {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (R : RotationSystem G) (hfaces : ∀ f : R.Face, R.faceLength f = 3)
    (r h : V) (hhr : h ≠ r) (hadj : ¬ G.Adj h r) (hdeg : 5 ≤ G.degree h)
    (c : V → Fin 4) (hc : ∀ u v, G.Adj u v → u ≠ r → v ≠ r → c u ≠ c v)
    {x y : V} (hx : G.Adj h x) (hy : G.Adj h y)
    (hux : ∀ z, G.Adj h z → c z = c x → z = x)
    (huy : ∀ z, G.Adj h z → c z = c y → z = y) : x = y :=
  R.singleton_colour_neighbour_unique hfaces r h hhr hadj hdeg c hc hx hy hux huy

-- The empty set of neighbours trivially satisfies the cycle bound.
example {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (R : RotationSystem G) (h : V) :
    2 * (∅ : Finset (G.neighborSet h)).card ≤ G.degree h :=
  R.two_mul_card_le_degree h ∅ (by simp)

end SharedHubRegression
