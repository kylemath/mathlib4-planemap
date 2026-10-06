module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.TwoPoleBelt
public import Mathlib.Tactic

@[expose] public section
namespace SimpleGraph.TwoPoleBeltCaps
open VacancySlide TwoPoleBelt TwoPoleBelt.Vertex

lemma bounded_cast_injective {n a b : Nat} (ha : a < n) (hb : b < n)
    (h : (a : ZMod n) = (b : ZMod n)) : a = b := by
  have e := (ZMod.natCast_eq_natCast_iff' a b n).mp h
  simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using e

lemma d_prelast_impossible {n : Nat} (hn : 5 ≤ n) (c : Vertex n → Colour)
    (hc : ProperOff (graph n) (u ((n-3 : Nat) : ZMod n)) c)
    (hleft : c (u ((n-2 : Nat) : ZMod n)) = 1)
    (hright : c (u ((n-1 : Nat) : ZMod n)) = 1) : False := by
  have step : ((n-2 : Nat) : ZMod n)+1 = ((n-1 : Nat) : ZMod n) := by
    have e : n-2+1=n-1 := by omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : Nat => (k : ZMod n)) e
  have adj : (graph n).Adj (u ((n-2 : Nat) : ZMod n)) (u ((n-1 : Nat) : ZMod n)) := by
    apply (adj_u hn _ _).mpr
    right; left; rw [step]
  have left_ne : (u ((n-2 : Nat) : ZMod n) : Vertex n) ≠ u ((n-3 : Nat) : ZMod n) := by
    intro e
    have eq := bounded_cast_injective (by omega : n-2<n) (by omega : n-3<n) (Vertex.u.inj e)
    omega
  have right_ne : (u ((n-1 : Nat) : ZMod n) : Vertex n) ≠ u ((n-3 : Nat) : ZMod n) := by
    intro e
    have eq := bounded_cast_injective (by omega : n-1<n) (by omega : n-3<n) (Vertex.u.inj e)
    omega
  exact hc adj left_ne right_ne (hleft.trans hright.symm)

/-- An actual D-return leaves the last input column unchanged before the cap. -/
lemma d_return_preserves_last {n i : Nat} (hn : 5 ≤ n) (hi : i ≤ n-4)
    (c : Vertex n → Colour) :
    let j : ZMod n := i
    let d := slide (v (j+1)) (u (j+2)) (slide (v j) (v (j+1)) (slide (u j) (v j) c))
    d (u ((n-1 : Nat) : ZMod n)) = c (u ((n-1 : Nat) : ZMod n)) ∧
    d (v ((n-1 : Nat) : ZMod n)) = c (v ((n-1 : Nat) : ZMod n)) := by
  have neq : ((n-1 : Nat) : ZMod n) ≠ (i : ZMod n) := by
    intro e
    have eq := bounded_cast_injective (by omega : n-1<n) (by omega : i<n) e
    omega
  have neqnext : ((n-1 : Nat) : ZMod n) ≠ (i : ZMod n)+1 := by
    intro e
    have cast : (i : ZMod n)+1 = ((i+1 : Nat) : ZMod n) := by simp
    rw [cast] at e
    have eq := bounded_cast_injective (by omega : n-1<n) (by omega : i+1<n) e
    omega
  dsimp
  constructor <;> simp [slide,neq,neqnext]

/-- The long S cap contradicts properness on the actual upper-ring edge. -/
lemma z_long_cap_impossible {n : Nat} (hn : 5 ≤ n) (c : Vertex n → Colour)
    (hc : ProperOff (graph n) (v (2 : ZMod n)) c) (rho : Colour)
    (h2 : c (u (2 : ZMod n)) = rho) (h3 : c (u (3 : ZMod n)) = rho) : False := by
  have adj : (graph n).Adj (u (2 : ZMod n)) (u (3 : ZMod n)) := by
    apply (adj_u hn _ _).mpr
    right; left; congr 1; ring
  exact hc adj (by simp) (by simp) (h2.trans h3.symm)

end SimpleGraph.TwoPoleBeltCaps
