module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin

set_option synthInstance.maxSize 1000

@[expose] public section
namespace SimpleGraph.BeltOpeningWords

abbrev Word := Fin 4 × Fin 4 × Fin 4 × Fin 4

/-- Local inequalities for the unequal-pole link (0,p,q,r,s). -/
def ProperWord (p q r s : Fin 4) : Prop :=
  p ≠ 0 ∧ s ≠ 0 ∧ q ≠ 1 ∧ r ≠ 1 ∧ p ≠ q ∧ q ≠ r ∧ r ≠ s

def UnfilledWord (p q r s : Fin 4) : Prop :=
  ∀ x : Fin 4, x = 0 ∨ x = p ∨ x = q ∨ x = r ∨ x = s

/-- O1 and its reflections, O2, and the eight doubled-zero words. -/
def openings : List Word :=
  [(1,2,3,2),(1,3,2,3),(2,3,2,1),(3,2,3,1),
   (1,2,3,1),(1,3,2,1),
   (1,2,0,3),(1,3,0,2),(3,0,2,1),(2,0,3,1),
   (3,2,0,1),(2,3,0,1),(1,0,2,3),(1,0,3,2)]

/-- Kernel evaluation of all 256 local words; no graph census. -/
theorem classification : ∀ p q r s : Fin 4,
    (ProperWord p q r s ∧ UnfilledWord p q r s) ↔ (p,q,r,s) ∈ openings := by
  unfold ProperWord UnfilledWord openings
  decide

end SimpleGraph.BeltOpeningWords
