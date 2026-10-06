module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyCliqueLift

@[expose] public section
namespace SimpleGraph.VacancyCliqueLift
open VacancySlide VacancyShortFill
variable {V C : Type*} (G : SimpleGraph V)

/-- Actual global moves, carrying the invariant at every intermediate hole. -/
inductive ProtectedPath [DecidableEq V] [DecidableEq C] (A F : Set V) :
    Nat → (V × (V → C)) → (V × (V → C)) → Prop
  | nil {h c} : h ∈ A → h ∉ F → ProtectedPath A F 0 (h,c) (h,c)
  | cons {n s t v} : MixedStep G s t → s.1 ∈ A → s.1 ∉ F →
      ProtectedPath A F n t v → ProtectedPath A F (n+1) s v

lemma ProtectedPath.forget [DecidableEq V] [DecidableEq C] {A F : Set V}
    {n : Nat} {s t : V × (V → C)} (path : ProtectedPath G A F n s t) :
    MixedPath G n s t := by
  induction path with
  | nil _ _ => exact .nil _
  | cons step _ _ _ ih => exact .cons step ih

/-- The global lift retains the all-holes invariant, not merely endpoint agreement. -/
theorem protected_path_lift [DecidableEq V] [DecidableEq C] {A F : Set V}
    (bd : Boundary G A F) (cl : Clique G F) {n : Nat} {s t : V × (V → C)}
    {g : V → C} (path : InteriorPath G A F n s t)
    (eq : ∀ v, v ∈ A → g v = s.2 v) :
    ∃ e, ProtectedPath G A F n (s.1,g) (t.1,e) ∧
      ∀ v, v ∈ A → e v = t.2 v := by
  induction path generalizing g with
  | nil ha hf => exact ⟨g,.nil ha hf,eq⟩
  | @cons n s t v st rest ih =>
    cases st with
    | kempe ha hf step =>
      obtain ⟨next,move,agree⟩ := kempe_lift_agree G bd cl eq step
      obtain ⟨last,rest',agree'⟩ := ih agree
      exact ⟨last,.cons (.kempe move) ha hf rest',agree'⟩
    | slide ha hf ua uf edge unique =>
      obtain ⟨unique',agree⟩ := slide_lift G bd ha hf edge unique eq
      obtain ⟨last,rest',agree'⟩ := ih agree
      exact ⟨last,.cons (.slide edge.1 unique') ha hf rest',agree'⟩

/-- Actual filling path, same length and holes, with the protected boundary avoided. -/
theorem protected_fill_lift [DecidableEq V] [DecidableEq C] {A F : Set V}
    (bd : Boundary G A F) (cl : Clique G F) {n : Nat} {s t : V × (V → C)}
    {g : V → C} (path : InteriorPath G A F n s t)
    (eq : ∀ v, v ∈ A → g v = s.2 v) (proper : ProperOff G s.1 g)
    (filled : Target (sideGraph G A) t.1 t.2) :
    ∃ e, ProtectedPath G A F n (s.1,g) (t.1,e) ∧
      ProperOff G t.1 e ∧ Target G t.1 e := by
  obtain ⟨e,globalPath,agree⟩ := protected_path_lift G bd cl path eq
  obtain ⟨ha,hf⟩ := terminal_interior G path
  exact ⟨e,globalPath,mixed_path_proper G (globalPath.forget G) proper,
    target_lift G bd ha hf agree filled⟩

end SimpleGraph.VacancyCliqueLift
