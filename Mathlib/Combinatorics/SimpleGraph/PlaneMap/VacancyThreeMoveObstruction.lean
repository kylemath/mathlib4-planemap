module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyShortFill

@[expose] public section
namespace SimpleGraph.VacancyThreeMoveObstruction
open VacancySlide VacancyShortFill
variable {V C : Type*} [DecidableEq V] [DecidableEq C] (G : SimpleGraph V)

omit [DecidableEq V] in
lemma prepend_kempe {h : V} {c d : V → C} {bound : Nat}
    (step : KempeStep G h c d) (rest : PureFill G h d bound) :
    PureFill G h c (bound+1) := by
  obtain ⟨k,hk,e,path,target⟩ := rest
  exact ⟨k+1,by omega,e,.cons step path,target⟩

/-- Any target-reaching three-move path with a Kempe first move has a pure
replacement of length at most three. -/
lemma kempe_prefix {h : V} {c d : V → C} {t : V × (V → C)}
    (hc : ProperOff G h c) (step : KempeStep G h c d)
    (tail : MixedPath G 2 (h,d) t) (filled : Target G t.1 t.2) :
    PureFill G h c 3 := by
  exact prepend_kempe G step (short_fill G (kempe_proper G hc step) (by decide) tail filled)

/-- L3(a): if no three-swap fill exists, every three-move mixed fill starts
with an actual singleton slide. No shortest-path encoding is assumed. -/
theorem first_is_slide {h : V} {c : V → C} {t : V × (V → C)}
    (hc : ProperOff G h c) (no_pure : ¬ PureFill G h c 3)
    (path : MixedPath G 3 (h,c) t) (filled : Target G t.1 t.2) :
    ∃ u, G.Adj h u ∧ UniqueAt G h u c ∧
      MixedPath G 2 (u,slide h u c) t := by
  cases path with
  | cons first tail =>
    cases first with
    | kempe step => exact False.elim (no_pure (kempe_prefix G hc step tail filled))
    | slide adj unique => exact ⟨_,adj,unique,tail⟩

/-- An avoiding-colour swap after a slide commutes before it. If one more
swap fills, M3 converts the remaining two mixed moves, yielding three swaps. -/
lemma avoiding_pair_three {h u : V} {c d : V → C} {a b : C} {S : Set V}
    (hc : ProperOff G h c) (adj : G.Adj h u) (unique : UniqueAt G h u c)
    (hab : a ≠ b) (whole : Whole G u (slide h u c) a b S)
    (ha : c u ≠ a) (hb : c u ≠ b)
    (second : KempeStep G u (swap (slide h u c) a b S) d)
    (filled : Target G u d) : PureFill G h c 3 := by
  have hgraph := pairGraph_slide_eq G (h := h) ha hb
  have original : Whole G h c a b S := by
    obtain ⟨s,hs,hm⟩ := whole
    refine ⟨s,(active_slide_eq ha hb s).mpr hs,?_⟩
    intro v; rw [hgraph]; exact hm v
  have first : KempeStep G h c (swap c a b S) := ⟨a,b,S,hab,original,rfl⟩
  have proper := properOff_swap G hc original
  have unique' : UniqueAt G h u (swap c a b S) := by
    intro v edge eq
    rw [swap_other ha hb] at eq
    exact unique edge ((swap_preserves_eq ha hb v).mp eq)
  rw [swap_slide_commute G ha hb whole] at second
  exact prepend_kempe G first (slide_kempe G proper adj unique' second filled)

/-- L3(b): a two-swap finish after the initial slide must first use a pair
containing the slid colour, whenever a three-swap fill is impossible. -/
theorem first_pair_contains_slide_colour {h u : V} {c d : V → C}
    {a b : C} {S : Set V} (hc : ProperOff G h c)
    (no_pure : ¬ PureFill G h c 3) (adj : G.Adj h u) (unique : UniqueAt G h u c)
    (hab : a ≠ b) (whole : Whole G u (slide h u c) a b S)
    (second : KempeStep G u (swap (slide h u c) a b S) d)
    (filled : Target G u d) : c u = a ∨ c u = b := by
  by_cases ha : c u = a
  · exact Or.inl ha
  · by_cases hb : c u = b
    · exact Or.inr hb
    · exact False.elim (no_pure (avoiding_pair_three G hc adj unique hab whole ha hb second filled))

end SimpleGraph.VacancyThreeMoveObstruction
