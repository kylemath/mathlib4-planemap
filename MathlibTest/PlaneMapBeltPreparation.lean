module

import Mathlib.Combinatorics.SimpleGraph.PlaneMap.VacancyPotential
import Mathlib.Combinatorics.SimpleGraph.PlaneMap.BeltOpeningWords

/--
info: 'SimpleGraph.VacancyPotential.budget' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SimpleGraph.VacancyPotential.budget
/--
info: 'SimpleGraph.BeltOpeningWords.classification' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SimpleGraph.BeltOpeningWords.classification
#print SimpleGraph.VacancyPotential.budget
#print SimpleGraph.BeltOpeningWords.classification
