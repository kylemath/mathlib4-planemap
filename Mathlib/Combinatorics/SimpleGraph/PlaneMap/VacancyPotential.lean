module

public import Mathlib.Tactic

@[expose] public section
namespace SimpleGraph.VacancyPotential

variable {S : Type*}

/-- A path with its actual number of primitive moves. -/
inductive Path (R : S → S → Prop) : Nat → S → S → Prop
  | nil (s : S) : Path R 0 s s
  | cons {s t u : S} {n : Nat} : R s t → Path R n t u → Path R (n+1) s u

lemma Path.append {R : S → S → Prop} {s t u : S} {m n : Nat}
    (first : Path R m s t) (second : Path R n t u) : Path R (m+n) s u := by
  induction first with
  | nil => simpa using second
  | cons step rest ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Path.cons step (ih second)

/-- A macro controller is useful only when its branches are separately derived
from the intended graph: this lemma supplies the well-founded budget induction. -/
theorem budget {R : S → S → Prop} (good target : S → Prop) (potential : S → Nat)
    (slack : Nat)
    (controller : ∀ s, good s →
      (∃ n t, Path R n s t ∧ target t ∧ n ≤ potential s + slack) ∨
      (∃ n t, Path R n s t ∧ good t ∧ potential t < potential s ∧
        n + potential t ≤ potential s)) :
    ∀ s, good s → ∃ n t, Path R n s t ∧ target t ∧ n ≤ potential s + slack := by
  intro s
  generalize hp : potential s = p
  induction p using Nat.strong_induction_on generalizing s with
  | h p ih =>
    intro hs
    rcases controller s hs with done | ⟨n,t,path,ht,lt,cost⟩
    · simpa only [hp] using done
    · obtain ⟨m,u,tail,hu,bound⟩ := ih (potential t) (by omega) t rfl ht
      exact ⟨n+m,u,path.append tail,hu,by omega⟩

end SimpleGraph.VacancyPotential
