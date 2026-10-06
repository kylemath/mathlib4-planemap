/-
Copyright (c) 2026 Kyle Mathewson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Mathewson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.SphericalMap
public import Mathlib.Combinatorics.SimpleGraph.PlaneMap.ErasePermutation
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! # Deleting an edge from a rotation system -/

@[expose] public section
namespace SimpleGraph.RotationSystem

variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-- Delete the unoriented edge of a dart. -/
def eraseGraph (a : G.Dart) : SimpleGraph (Fin n) where
  Adj x y := G.Adj x y ∧ s(x, y) ≠ a.edge
  symm := ⟨fun x y h => ⟨h.1.symm, by
    intro hh
    exact h.2 (by simpa only [Sym2.eq_swap] using hh)⟩⟩
  loopless := ⟨fun x h => h.1.ne rfl⟩

/-- View a surviving dart in the original graph. -/
def eraseDart (a : G.Dart) (d : (eraseGraph a).Dart) : G.Dart :=
  ⟨d.toProd, d.adj.1⟩

@[simp] theorem eraseDart_fst (a : G.Dart) (d : (eraseGraph a).Dart) :
    (eraseDart a d).fst = d.fst := rfl
@[simp] theorem eraseDart_snd (a : G.Dart) (d : (eraseGraph a).Dart) :
    (eraseDart a d).snd = d.snd := rfl
@[simp] theorem eraseDart_symm (a : G.Dart) (d : (eraseGraph a).Dart) :
    eraseDart a d.symm = (eraseDart a d).symm := rfl

def eraseDartEquiv (a : G.Dart) :
    (eraseGraph a).Dart ≃ {d : G.Dart // d ≠ a ∧ d ≠ a.symm} where
  toFun d := ⟨eraseDart a d, by
    have hd : d.edge ≠ a.edge := d.adj.2
    constructor
    · intro hh; exact hd (congrArg Dart.edge hh)
    · intro hh
      apply hd
      have hh' := congrArg Dart.edge hh
      rw [Dart.edge_symm] at hh'
      exact hh' ⟩
  invFun d := ⟨d.val.toProd, d.val.adj, by
    change d.val.edge ≠ a.edge
    intro hh
    exact ((dart_edge_eq_iff d.val a).mp hh).elim d.property.1 d.property.2⟩
  left_inv d := by apply Dart.ext; rfl
  right_inv d := by apply Subtype.ext; apply Dart.ext; rfl

noncomputable def eraseNext (R : RotationSystem G) (a : G.Dart) : Equiv.Perm G.Dart :=
  (R.next.erasePoint a).erasePoint a.symm

@[simp] theorem eraseNext_a (R : RotationSystem G) (a : G.Dart) :
    R.eraseNext a a = a :=
  Equiv.Perm.erasePoint_fixed _ _ _ (Equiv.Perm.erasePoint_self _ _)

@[simp] theorem eraseNext_symm (R : RotationSystem G) (a : G.Dart) :
    R.eraseNext a a.symm = a.symm := Equiv.Perm.erasePoint_self _ _

theorem eraseNext_fst (R : RotationSystem G) (a d : G.Dart) :
    (R.eraseNext a d).fst = d.fst := by
  exact Equiv.Perm.erasePoint_preserves (R.next.erasePoint a) a.symm
    (fun z => z.fst)
    (fun z => Equiv.Perm.erasePoint_preserves R.next a (fun z => z.fst) R.next_fst z) d

theorem eraseNext_kept (R : RotationSystem G) (a d : G.Dart) :
    (R.eraseNext a d ≠ a ∧ R.eraseNext a d ≠ a.symm) ↔ (d ≠ a ∧ d ≠ a.symm) := by
  have h1 := (R.eraseNext a).injective.eq_iff (a := d) (b := a)
  have h2 := (R.eraseNext a).injective.eq_iff (a := d) (b := a.symm)
  simp only [eraseNext_a, eraseNext_symm] at h1 h2
  simp only [ne_eq, h1, h2]

noncomputable def eraseRotation (R : RotationSystem G) (a : G.Dart) :
    RotationSystem (eraseGraph a) where
  next := (eraseDartEquiv a).trans
    (((R.eraseNext a).subtypePerm (R.eraseNext_kept a)).trans (eraseDartEquiv a).symm)
  next_fst d := R.eraseNext_fst a (eraseDart a d)
  cyclic d e hde := by
    obtain ⟨k, hk⟩ := R.cyclic (eraseDart a d) (eraseDart a e) hde
    have hd := ((eraseDartEquiv a) d).property
    have he := ((eraseDartEquiv a) e).property
    obtain ⟨j, hj⟩ := Equiv.Perm.erasePoint_iterate R.next a
      (eraseDart a d) (eraseDart a e) hd.1 he.1 ⟨k, hk⟩
    obtain ⟨l, hl⟩ := Equiv.Perm.erasePoint_iterate (R.next.erasePoint a) a.symm
      (eraseDart a d) (eraseDart a e) hd.2 he.2 ⟨j, hj⟩
    refine ⟨l, ?_⟩
    let σ := (eraseDartEquiv a).trans
      (((R.eraseNext a).subtypePerm (R.eraseNext_kept a)).trans (eraseDartEquiv a).symm)
    have hi : ∀ l, eraseDart a ((⇑σ)^[l] d) = (⇑(R.eraseNext a))^[l] (eraseDart a d) := by
      intro l
      induction l with
      | zero => rfl
      | succ l ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        change R.eraseNext a (eraseDart a ((⇑σ)^[l] d)) = _
        rw [ih]
    apply (eraseDartEquiv a).injective
    apply Subtype.ext
    exact (hi l).trans hl

@[simp] theorem eraseRotation_next (R : RotationSystem G) (a : G.Dart)
    (d : (eraseGraph a).Dart) :
    eraseDart a ((R.eraseRotation a).next d) = R.eraseNext a (eraseDart a d) := rfl

end SimpleGraph.RotationSystem
