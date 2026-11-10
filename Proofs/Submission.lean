import Specs.Defs

namespace CatSem

variable {α : Type*} [HeytingAlgebra α]

/-- Soundness: Conjoining state `a` with `synthesizeGuard a b` establishes `b`. -/
theorem synthesizeGuard_sound (a b : α) :
    a ⊓ synthesizeGuard a b ≤ b := by
  unfold synthesizeGuard
  exact inf_himp_le

/-- Optimality (Weakest Precondition): Any valid guard `g` implies `synthesizeGuard a b`. -/
theorem synthesizeGuard_weakest (a b g : α) (h : a ⊓ g ≤ b) :
    g ≤ synthesizeGuard a b := by
  unfold synthesizeGuard
  exact le_himp_iff'.mpr h

/-- Heyting Adjunction: Conjoining `a` with `g` establishes `b` if and only if `g` implies `synthesizeGuard a b`. -/
theorem synthesizeGuard_adjunction (a b g : α) :
    a ⊓ g ≤ b ↔ g ≤ synthesizeGuard a b := by
  unfold synthesizeGuard
  exact le_himp_iff'.symm

end CatSem
