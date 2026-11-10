import Specs.Defs

namespace CatSem

variable {α : Type*} [HeytingAlgebra α]

/-- Soundness: Conjoining state `a` with `synthesizeGuard a b` establishes `b`. -/
theorem synthesizeGuard_sound (a b : α) :
    a ⊓ synthesizeGuard a b ≤ b := by
  sorry

/-- Optimality (Weakest Precondition): Any valid guard `g` implies `synthesizeGuard a b`. -/
theorem synthesizeGuard_weakest (a b g : α) (h : a ⊓ g ≤ b) :
    g ≤ synthesizeGuard a b := by
  sorry

/-- Heyting Adjunction: Conjoining `a` with `g` establishes `b` if and only if `g` implies `synthesizeGuard a b`. -/
theorem synthesizeGuard_adjunction (a b g : α) :
    a ⊓ g ≤ b ↔ g ≤ synthesizeGuard a b := by
  sorry

end CatSem
