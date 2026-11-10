import Mathlib.Order.Heyting.Basic

namespace CatSem

/-- Given a current abstract state `a` and a target optimization invariant `b`
    in a Heyting domain, synthesize the weakest guard `g` such that `a ⊓ g ≤ b`. -/
def synthesizeGuard {α : Type*} [HeytingAlgebra α] (a b : α) : α :=
  a ⇨ b

-- Sanity checks on Prop Heyting structure
example : ¬ synthesizeGuard True False := by simp [synthesizeGuard]
example : synthesizeGuard False False := by simp [synthesizeGuard]

end CatSem
