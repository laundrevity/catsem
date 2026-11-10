import Mathlib.Order.Heyting.Basic
import Mathlib.Order.GaloisConnection.Basic

namespace CatSem

/-- Given a current abstract state `a` and a target optimization invariant `b`
    in a Heyting domain, synthesize the weakest guard `g` such that `a ⊓ g ≤ b`. -/
def synthesizeGuard {α : Type*} [HeytingAlgebra α] (a b : α) : α :=
  a ⇨ b

-- Sanity checks on Prop Heyting structure
example : ¬ synthesizeGuard True False := by simp [synthesizeGuard]
example : synthesizeGuard False False := by simp [synthesizeGuard]

/-- A Kripke-Joyal CFG presheaf/transfer structure representing a basic-block transition `u → v`,
    equipped with a pullback transfer map `pullback : β → α` (weakest precondition) and a
    forward existential postcondition map `post : α → β` (strongest postcondition) linked by
    `GaloisConnection post pullback`. -/
structure CFGTransfer (α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] where
  pullback : β → α
  post : α → β
  gc : GaloisConnection post pullback

/-- Backward guard synthesis across an edge `T : CFGTransfer α β`:
    synthesizes the weakest local guard at source block `u` establishing `b` at target block `v`. -/
def synthesizeEdgeGuard {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (a : α) (b : β) : α :=
  synthesizeGuard a (T.pullback b)

-- Sanity checks on identity CFG transfer over Prop
example :
    let T : CFGTransfer Prop Prop :=
      { pullback := id, post := id, gc := fun _ _ => Iff.rfl }
    ¬ synthesizeEdgeGuard T True False := by
  simp [synthesizeEdgeGuard, synthesizeGuard]

example :
    let T : CFGTransfer Prop Prop :=
      { pullback := id, post := id, gc := fun _ _ => Iff.rfl }
    synthesizeEdgeGuard T False False := by
  simp [synthesizeEdgeGuard, synthesizeGuard]

end CatSem
