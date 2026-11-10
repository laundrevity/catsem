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

/-- Identity CFG transfer on a block `α`. -/
def CFGTransfer.id (α : Type*) [HeytingAlgebra α] : CFGTransfer α α where
  pullback := _root_.id
  post := _root_.id
  gc := fun _ _ => Iff.rfl

/-- Sequential composition of CFG transfers `u → v` (`T₁`) and `v → w` (`T₂`). -/
def CFGTransfer.comp {α β γ : Type*} [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ]
    (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ) : CFGTransfer α γ where
  pullback := T₁.pullback ∘ T₂.pullback
  post := T₂.post ∘ T₁.post
  gc := T₁.gc.compose T₂.gc

-- Sanity checks on identity and composed CFG transfers over Prop
example : ¬ synthesizeEdgeGuard (CFGTransfer.id Prop) True False := by
  simp [synthesizeEdgeGuard, CFGTransfer.id, synthesizeGuard]

example : synthesizeEdgeGuard (CFGTransfer.id Prop) False False := by
  simp [synthesizeEdgeGuard, CFGTransfer.id, synthesizeGuard]

example :
    synthesizeEdgeGuard ((CFGTransfer.id Prop).comp (CFGTransfer.id Prop)) False False := by
  simp [synthesizeEdgeGuard, CFGTransfer.comp, CFGTransfer.id, synthesizeGuard]

/-- A predicate `inv` is a forward loop invariant for a self-transfer `L : CFGTransfer α α`
    when its forward postcondition implies `inv`. -/
def IsLoopInvariant {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) (inv : α) : Prop :=
  L.post inv ≤ inv

/-- Abductive loop-step guard synthesis: synthesizes the weakest local guard on the loop header
    such that conjoining `inv` with the guard re-establishes `inv` across `L`. -/
def synthesizeLoopStepGuard {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) (inv : α) : α :=
  synthesizeEdgeGuard L inv inv

-- Sanity checks on loop invariance and abductive loop-step guard over Prop
example : IsLoopInvariant (CFGTransfer.id Prop) True := by
  simp [IsLoopInvariant, CFGTransfer.id]

example : synthesizeLoopStepGuard (CFGTransfer.id Prop) True := by
  simp [synthesizeLoopStepGuard, synthesizeEdgeGuard, CFGTransfer.id, synthesizeGuard]

/-- An invariant `inv` is an inductive witness for a target property `target` under loop `L`
    if `inv` is a loop invariant for `L` and implies `target`. -/
def IsInductiveFor {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) (inv target : α) : Prop :=
  IsLoopInvariant L inv ∧ inv ≤ target

/-- Hoisted preheader guard synthesis across loop entry edge `E : CFGTransfer α β`:
    synthesizes the weakest guard at the preheader `a₀` that establishes loop invariant `inv`
    upon entering the loop header. -/
def hoistLoopGuard {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (a₀ : α) (inv : β) : α :=
  synthesizeEdgeGuard E a₀ inv

-- Sanity checks on inductive witnesses and hoisted preheader guards over Prop
example : IsInductiveFor (CFGTransfer.id Prop) False True := by
  simp [IsInductiveFor, IsLoopInvariant, CFGTransfer.id]

example : ¬ hoistLoopGuard (CFGTransfer.id Prop) True False := by
  simp [hoistLoopGuard, synthesizeEdgeGuard, CFGTransfer.id, synthesizeGuard]

/-- `n`-fold loop iteration of a self-transfer `L : CFGTransfer α α`. -/
def CFGTransfer.iterate {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) :
    ℕ → CFGTransfer α α
  | 0 => CFGTransfer.id α
  | n + 1 => (CFGTransfer.iterate L n).comp L

-- Sanity checks on n-fold loop iteration over Prop
example : ((CFGTransfer.id Prop).iterate 0).post True := by
  simp [CFGTransfer.iterate, CFGTransfer.id]

example : ¬ synthesizeEdgeGuard ((CFGTransfer.id Prop).iterate 2) True False := by
  simp [CFGTransfer.iterate, CFGTransfer.comp, CFGTransfer.id, synthesizeEdgeGuard, synthesizeGuard]

end CatSem
