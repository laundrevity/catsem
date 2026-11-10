import Specs.Defs
import Proofs.Submission

namespace CatSem.Verify

-- Fails to compile if Proofs/Submission.lean altered any theorem name or signature
example {α : Type*} [HeytingAlgebra α] (a b : α) :
    a ⊓ CatSem.synthesizeGuard a b ≤ b :=
  CatSem.synthesizeGuard_sound a b

example {α : Type*} [HeytingAlgebra α] (a b g : α) (h : a ⊓ g ≤ b) :
    g ≤ CatSem.synthesizeGuard a b :=
  CatSem.synthesizeGuard_weakest a b g h

example {α : Type*} [HeytingAlgebra α] (a b g : α) :
    a ⊓ g ≤ b ↔ g ≤ CatSem.synthesizeGuard a b :=
  CatSem.synthesizeGuard_adjunction a b g

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CatSem.CFGTransfer α β) (a : α) (b : β) :
    T.post (a ⊓ CatSem.synthesizeEdgeGuard T a b) ≤ b :=
  CatSem.synthesizeEdgeGuard_sound T a b

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CatSem.CFGTransfer α β) (a : α) (b : β) (g : α)
    (h : T.post (a ⊓ g) ≤ b) :
    g ≤ CatSem.synthesizeEdgeGuard T a b :=
  CatSem.synthesizeEdgeGuard_weakest T a b g h

example {α β₁ β₂ : Type*} [HeytingAlgebra α] [HeytingAlgebra β₁] [HeytingAlgebra β₂]
    (T₁ : CatSem.CFGTransfer α β₁) (T₂ : CatSem.CFGTransfer α β₂)
    (a : α) (b₁ : β₁) (b₂ : β₂) (g : α) :
    T₁.post (a ⊓ g) ≤ b₁ ∧ T₂.post (a ⊓ g) ≤ b₂ ↔
      g ≤ CatSem.synthesizeEdgeGuard T₁ a b₁ ⊓ CatSem.synthesizeEdgeGuard T₂ a b₂ :=
  CatSem.synthesizeBranchGuard_iff T₁ T₂ a b₁ b₂ g

#print axioms CatSem.synthesizeGuard_sound
#print axioms CatSem.synthesizeGuard_weakest
#print axioms CatSem.synthesizeGuard_adjunction
#print axioms CatSem.synthesizeEdgeGuard_sound
#print axioms CatSem.synthesizeEdgeGuard_weakest
#print axioms CatSem.synthesizeBranchGuard_iff

end CatSem.Verify
