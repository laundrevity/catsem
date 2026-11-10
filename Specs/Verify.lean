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

#print axioms CatSem.synthesizeGuard_sound
#print axioms CatSem.synthesizeGuard_weakest
#print axioms CatSem.synthesizeGuard_adjunction

end CatSem.Verify
