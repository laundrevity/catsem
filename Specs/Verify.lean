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

#print axioms CatSem.synthesizeGuard_sound
#print axioms CatSem.synthesizeGuard_weakest

end CatSem.Verify
