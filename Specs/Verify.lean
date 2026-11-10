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

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CatSem.CFGTransfer α β) (b₁ b₂ : β) :
    T.pullback (b₁ ⊓ b₂) = T.pullback b₁ ⊓ T.pullback b₂ :=
  CatSem.pullback_map_inf T b₁ b₂

example {α β γ : Type*} [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ]
    (T₁ : CatSem.CFGTransfer α β) (T₂ : CatSem.CFGTransfer β γ)
    (a : α) (c : γ) :
    CatSem.synthesizeEdgeGuard (T₁.comp T₂) a c =
      CatSem.synthesizeEdgeGuard T₁ a (T₂.pullback c) :=
  CatSem.synthesizeEdgeGuard_comp T₁ T₂ a c

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CatSem.CFGTransfer α β) (a : α) (b₁ b₂ : β) :
    CatSem.synthesizeEdgeGuard T a (b₁ ⊓ b₂) =
      CatSem.synthesizeEdgeGuard T a b₁ ⊓ CatSem.synthesizeEdgeGuard T a b₂ :=
  CatSem.synthesizeEdgeGuard_map_inf T a b₁ b₂

example {α γ : Type*} [HeytingAlgebra α] [HeytingAlgebra γ]
    (P₁ P₂ : CatSem.CFGTransfer α γ) (a : α) (c : γ) (g : α) :
    P₁.post (a ⊓ g) ⊔ P₂.post (a ⊓ g) ≤ c ↔
      g ≤ CatSem.synthesizeEdgeGuard P₁ a c ⊓ CatSem.synthesizeEdgeGuard P₂ a c :=
  CatSem.synthesizeDiamondGuard_iff P₁ P₂ a c g

example {α : Type*} [HeytingAlgebra α]
    (L : CatSem.CFGTransfer α α) (inv : α) :
    CatSem.IsLoopInvariant L inv ↔ inv ≤ L.pullback inv :=
  CatSem.isLoopInvariant_iff_le_pullback L inv

example {α : Type*} [HeytingAlgebra α]
    (L : CatSem.CFGTransfer α α) (inv : α) :
    CatSem.IsLoopInvariant L inv ↔ CatSem.synthesizeLoopStepGuard L inv = ⊤ :=
  CatSem.isLoopInvariant_iff_guard_eq_top L inv

example {α : Type*} [HeytingAlgebra α]
    (L : CatSem.CFGTransfer α α) (inv : α) :
    L.post (inv ⊓ CatSem.synthesizeLoopStepGuard L inv) ≤ inv :=
  CatSem.synthesizeLoopStepGuard_sound L inv

example {α : Type*} [HeytingAlgebra α]
    (L : CatSem.CFGTransfer α α) (inv₁ inv₂ : α) :
    CatSem.IsLoopInvariant L inv₁ →
      CatSem.IsLoopInvariant L inv₂ →
      CatSem.IsLoopInvariant L (inv₁ ⊓ inv₂) :=
  CatSem.isLoopInvariant_inf L inv₁ inv₂

example {α : Type*} [HeytingAlgebra α]
    (L : CatSem.CFGTransfer α α) (inv : α)
    (h : CatSem.IsLoopInvariant L inv) :
    (L.comp L).post inv ≤ inv :=
  CatSem.isLoopInvariant_iterate_two L inv h

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CatSem.CFGTransfer α β) (L : CatSem.CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : CatSem.IsInductiveFor L inv target) :
    E.post (a₀ ⊓ CatSem.hoistLoopGuard E a₀ inv) ≤ target :=
  CatSem.hoistLoopGuard_entry_target E L a₀ inv target h

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CatSem.CFGTransfer α β) (L : CatSem.CFGTransfer β β)
    (a₀ : α) (inv : β) (h : CatSem.IsLoopInvariant L inv) :
    L.post (E.post (a₀ ⊓ CatSem.hoistLoopGuard E a₀ inv)) ≤ inv :=
  CatSem.hoistLoopGuard_step_invariant E L a₀ inv h

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CatSem.CFGTransfer α β) (L : CatSem.CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : CatSem.IsInductiveFor L inv target) :
    L.post (E.post (a₀ ⊓ CatSem.hoistLoopGuard E a₀ inv)) ≤ target :=
  CatSem.hoistLoopGuard_step_target E L a₀ inv target h

example {α : Type*} [HeytingAlgebra α]
    (L : CatSem.CFGTransfer α α) (inv : α)
    (h : CatSem.IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post inv ≤ inv :=
  CatSem.isLoopInvariant_iterate L inv h

example {α : Type*} [HeytingAlgebra α]
    (L : CatSem.CFGTransfer α α) (inv : α)
    (h : CatSem.IsLoopInvariant L inv) :
    ∀ n : ℕ, inv ≤ (L.iterate n).pullback inv :=
  CatSem.isLoopInvariant_iterate_pullback L inv h

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CatSem.CFGTransfer α β) (L : CatSem.CFGTransfer β β)
    (a₀ : α) (inv : β) (h : CatSem.IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ CatSem.hoistLoopGuard E a₀ inv)) ≤ inv :=
  CatSem.hoistLoopGuard_iterate_invariant E L a₀ inv h

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CatSem.CFGTransfer α β) (L : CatSem.CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : CatSem.IsInductiveFor L inv target) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ CatSem.hoistLoopGuard E a₀ inv)) ≤ target :=
  CatSem.hoistLoopGuard_iterate_target E L a₀ inv target h

#print axioms CatSem.synthesizeGuard_sound
#print axioms CatSem.synthesizeGuard_weakest
#print axioms CatSem.synthesizeGuard_adjunction
#print axioms CatSem.synthesizeEdgeGuard_sound
#print axioms CatSem.synthesizeEdgeGuard_weakest
#print axioms CatSem.synthesizeBranchGuard_iff
#print axioms CatSem.pullback_map_inf
#print axioms CatSem.synthesizeEdgeGuard_comp
#print axioms CatSem.synthesizeEdgeGuard_map_inf
#print axioms CatSem.synthesizeDiamondGuard_iff
#print axioms CatSem.isLoopInvariant_iff_le_pullback
#print axioms CatSem.isLoopInvariant_iff_guard_eq_top
#print axioms CatSem.synthesizeLoopStepGuard_sound
#print axioms CatSem.isLoopInvariant_inf
#print axioms CatSem.isLoopInvariant_iterate_two
#print axioms CatSem.hoistLoopGuard_entry_target
#print axioms CatSem.hoistLoopGuard_step_invariant
#print axioms CatSem.hoistLoopGuard_step_target
#print axioms CatSem.isLoopInvariant_iterate
#print axioms CatSem.isLoopInvariant_iterate_pullback
#print axioms CatSem.hoistLoopGuard_iterate_invariant
#print axioms CatSem.hoistLoopGuard_iterate_target

end CatSem.Verify
