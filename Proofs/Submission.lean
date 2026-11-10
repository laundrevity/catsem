import Specs.Defs

namespace CatSem

variable {α β β₁ β₂ : Type*} [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra β₁] [HeytingAlgebra β₂]

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

/-- Edge Soundness: Conjoining state `a` at block `u` with `synthesizeEdgeGuard T a b`
    guarantees `b` holds after the forward transfer `T.post` at block `v`. -/
theorem synthesizeEdgeGuard_sound (T : CFGTransfer α β) (a : α) (b : β) :
    T.post (a ⊓ synthesizeEdgeGuard T a b) ≤ b := by
  unfold synthesizeEdgeGuard
  exact T.gc.l_le (synthesizeGuard_sound a (T.pullback b))

/-- Edge Optimality (Weakest Precondition): Any local guard `g` at block `u` whose
    forward transfer satisfies `T.post (a ⊓ g) ≤ b` implies `g ≤ synthesizeEdgeGuard T a b`. -/
theorem synthesizeEdgeGuard_weakest (T : CFGTransfer α β) (a : α) (b : β) (g : α)
    (h : T.post (a ⊓ g) ≤ b) :
    g ≤ synthesizeEdgeGuard T a b := by
  unfold synthesizeEdgeGuard
  exact synthesizeGuard_weakest a (T.pullback b) g (T.gc.le_u h)

/-- Branch Split Adjunction: Across two branch transitions `T₁ : CFGTransfer α β₁` and
    `T₂ : CFGTransfer α β₂`, the meet of the synthesized branch guards is the exact weakest
    guard establishing both `b₁` and `b₂` along their respective branches. -/
theorem synthesizeBranchGuard_iff (T₁ : CFGTransfer α β₁) (T₂ : CFGTransfer α β₂)
    (a : α) (b₁ : β₁) (b₂ : β₂) (g : α) :
    T₁.post (a ⊓ g) ≤ b₁ ∧ T₂.post (a ⊓ g) ≤ b₂ ↔
      g ≤ synthesizeEdgeGuard T₁ a b₁ ⊓ synthesizeEdgeGuard T₂ a b₂ := by
  rw [le_inf_iff]
  exact and_congr
    ((T₁.gc (a ⊓ g) b₁).trans (synthesizeGuard_adjunction a (T₁.pullback b₁) g))
    ((T₂.gc (a ⊓ g) b₂).trans (synthesizeGuard_adjunction a (T₂.pullback b₂) g))

end CatSem
