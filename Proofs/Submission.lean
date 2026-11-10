import Specs.Defs

namespace CatSem

variable {α β β₁ β₂ γ : Type*} [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra β₁] [HeytingAlgebra β₂] [HeytingAlgebra γ]

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

/-- Meet Preservation: Every `T : CFGTransfer α β` preserves binary meets on pullbacks. -/
theorem pullback_map_inf (T : CFGTransfer α β) (b₁ b₂ : β) :
    T.pullback (b₁ ⊓ b₂) = T.pullback b₁ ⊓ T.pullback b₂ := by
  apply le_antisymm
  · exact le_inf (T.gc.monotone_u inf_le_left) (T.gc.monotone_u inf_le_right)
  · exact T.gc.le_u (le_inf (T.gc.l_le inf_le_left) (T.gc.l_le inf_le_right))

/-- Path Composition: Guard synthesis across a composed path `T₁.comp T₂` equals
    nested stage-by-stage guard synthesis. -/
theorem synthesizeEdgeGuard_comp (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ)
    (a : α) (c : γ) :
    synthesizeEdgeGuard (T₁.comp T₂) a c = synthesizeEdgeGuard T₁ a (T₂.pullback c) := by
  rfl

/-- Conjunctive Target Decomposition: Synthesizing a guard for a conjunction `b₁ ⊓ b₂`
    at the target block equals the meet of the synthesized guards. -/
theorem synthesizeEdgeGuard_map_inf (T : CFGTransfer α β) (a : α) (b₁ b₂ : β) :
    synthesizeEdgeGuard T a (b₁ ⊓ b₂) =
      synthesizeEdgeGuard T a b₁ ⊓ synthesizeEdgeGuard T a b₂ := by
  unfold synthesizeEdgeGuard synthesizeGuard
  rw [pullback_map_inf, himp_inf_distrib]

/-- Diamond Join Adjunction: Given two converging CFG paths `P₁ P₂ : CFGTransfer α γ`
    from entry `α` to join block `γ`, a guard `g : α` guarantees that the joined post-state
    at `γ` satisfies `c` if and only if `g` implies the meet of the path guards. -/
theorem synthesizeDiamondGuard_iff (P₁ P₂ : CFGTransfer α γ) (a : α) (c : γ) (g : α) :
    P₁.post (a ⊓ g) ⊔ P₂.post (a ⊓ g) ≤ c ↔
      g ≤ synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c := by
  rw [sup_le_iff]
  exact synthesizeBranchGuard_iff P₁ P₂ a c c g

/-- Kripke-Joyal Loop Stability: A predicate `inv` is a forward loop invariant
    if and only if it is Kripke-Joyal stable under back-edge pullback (`inv ≤ L.pullback inv`). -/
theorem isLoopInvariant_iff_le_pullback (L : CFGTransfer α α) (inv : α) :
    IsLoopInvariant L inv ↔ inv ≤ L.pullback inv := by
  unfold IsLoopInvariant
  exact L.gc.le_iff_le

/-- Trivial Abductive Guard Characterization: `IsLoopInvariant L inv` holds if and only if
    the abductive loop-step guard is trivial (`synthesizeLoopStepGuard L inv = ⊤`). -/
theorem isLoopInvariant_iff_guard_eq_top (L : CFGTransfer α α) (inv : α) :
    IsLoopInvariant L inv ↔ synthesizeLoopStepGuard L inv = ⊤ := by
  unfold synthesizeLoopStepGuard synthesizeEdgeGuard synthesizeGuard
  exact (isLoopInvariant_iff_le_pullback L inv).trans himp_eq_top_iff.symm

/-- Loop-Step Guard Soundness: Conjoining any candidate invariant `inv` with its abductive
    loop-step guard guarantees the invariant holds after executing the loop body. -/
theorem synthesizeLoopStepGuard_sound (L : CFGTransfer α α) (inv : α) :
    L.post (inv ⊓ synthesizeLoopStepGuard L inv) ≤ inv := by
  unfold synthesizeLoopStepGuard
  exact synthesizeEdgeGuard_sound L inv inv

/-- Conjunctive Loop Invariance: If `inv₁` and `inv₂` are both loop invariants for `L`,
    their conjunction `inv₁ ⊓ inv₂` is also a loop invariant. -/
theorem isLoopInvariant_inf (L : CFGTransfer α α) (inv₁ inv₂ : α) :
    IsLoopInvariant L inv₁ → IsLoopInvariant L inv₂ → IsLoopInvariant L (inv₁ ⊓ inv₂) := by
  intro h₁ h₂
  exact le_inf ((L.gc.monotone_l inf_le_left).trans h₁) ((L.gc.monotone_l inf_le_right).trans h₂)

/-- Two-Step Loop Invariance: If `IsLoopInvariant L inv`, then `inv` is preserved
    across two back-to-back iterations `(L.comp L).post inv ≤ inv`. -/
theorem isLoopInvariant_iterate_two (L : CFGTransfer α α) (inv : α)
    (h : IsLoopInvariant L inv) :
    (L.comp L).post inv ≤ inv := by
  show L.post (L.post inv) ≤ inv
  exact (L.gc.monotone_l h).trans h

/-- Hoisted Guard Entry Target Soundness: If `IsInductiveFor L inv target`, conjoining
    preheader state `a₀` with `hoistLoopGuard E a₀ inv` establishes `target` on loop entry. -/
theorem hoistLoopGuard_entry_target (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    E.post (a₀ ⊓ hoistLoopGuard E a₀ inv) ≤ target := by
  unfold hoistLoopGuard
  exact (synthesizeEdgeGuard_sound E a₀ inv).trans h.2

/-- Hoisted Guard One-Step Invariance: If `IsLoopInvariant L inv`, conjoining `a₀` with
    `hoistLoopGuard E a₀ inv` preserves `inv` after executing the preheader followed by the loop body. -/
theorem hoistLoopGuard_step_invariant (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv : β) (h : IsLoopInvariant L inv) :
    L.post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ inv := by
  unfold hoistLoopGuard
  exact (L.gc.monotone_l (synthesizeEdgeGuard_sound E a₀ inv)).trans h

/-- Hoisted Guard One-Step Target Soundness: If `IsInductiveFor L inv target`, the hoisted
    preheader guard guarantees `target` still holds after executing the preheader followed by the loop body. -/
theorem hoistLoopGuard_step_target (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    L.post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ target := by
  exact (hoistLoopGuard_step_invariant E L a₀ inv h.1).trans h.2

end CatSem
