import Specs.Defs

namespace CatSem

variable {α β β₁ β₂ γ Term Val S S₀ S₁ S₂ : Type*} [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra β₁] [HeytingAlgebra β₂] [HeytingAlgebra γ]

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

/-- Arbitrary-Iteration Loop Invariance: If `IsLoopInvariant L inv`, then `inv` is preserved
    across any number of loop iterations (`∀ n : ℕ, (L.iterate n).post inv ≤ inv`). -/
theorem isLoopInvariant_iterate (L : CFGTransfer α α) (inv : α)
    (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post inv ≤ inv := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    show L.post ((L.iterate n).post inv) ≤ inv
    exact (L.gc.monotone_l ih).trans h

/-- Arbitrary-Iteration Kripke-Joyal Pullback Stability: If `IsLoopInvariant L inv`, then `inv`
    is Kripke-Joyal stable under pullback along any `n`-fold loop path (`∀ n : ℕ, inv ≤ (L.iterate n).pullback inv`). -/
theorem isLoopInvariant_iterate_pullback (L : CFGTransfer α α) (inv : α)
    (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, inv ≤ (L.iterate n).pullback inv := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    show inv ≤ (L.iterate n).pullback (L.pullback inv)
    exact ih.trans ((L.iterate n).gc.monotone_u (L.gc.le_u h))

/-- Hoisted Guard Arbitrary-Iteration Invariance: If `IsLoopInvariant L inv`, the single
    preheader guard `hoistLoopGuard E a₀ inv` preserves `inv` after entering the loop and running `n` iterations. -/
theorem hoistLoopGuard_iterate_invariant (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv : β) (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ inv := by
  intro n
  induction n with
  | zero => exact synthesizeEdgeGuard_sound E a₀ inv
  | succ n ih =>
    show L.post ((L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv))) ≤ inv
    exact (L.gc.monotone_l ih).trans h

/-- Hoisted Guard Arbitrary-Iteration Target Soundness: If `IsInductiveFor L inv target`,
    the hoisted preheader guard guarantees `target` holds after entering the loop and running `n` iterations. -/
theorem hoistLoopGuard_iterate_target (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ target := by
  intro n
  exact (hoistLoopGuard_iterate_invariant E L a₀ inv h.1 n).trans h.2

/-- Kripke-Joyal Forcing Adjunction: Across any `T : CFGTransfer α β`,
    `a` forces `q` after `T` if and only if `a` locally forces the pullback `T.pullback q`. -/
theorem forcesAfter_iff_pullback (T : CFGTransfer α β) (a : α) (q : β) :
    ForcesAfter T a q ↔ Forces a (T.pullback q) := by
  unfold ForcesAfter Forces
  exact T.gc.le_iff_le

/-- Kripke-Joyal Implication Forcing: At stage `a`, a guarded stage `a ⊓ g` forces `p`
    if and only if `g` forces the synthesized guard `synthesizeGuard a p`. -/
theorem forces_guard_iff (a p g : α) :
    Forces (a ⊓ g) p ↔ Forces g (synthesizeGuard a p) := by
  unfold Forces
  exact synthesizeGuard_adjunction a p g

/-- Kripke-Joyal Rewrite-Chain Forcing: For two conditional rewrite preconditions `p₁ p₂ : α`,
    a guarded stage `a ⊓ g` forces `p₁ ⊓ p₂` if and only if `g` forces the meet of their synthesized guards. -/
theorem forces_rewrite_chain_iff (a p₁ p₂ g : α) :
    Forces (a ⊓ g) (p₁ ⊓ p₂) ↔ Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) := by
  unfold Forces
  rw [le_inf_iff, le_inf_iff]
  exact and_congr (synthesizeGuard_adjunction a p₁ g) (synthesizeGuard_adjunction a p₂ g)

/-- Kripke-Joyal Hoisted Loop Forcing: If `IsInductiveFor L inv target`, then for every
    iteration count `n : ℕ`, the guarded preheader stage forces `target` along the composed
    morphism `E.comp (L.iterate n)`. -/
theorem forcesAfter_hoistLoopGuard_iterate (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    ∀ n : ℕ, ForcesAfter (E.comp (L.iterate n)) (a₀ ⊓ hoistLoopGuard E a₀ inv) target := by
  intro n
  show (L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ target
  exact hoistLoopGuard_iterate_target E L a₀ inv target h n

/-- Reflexivity of Guarded Equivalence: Any term `t` is guardedly equivalent to itself under `⊤`. -/
theorem guardedEquiv_refl (eval : α → Term → Val) (t : Term) :
    GuardedEquiv eval ⊤ t t := by
  intro s _
  rfl

/-- Symmetry of Guarded Equivalence: Guarded equivalence is symmetric. -/
theorem guardedEquiv_symm (eval : α → Term → Val) (p : α) (t₁ t₂ : Term) :
    GuardedEquiv eval p t₁ t₂ → GuardedEquiv eval p t₂ t₁ := by
  intro h s hs
  exact (h s hs).symm

/-- Conjunctive Transitivity of Guarded Equivalence: Chaining two conditional rewrites
    `GuardedEquiv eval p₁ t₁ t₂` and `GuardedEquiv eval p₂ t₂ t₃` yields a sound equivalence
    under the conjoined guard `p₁ ⊓ p₂`. -/
theorem guardedEquiv_trans_inf (eval : α → Term → Val) (p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : GuardedEquiv eval p₁ t₁ t₂) (h₂ : GuardedEquiv eval p₂ t₂ t₃) :
    GuardedEquiv eval (p₁ ⊓ p₂) t₁ t₃ := by
  intro s hs
  unfold Forces at hs
  exact (h₁ s (hs.trans inf_le_left)).trans (h₂ s (hs.trans inf_le_right))

/-- Abductive Rewrite-Chain Soundness: Given `GuardedEquiv eval p₁ t₁ t₂` and
    `GuardedEquiv eval p₂ t₂ t₃`, at any stage `a : α`, conjoining `a` with the synthesized
    residual guard `synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂` guarantees `t₁` and `t₃`
    evaluate identically at the guarded stage. -/
theorem guardedEquiv_synthesize_chain (eval : α → Term → Val) (a p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : GuardedEquiv eval p₁ t₁ t₂) (h₂ : GuardedEquiv eval p₂ t₂ t₃) :
    eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) t₁ =
      eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) t₃ := by
  apply guardedEquiv_trans_inf eval p₁ p₂ t₁ t₂ t₃ h₁ h₂
  exact (forces_rewrite_chain_iff a p₁ p₂ _).mpr le_rfl

/-- Guarded Equivalence Monotonicity (Weakening): If `Forces p q` and
    `GuardedEquiv eval q t₁ t₂`, then `GuardedEquiv eval p t₁ t₂`. -/
theorem guardedEquiv_weaken (eval : α → Term → Val) (p q : α) (t₁ t₂ : Term)
    (hpq : Forces p q) (h : GuardedEquiv eval q t₁ t₂) :
    GuardedEquiv eval p t₁ t₂ := by
  intro s hs
  unfold Forces at hs hpq
  exact h s (hs.trans hpq)

/-- Kripke-Joyal Pullback of Guarded Equivalence: If `GuardedEquiv evalβ q t₁ t₂`,
    then `GuardedEquiv (pullbackEval T evalβ) (T.pullback q) t₁ t₂`. -/
theorem guardedEquiv_pullback (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (q : β) (t₁ t₂ : Term) (h : GuardedEquiv evalβ q t₁ t₂) :
    GuardedEquiv (pullbackEval T evalβ) (T.pullback q) t₁ t₂ := by
  intro s hs
  unfold pullbackEval
  exact h (T.post s) ((forcesAfter_iff_pullback T s q).mpr hs)

/-- Inter-Block Abductive Guarded Rewrite Soundness: If `GuardedEquiv evalβ q t₁ t₂`,
    then at any upstream stage `a : α`, conjoining `a` with `synthesizeEdgeGuard T a q`
    guarantees `t₁` and `t₂` evaluate identically after transferring across `T`. -/
theorem guardedEquiv_edge_synthesize (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (a : α) (q : β) (t₁ t₂ : Term) (h : GuardedEquiv evalβ q t₁ t₂) :
    evalβ (T.post (a ⊓ synthesizeEdgeGuard T a q)) t₁ =
      evalβ (T.post (a ⊓ synthesizeEdgeGuard T a q)) t₂ := by
  exact h _ (synthesizeEdgeGuard_sound T a q)

/-- Loop-Hoisted Guarded Rewrite Soundness: If `IsInductiveFor L inv q` and
    `GuardedEquiv evalβ q t₁ t₂`, then for every iteration count `n : ℕ`, the single
    preheader guard `hoistLoopGuard E a₀ inv` guarantees `t₁` and `t₂` evaluate identically
    after entering the loop and running `n` iterations. -/
theorem guardedEquiv_hoistLoopGuard_iterate (E : CFGTransfer α β) (L : CFGTransfer β β)
    (evalβ : β → Term → Val) (a₀ : α) (inv q : β) (t₁ t₂ : Term)
    (hind : IsInductiveFor L inv q) (heq : GuardedEquiv evalβ q t₁ t₂) :
    ∀ n : ℕ,
      evalβ ((E.comp (L.iterate n)).post (a₀ ⊓ hoistLoopGuard E a₀ inv)) t₁ =
        evalβ ((E.comp (L.iterate n)).post (a₀ ⊓ hoistLoopGuard E a₀ inv)) t₂ := by
  intro n
  exact heq _ (forcesAfter_hoistLoopGuard_iterate E L a₀ inv q hind n)

/-- Binary Congruence of Guarded Equivalence: Under `CompatibleOp2 eval op semOp`,
    guarded equivalences on subterms compose under the meet of their guards. -/
theorem guardedEquiv_congr2 (eval : α → Term → Val)
    (op : Term → Term → Term) (semOp : α → Val → Val → Val)
    (p₁ p₂ : α) (t₁ u₁ t₂ u₂ : Term)
    (hcompat : CompatibleOp2 eval op semOp)
    (h₁ : GuardedEquiv eval p₁ t₁ u₁) (h₂ : GuardedEquiv eval p₂ t₂ u₂) :
    GuardedEquiv eval (p₁ ⊓ p₂) (op t₁ t₂) (op u₁ u₂) := by
  intro s hs
  unfold Forces at hs
  rw [hcompat s t₁ t₂, hcompat s u₁ u₂]
  exact congrArg₂ (semOp s) (h₁ s (hs.trans inf_le_left)) (h₂ s (hs.trans inf_le_right))

/-- Abductive Binary Congruence Soundness: Under `CompatibleOp2 eval op semOp`,
    `GuardedEquiv eval p₁ t₁ u₁`, and `GuardedEquiv eval p₂ t₂ u₂`, at any stage `a : α`,
    conjoining `a` with `synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂` guarantees
    `op t₁ t₂` and `op u₁ u₂` evaluate identically at the guarded stage. -/
theorem guardedEquiv_congr2_synthesize (eval : α → Term → Val)
    (op : Term → Term → Term) (semOp : α → Val → Val → Val)
    (a p₁ p₂ : α) (t₁ u₁ t₂ u₂ : Term)
    (hcompat : CompatibleOp2 eval op semOp)
    (h₁ : GuardedEquiv eval p₁ t₁ u₁) (h₂ : GuardedEquiv eval p₂ t₂ u₂) :
    eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) (op t₁ t₂) =
      eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) (op u₁ u₂) := by
  apply guardedEquiv_congr2 eval op semOp p₁ p₂ t₁ u₁ t₂ u₂ hcompat h₁ h₂
  exact (forces_rewrite_chain_iff a p₁ p₂ _).mpr le_rfl

/-- Pullback Meet Commutativity for Guarded Equivalence: Across any `T : CFGTransfer α β`,
    guarded equivalence under `T.pullback (q₁ ⊓ q₂)` is equivalent to guarded equivalence
    under `T.pullback q₁ ⊓ T.pullback q₂`. -/
theorem guardedEquiv_pullback_inf_commute (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (q₁ q₂ : β) (t₁ t₂ : Term) :
    GuardedEquiv (pullbackEval T evalβ) (T.pullback (q₁ ⊓ q₂)) t₁ t₂ ↔
      GuardedEquiv (pullbackEval T evalβ) (T.pullback q₁ ⊓ T.pullback q₂) t₁ t₂ := by
  rw [pullback_map_inf T q₁ q₂]

/-- Diamond Join Guarded Rewrite Soundness: Given two converging CFG paths
    `P₁ P₂ : CFGTransfer α γ` and a downstream rewrite `GuardedEquiv evalγ c t₁ t₂`,
    conjoining `a` with `g := synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c`
    guarantees `t₁` and `t₂` evaluate identically along both paths at the join block. -/
theorem guardedEquiv_diamond (P₁ P₂ : CFGTransfer α γ) (evalγ : γ → Term → Val)
    (a : α) (c : γ) (t₁ t₂ : Term) (h : GuardedEquiv evalγ c t₁ t₂) :
    let g := synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c
    evalγ (P₁.post (a ⊓ g)) t₁ = evalγ (P₁.post (a ⊓ g)) t₂ ∧
      evalγ (P₂.post (a ⊓ g)) t₁ = evalγ (P₂.post (a ⊓ g)) t₂ := by
  intro g
  have hj := (synthesizeDiamondGuard_iff P₁ P₂ a c g).mpr le_rfl
  exact ⟨h _ (le_sup_left.trans hj), h _ (le_sup_right.trans hj)⟩

/-- Concrete Pullback Application: Applying `(stateTransfer step).pullback Q` at `s₁`
    computes the weakest precondition `Q (step s₁)`. -/
theorem stateTransfer_pullback_apply (step : S₁ → S₂) (Q : S₂ → Prop) (s₁ : S₁) :
    (stateTransfer step).pullback Q s₁ ↔ Q (step s₁) := by
  exact Iff.rfl

/-- Concrete Edge Guard Synthesis: Pointwise evaluation of `synthesizeEdgeGuard (stateTransfer step) P Q`
    at state `s₁` is the logical implication `P s₁ → Q (step s₁)`. -/
theorem stateTransfer_synthesizeEdgeGuard_apply (step : S₁ → S₂)
    (P : S₁ → Prop) (Q : S₂ → Prop) (s₁ : S₁) :
    synthesizeEdgeGuard (stateTransfer step) P Q s₁ ↔ (P s₁ → Q (step s₁)) := by
  unfold synthesizeEdgeGuard synthesizeGuard
  rw [Pi.himp_apply, himp_iff_imp, stateTransfer_pullback_apply]

/-- Concrete Hoare Loop Invariance: `IsLoopInvariant (stateTransfer step) inv` holds if and only if
    `inv` is preserved pointwise by `step` (`∀ s, inv s → inv (step s)`). -/
theorem stateTransfer_isLoopInvariant_iff (step : S → S) (inv : S → Prop) :
    IsLoopInvariant (stateTransfer step) inv ↔ ∀ s, inv s → inv (step s) := by
  exact isLoopInvariant_iff_le_pullback (stateTransfer step) inv

/-- Concrete Loop-Hoisted Guarded Rewrite Soundness: Given an entry transition `init : S₀ → S`,
    a loop step `step : S → S`, predicates `a₀ : S₀ → Prop` and `inv q : S → Prop`, and a
    conditional IR rewrite `GuardedEquiv eval q t₁ t₂`, if `IsInductiveFor (stateTransfer step) inv q`,
    then for every `n : ℕ`, `t₁` and `t₂` evaluate identically after entering the loop under the
    hoisted guard and executing `n` iterations. -/
theorem stateTransfer_hoistLoopGuard_iterate_equiv (init : S₀ → S) (step : S → S)
    (eval : (S → Prop) → Term → Val) (a₀ : S₀ → Prop) (inv q : S → Prop) (t₁ t₂ : Term)
    (hind : IsInductiveFor (stateTransfer step) inv q) (heq : GuardedEquiv eval q t₁ t₂) :
    ∀ n : ℕ,
      eval (((stateTransfer init).comp ((stateTransfer step).iterate n)).post
        (a₀ ⊓ hoistLoopGuard (stateTransfer init) a₀ inv)) t₁ =
      eval (((stateTransfer init).comp ((stateTransfer step).iterate n)).post
        (a₀ ⊓ hoistLoopGuard (stateTransfer init) a₀ inv)) t₂ := by
  intro n
  exact guardedEquiv_hoistLoopGuard_iterate (stateTransfer init) (stateTransfer step)
    eval a₀ inv q t₁ t₂ hind heq n

/-! ## Milestone 1: Executable Guarded Expression Optimizer & Concrete State Bridge -/

/-! ### Guard normalisation (implementation of `synthesizeGuardIR`)

Atoms (`.nonZero`, `.eq`) are treated as opaque propositional variables: no arithmetic
reasoning or constant folding is performed. A context is read as the list of its conjuncts
("hypotheses"); a target is simplified by dropping every conjunct that is already a
hypothesis. -/

/-- `g` is syntactically `.top`. -/
private def GuardIR.isTop : GuardIR → Bool
  | .top => true
  | _ => false

/-- `g` is syntactically `.bot`. -/
private def GuardIR.isBot : GuardIR → Bool
  | .bot => true
  | _ => false

/-- Conjunction with unit `.top` and absorbing element `.bot`. -/
private def GuardIR.mkConj (g₁ g₂ : GuardIR) : GuardIR :=
  match g₁, g₂ with
  | .top, g => g
  | g, .top => g
  | .bot, _ => .bot
  | _, .bot => .bot
  | g₁, g₂ => .conj g₁ g₂

/-- Implication with the trivial cases `g ⇨ ⊤ = ⊤`, `⊤ ⇨ g = g` and `⊥ ⇨ g = ⊤` folded away. -/
private def GuardIR.mkImp (g₁ g₂ : GuardIR) : GuardIR :=
  match g₁, g₂ with
  | _, .top => .top
  | .top, g => g
  | .bot, _ => .top
  | g₁, g₂ => .imp g₁ g₂

/-- Context-free normal form: rebuilds every `.conj` / `.imp` with the smart constructors. -/
private def GuardIR.nf : GuardIR → GuardIR
  | .conj g₁ g₂ => GuardIR.mkConj (GuardIR.nf g₁) (GuardIR.nf g₂)
  | .imp g₁ g₂ => GuardIR.mkImp (GuardIR.nf g₁) (GuardIR.nf g₂)
  | g => g

/-- `hasHyp ctx h`: `h` is literally one of the conjuncts of `ctx`, or `ctx` contains the
    conjunct `.bot` (ex falso). -/
private def GuardIR.hasHyp : GuardIR → GuardIR → Bool
  | .top, _ => false
  | .bot, _ => true
  | .conj c₁ c₂, h => GuardIR.hasHyp c₁ h || GuardIR.hasHyp c₂ h
  | c, h => decide (c = h)

/-- `residual ctx g`: what is left of the target `g` once every conjunct that is already a
    hypothesis of `ctx` (or of an earlier conjunct of `g`) has been discharged. -/
private def GuardIR.residual : GuardIR → GuardIR → GuardIR
  | _, .top => .top
  | ctx, .conj g₁ g₂ =>
    GuardIR.mkConj (GuardIR.residual ctx g₁) (GuardIR.residual (.conj ctx g₁) g₂)
  | ctx, .imp g₁ g₂ =>
    if GuardIR.hasHyp ctx (.imp g₁ g₂) then .top
    else GuardIR.mkImp g₁ (GuardIR.residual (.conj ctx g₁) g₂)
  | ctx, g => if GuardIR.hasHyp ctx g then .top else g

/-- `g` simplified relative to the context `ctx`; equivalent to `g` wherever `ctx` holds. -/
private def GuardIR.simplifyUnder (ctx g : GuardIR) : GuardIR :=
  GuardIR.residual (GuardIR.nf ctx) (GuardIR.nf g)

/-- `ctx` syntactically entails `g`: nothing of `g` is left once the hypotheses of `ctx` have
    been discharged. Equivalently (`GuardIR.entails_eq`), the residual guard
    `synthesizeGuardIR ctx g` is `.top`. -/
private def GuardIR.entails (ctx g : GuardIR) : Bool :=
  GuardIR.isTop (GuardIR.simplifyUnder ctx g)

/-- `hyp ⇨ r` for a residual `r ≠ ⊤`, without an `.imp .top _` wrapper. -/
private def GuardIR.wrapImp (hyp r : GuardIR) : GuardIR :=
  match hyp with
  | .top => r
  | hyp => .imp hyp r

/-- Computable Heyting guard synthesis on `GuardIR` syntax. -/
def synthesizeGuardIR (a b : GuardIR) : GuardIR :=
  match GuardIR.simplifyUnder a b with
  | .top => .top
  | r => GuardIR.wrapImp (GuardIR.residual .top (GuardIR.nf a)) r

/-! ### Expression rewriting (implementation of `optimizeExpr`) -/

/-- If `num` is syntactically `x * d` or `d * x`, the cofactor `x`. -/
private def PureExpr.cancelFactor? (num d : PureExpr) : Option PureExpr :=
  match num with
  | .mul a b => if b = d then some a else if a = d then some b else none
  | _ => none

/-- The pure arithmetic expression computed by `e`, if `e` contains neither divisions nor
    guard branches. -/
private def Expr.asPure? : Expr → Option PureExpr
  | .pure p => some p
  | .add e₁ e₂ =>
    match Expr.asPure? e₁, Expr.asPure? e₂ with
    | some p₁, some p₂ => some (.add p₁ p₂)
    | _, _ => none
  | .sub e₁ e₂ =>
    match Expr.asPure? e₁, Expr.asPure? e₂ with
    | some p₁, some p₂ => some (.sub p₁ p₂)
    | _, _ => none
  | .mul e₁ e₂ =>
    match Expr.asPure? e₁, Expr.asPure? e₂ with
    | some p₁, some p₂ => some (.mul p₁ p₂)
    | _, _ => none
  | _ => none

/-- Facts that hold in every environment in which `e` evaluates to a value: each division
    executed on the way has a non-zero divisor (a zero divisor yields `.trap` or `.ub`). -/
private def Expr.postFacts : Expr → GuardIR
  | .pure _ => .top
  | .add e₁ e₂ | .sub e₁ e₂ | .mul e₁ e₂ => .conj (Expr.postFacts e₁) (Expr.postFacts e₂)
  | .checkedDiv n d | .uncheckedDiv n d =>
    .conj (.conj (Expr.postFacts n) (Expr.postFacts d))
      (match Expr.asPure? d with
       | some pd => .nonZero pd
       | none => .top)
  | .iteGuard _ _ _ => .top

/-- Rebuilds a binary arithmetic node, fusing two pure operands into one pure expression. -/
private def Expr.mkBin (pureOp : PureExpr → PureExpr → PureExpr)
    (exprOp : Expr → Expr → Expr) (e₁ e₂ : Expr) : Expr :=
  match e₁, e₂ with
  | .pure p₁, .pure p₂ => .pure (pureOp p₁ p₂)
  | _, _ => exprOp e₁ e₂

/-- The division node of the original kind (`true` = checked, `false` = unchecked). -/
private def Expr.rawDiv : Bool → Expr → Expr → Expr
  | true, n, d => .checkedDiv n d
  | false, n, d => .uncheckedDiv n d

/-- Division by a pure divisor `pd` that is known to be non-zero: cancels `(x * pd) / pd` and
    `(pd * x) / pd` to `x`, and otherwise emits an unchecked division. -/
private def Expr.mkSafeDiv (n : Expr) (pd : PureExpr) : Expr :=
  match n with
  | .pure pn =>
    match PureExpr.cancelFactor? pn pd with
    | some x => .pure x
    | none => .uncheckedDiv (.pure pn) (.pure pd)
  | n => .uncheckedDiv n (.pure pd)

/-- Rebuilds a division node. `known` collects the facts available once both operands have
    evaluated to values; the zero check is dropped exactly when `known` entails that the pure
    divisor `pd` is non-zero, i.e. when the residual guard
    `synthesizeGuardIR known (.nonZero pd)` is trivial. -/
private def Expr.mkDiv (checked : Bool) (known : GuardIR) (n d : Expr) : Expr :=
  match d with
  | .pure pd =>
    if GuardIR.entails known (.nonZero pd) then Expr.mkSafeDiv n pd
    else Expr.rawDiv checked n (.pure pd)
  | d => Expr.rawDiv checked n d

/-- Rebuilds a guard branch: a statically false guard selects the else-branch, a guard whose
    residual `g` under the context is `.top` selects the then-branch. -/
private def Expr.mkIte (staticFalse : Bool) (g : GuardIR) (t f : Expr) : Expr :=
  match staticFalse, g with
  | true, _ => f
  | false, .top => t
  | false, g => .iteGuard g t f

/-- Computable context-sensitive guarded expression optimizer on `Expr`. -/
def optimizeExpr (ctx : GuardIR) (e : Expr) : Expr :=
  match e with
  | .pure p => .pure p
  | .add e₁ e₂ =>
    Expr.mkBin .add .add (optimizeExpr ctx e₁)
      (optimizeExpr (.conj ctx (Expr.postFacts e₁)) e₂)
  | .sub e₁ e₂ =>
    Expr.mkBin .sub .sub (optimizeExpr ctx e₁)
      (optimizeExpr (.conj ctx (Expr.postFacts e₁)) e₂)
  | .mul e₁ e₂ =>
    Expr.mkBin .mul .mul (optimizeExpr ctx e₁)
      (optimizeExpr (.conj ctx (Expr.postFacts e₁)) e₂)
  | .checkedDiv n d =>
    Expr.mkDiv true (.conj (.conj ctx (Expr.postFacts n)) (Expr.postFacts d))
      (optimizeExpr ctx n) (optimizeExpr (.conj ctx (Expr.postFacts n)) d)
  | .uncheckedDiv n d =>
    Expr.mkDiv false (.conj (.conj ctx (Expr.postFacts n)) (Expr.postFacts d))
      (optimizeExpr ctx n) (optimizeExpr (.conj ctx (Expr.postFacts n)) d)
  | .iteGuard g t f =>
    Expr.mkIte (GuardIR.isBot (GuardIR.nf g)) (GuardIR.simplifyUnder ctx g)
      (optimizeExpr (.conj ctx g) t) (optimizeExpr (.conj ctx (.imp g .bot)) f)

/-- Stage-to-Machine-State Bridge Equivalence: `GuardedEquiv (liftEval run) P t₁ t₂` holds
    if and only if `t₁` and `t₂` produce identical concrete outcomes on every state satisfying `P`. -/
theorem liftEval_guardedEquiv_iff {Out : Type*} (run : S → Term → Out)
    (P : S → Prop) (t₁ t₂ : Term) :
    GuardedEquiv (liftEval run) P t₁ t₂ ↔ ∀ s, P s → run s t₁ = run s t₂ := by
  constructor
  · intro h s hs
    have hP : liftEval run P t₁ = liftEval run P t₂ := h P (le_refl P)
    have hEq : (P s ∧ run s t₁ = run s t₁) = (P s ∧ run s t₂ = run s t₁) :=
      congrFun (congrFun hP s) (run s t₁)
    exact (hEq ▸ And.intro hs rfl).2.symm
  · intro h stage hst
    funext s out
    apply propext
    show (stage s ∧ run s t₁ = out) ↔ (stage s ∧ run s t₂ = out)
    constructor
    · rintro ⟨hs, he⟩
      exact ⟨hs, (h s (hst s hs)) ▸ he⟩
    · rintro ⟨hs, he⟩
      exact ⟨hs, (h s (hst s hs)).symm ▸ he⟩

/-- Denotational Compatibility of `Expr.add` with `liftEval evalExpr`. -/
theorem exprAdd_compatibleOp2 :
    CompatibleOp2 (liftEval evalExpr) Expr.add (liftBinarySem (fun x y => .val (x + y))) := by
  intro stage e₁ e₂
  funext env out
  apply propext
  show (stage env ∧ evalExpr env (.add e₁ e₂) = out) ↔
    ∃ o₁ o₂, (stage env ∧ evalExpr env e₁ = o₁) ∧ (stage env ∧ evalExpr env e₂ = o₂) ∧
      bindOutcome2 (fun x y => .val (x + y)) o₁ o₂ = out
  constructor
  · rintro ⟨hs, he⟩
    exact ⟨_, _, ⟨hs, rfl⟩, ⟨hs, rfl⟩, he⟩
  · rintro ⟨o₁, o₂, ⟨hs, h₁⟩, ⟨-, h₂⟩, hb⟩
    subst h₁ h₂
    exact ⟨hs, hb⟩

/-- Denotational Compatibility of `Expr.checkedDiv` with `liftEval evalExpr`. -/
theorem exprCheckedDiv_compatibleOp2 :
    CompatibleOp2 (liftEval evalExpr) Expr.checkedDiv
      (liftBinarySem (fun x y => if y = 0 then .trap else .val (x / y))) := by
  intro stage e₁ e₂
  funext env out
  apply propext
  show (stage env ∧ evalExpr env (.checkedDiv e₁ e₂) = out) ↔
    ∃ o₁ o₂, (stage env ∧ evalExpr env e₁ = o₁) ∧ (stage env ∧ evalExpr env e₂ = o₂) ∧
      bindOutcome2 (fun x y => if y = 0 then .trap else .val (x / y)) o₁ o₂ = out
  constructor
  · rintro ⟨hs, he⟩
    exact ⟨_, _, ⟨hs, rfl⟩, ⟨hs, rfl⟩, he⟩
  · rintro ⟨o₁, o₂, ⟨hs, h₁⟩, ⟨-, h₂⟩, hb⟩
    subst h₁ h₂
    exact ⟨hs, hb⟩

/-! ### Semantics of the guard normaliser -/

private theorem GuardIR.isTop_iff {g : GuardIR} : GuardIR.isTop g = true ↔ g = .top := by
  cases g <;> simp [GuardIR.isTop]

private theorem GuardIR.isBot_iff {g : GuardIR} : GuardIR.isBot g = true ↔ g = .bot := by
  cases g <;> simp [GuardIR.isBot]

private theorem GuardIR.evalGuard_mkConj (env : Env) (g₁ g₂ : GuardIR) :
    evalGuard env (GuardIR.mkConj g₁ g₂) = (evalGuard env g₁ && evalGuard env g₂) := by
  cases g₁ <;> cases g₂ <;> simp [GuardIR.mkConj, evalGuard]

private theorem GuardIR.evalGuard_mkImp (env : Env) (g₁ g₂ : GuardIR) :
    evalGuard env (GuardIR.mkImp g₁ g₂) = (!evalGuard env g₁ || evalGuard env g₂) := by
  cases g₁ <;> cases g₂ <;> simp [GuardIR.mkImp, evalGuard]

private theorem GuardIR.evalGuard_nf (env : Env) (g : GuardIR) :
    evalGuard env (GuardIR.nf g) = evalGuard env g := by
  induction g with
  | conj g₁ g₂ ih₁ ih₂ => simp only [GuardIR.nf, GuardIR.evalGuard_mkConj, evalGuard, ih₁, ih₂]
  | imp g₁ g₂ ih₁ ih₂ => simp only [GuardIR.nf, GuardIR.evalGuard_mkImp, evalGuard, ih₁, ih₂]
  | _ => rfl

private theorem GuardIR.evalGuard_conj_intro {env : Env} {a b : GuardIR}
    (ha : evalGuard env a = true) (hb : evalGuard env b = true) :
    evalGuard env (.conj a b) = true := by
  simp only [evalGuard, ha, hb, Bool.and_self]

/-- A hypothesis of a context holds wherever the context holds. -/
private theorem GuardIR.hasHyp_sound {env : Env} {c h : GuardIR}
    (hh : GuardIR.hasHyp c h = true) (hc : evalGuard env c = true) :
    evalGuard env h = true := by
  induction c with
  | top => exact absurd hh (by simp [GuardIR.hasHyp])
  | bot => exact absurd hc (by simp [evalGuard])
  | conj c₁ c₂ ih₁ ih₂ =>
    simp only [evalGuard, Bool.and_eq_true] at hc
    simp only [GuardIR.hasHyp, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ih₁ hh hc.1
    · exact ih₂ hh hc.2
  | _ => exact (of_decide_eq_true hh) ▸ hc

private theorem GuardIR.hasHyp_mkConj (g₁ g₂ h : GuardIR) :
    GuardIR.hasHyp (GuardIR.mkConj g₁ g₂) h = (GuardIR.hasHyp g₁ h || GuardIR.hasHyp g₂ h) := by
  cases g₁ <;> cases g₂ <;> simp [GuardIR.mkConj, GuardIR.hasHyp]

/-- Ex falso: a context with the hypothesis `.bot` has every hypothesis. -/
private theorem GuardIR.hasHyp_of_bot {c : GuardIR} (hb : GuardIR.hasHyp c .bot = true)
    (h : GuardIR) : GuardIR.hasHyp c h = true := by
  induction c with
  | top => exact absurd hb (by simp [GuardIR.hasHyp])
  | bot => rfl
  | conj c₁ c₂ ih₁ ih₂ =>
    simp only [GuardIR.hasHyp, Bool.or_eq_true] at hb ⊢
    exact hb.imp ih₁ ih₂
  | _ => exact absurd hb (by simp [GuardIR.hasHyp])

private theorem GuardIR.mkConj_top_right (g : GuardIR) : GuardIR.mkConj g .top = g := by
  cases g <;> rfl

private theorem GuardIR.mkImp_top_right (g : GuardIR) : GuardIR.mkImp g .top = .top := by
  cases g <;> rfl

private theorem GuardIR.mkImp_bot_left (g : GuardIR) : GuardIR.mkImp .bot g = .top := by
  cases g <;> rfl

private theorem GuardIR.mkConj_eq_top {g₁ g₂ : GuardIR} (h : GuardIR.mkConj g₁ g₂ = .top) :
    g₁ = .top ∧ g₂ = .top := by
  cases g₁ <;> cases g₂ <;> simp [GuardIR.mkConj] at h ⊢

private theorem GuardIR.mkImp_eq_top {g₁ g₂ : GuardIR} (h : GuardIR.mkImp g₁ g₂ = .top) :
    g₂ = .top ∨ g₁ = .bot := by
  cases g₁ <;> cases g₂ <;> simp [GuardIR.mkImp] at h ⊢

private theorem GuardIR.residual_of_hasHyp_bot {c : GuardIR}
    (hb : GuardIR.hasHyp c .bot = true) (g : GuardIR) : GuardIR.residual c g = .top := by
  induction g generalizing c with
  | top => rfl
  | conj g₁ g₂ ih₁ ih₂ =>
    have h₂ : GuardIR.hasHyp (.conj c g₁) .bot = true := by
      simp only [GuardIR.hasHyp, hb, Bool.true_or]
    simp only [GuardIR.residual, ih₁ hb, ih₂ h₂]
    rfl
  | imp g₁ g₂ _ _ => simp only [GuardIR.residual, GuardIR.hasHyp_of_bot hb, ↓reduceIte]
  | _ => simp only [GuardIR.residual, GuardIR.hasHyp_of_bot hb, ↓reduceIte]

/-- Wherever the context holds, the residual evaluates exactly like the original target. -/
private theorem GuardIR.evalGuard_residual {env : Env} {c : GuardIR}
    (hc : evalGuard env c = true) (g : GuardIR) :
    evalGuard env (GuardIR.residual c g) = evalGuard env g := by
  induction g generalizing c with
  | top => rfl
  | conj g₁ g₂ ih₁ ih₂ =>
    simp only [GuardIR.residual, GuardIR.evalGuard_mkConj, evalGuard, ih₁ hc]
    cases h₁ : evalGuard env g₁ with
    | false => rfl
    | true => rw [ih₂ (GuardIR.evalGuard_conj_intro hc h₁)]
  | imp g₁ g₂ _ ih₂ =>
    simp only [GuardIR.residual]
    split
    · next hh => exact (GuardIR.hasHyp_sound hh hc).symm
    · simp only [GuardIR.evalGuard_mkImp, evalGuard]
      cases h₁ : evalGuard env g₁ with
      | false => rfl
      | true => rw [ih₂ (GuardIR.evalGuard_conj_intro hc h₁)]
  | _ =>
    simp only [GuardIR.residual]
    split
    · next hh => exact (GuardIR.hasHyp_sound hh hc).symm
    · rfl

/-- A target that is fully discharged stays discharged when the context gains hypotheses. -/
private theorem GuardIR.residual_top_mono {c c' : GuardIR}
    (hle : ∀ h, GuardIR.hasHyp c h = true → GuardIR.hasHyp c' h = true) (g : GuardIR)
    (hg : GuardIR.residual c g = .top) : GuardIR.residual c' g = .top := by
  induction g generalizing c c' with
  | top => rfl
  | conj g₁ g₂ ih₁ ih₂ =>
    simp only [GuardIR.residual] at hg ⊢
    obtain ⟨h₁, h₂⟩ := GuardIR.mkConj_eq_top hg
    have hle' : ∀ h, GuardIR.hasHyp (.conj c g₁) h = true →
        GuardIR.hasHyp (.conj c' g₁) h = true := by
      intro h
      simp only [GuardIR.hasHyp, Bool.or_eq_true]
      exact Or.imp_left (hle h)
    rw [ih₁ hle h₁, ih₂ hle' h₂]
    rfl
  | imp g₁ g₂ _ ih₂ =>
    simp only [GuardIR.residual] at hg ⊢
    have hle' : ∀ h, GuardIR.hasHyp (.conj c g₁) h = true →
        GuardIR.hasHyp (.conj c' g₁) h = true := by
      intro h
      simp only [GuardIR.hasHyp, Bool.or_eq_true]
      exact Or.imp_left (hle h)
    split at hg
    · next hh => rw [ite_eq_left (hle _ hh)]
    · split
      · rfl
      · rcases GuardIR.mkImp_eq_top hg with h₂ | h₁
        · rw [ih₂ hle' h₂, GuardIR.mkImp_top_right]
        · subst h₁
          exact GuardIR.mkImp_bot_left _
  | _ =>
    simp only [GuardIR.residual] at hg ⊢
    split at hg
    · next hh => rw [ite_eq_left (hle _ hh)]
    · exact absurd hg (by simp)

private theorem GuardIR.evalGuard_wrapImp (env : Env) (hyp r : GuardIR) :
    evalGuard env (GuardIR.wrapImp hyp r) = (!evalGuard env hyp || evalGuard env r) := by
  cases hyp <;> rfl

/-- The synthesized guard is `.top` exactly when the target simplifies to `.top`. -/
private theorem isTop_synthesizeGuardIR (a b : GuardIR) :
    GuardIR.isTop (synthesizeGuardIR a b) = GuardIR.isTop (GuardIR.simplifyUnder a b) := by
  unfold synthesizeGuardIR
  cases GuardIR.simplifyUnder a b <;>
    first
      | rfl
      | (cases GuardIR.residual .top (GuardIR.nf a) <;> rfl)

/-- The optimizer's entailment test is exactly triviality of the synthesized guard. -/
private theorem GuardIR.entails_eq (ctx g : GuardIR) :
    GuardIR.entails ctx g = GuardIR.isTop (synthesizeGuardIR ctx g) :=
  (isTop_synthesizeGuardIR ctx g).symm

private theorem evalGuard_simplifyUnder {env : Env} {ctx : GuardIR}
    (hctx : evalGuard env ctx = true) (g : GuardIR) :
    evalGuard env (GuardIR.simplifyUnder ctx g) = evalGuard env g := by
  unfold GuardIR.simplifyUnder
  rw [GuardIR.evalGuard_residual (by rw [GuardIR.evalGuard_nf]; exact hctx), GuardIR.evalGuard_nf]

/-- Pointwise Boolean semantics of the synthesized guard: `a → b`. -/
private theorem evalGuard_synthesizeGuardIR (env : Env) (a b : GuardIR) :
    evalGuard env (synthesizeGuardIR a b) = (!evalGuard env a || evalGuard env b) := by
  have hb : evalGuard env a = true →
      evalGuard env (GuardIR.simplifyUnder a b) = evalGuard env b :=
    fun ha => evalGuard_simplifyUnder ha b
  have ha : evalGuard env (GuardIR.residual .top (GuardIR.nf a)) = evalGuard env a := by
    rw [GuardIR.evalGuard_residual rfl, GuardIR.evalGuard_nf]
  unfold synthesizeGuardIR
  generalize GuardIR.simplifyUnder a b = r at hb ⊢
  cases r with
  | top =>
    cases hA : evalGuard env a with
    | false => rfl
    | true => exact hb hA
  | _ =>
    simp only [GuardIR.evalGuard_wrapImp, ha]
    cases hA : evalGuard env a with
    | false => rfl
    | true => exact hb hA

/-- A `.nonZero` target that is a hypothesis of the (normalised) context is discharged. -/
private theorem synthesizeGuardIR_eq_top_of_hasHyp {a : GuardIR} {p : PureExpr}
    (h : GuardIR.hasHyp (GuardIR.nf a) (.nonZero p) = true) :
    synthesizeGuardIR a (.nonZero p) = .top := by
  unfold synthesizeGuardIR GuardIR.simplifyUnder
  simp only [GuardIR.nf, GuardIR.residual, h, ↓reduceIte]

/-- Categorical Realization of `synthesizeGuardIR`: Denotation commutes with abstract `synthesizeGuard`. -/
theorem synthesizeGuardIR_denote (a b : GuardIR) :
    denoteGuard (synthesizeGuardIR a b) = synthesizeGuard (denoteGuard a) (denoteGuard b) := by
  funext env
  apply propext
  show evalGuard env (synthesizeGuardIR a b) = true ↔
    (evalGuard env a = true → evalGuard env b = true)
  rw [evalGuard_synthesizeGuardIR]
  cases evalGuard env a <;> cases evalGuard env b <;> decide

/-- Universal Property (Heyting Adjunction) of `synthesizeGuardIR` in `Env → Prop`. -/
theorem synthesizeGuardIR_universal (a b : GuardIR) (g : Env → Prop) :
    denoteGuard a ⊓ g ≤ denoteGuard b ↔ g ≤ denoteGuard (synthesizeGuardIR a b) := by
  rw [synthesizeGuardIR_denote]
  exact synthesizeGuard_adjunction (denoteGuard a) (denoteGuard b) g

/-- Syntactic Self-Discharge: Synthesizing a non-zero guard already present in context yields `.top`. -/
theorem synthesizeGuardIR_discharge_self (p : PureExpr) :
    synthesizeGuardIR (.nonZero p) (.nonZero p) = .top := by
  apply synthesizeGuardIR_eq_top_of_hasHyp
  simp only [GuardIR.nf, GuardIR.hasHyp, decide_true]

/-! ### Operational soundness of the expression optimizer -/

private theorem bindOutcome2_congr {f : Int → Int → Outcome} {o₁ o₁' o₂ o₂' : Outcome}
    (h₁ : o₁' = o₁) (h₂ : ∀ n, o₁ = .val n → o₂' = o₂) :
    bindOutcome2 f o₁' o₂' = bindOutcome2 f o₁ o₂ := by
  subst h₁
  cases o₁' with
  | val n => rw [h₂ n rfl]
  | trap => rfl
  | ub => rfl

/-- Euclidean cancellation `(x * d) / d = x = (d * x) / d` for a non-zero divisor. -/
private theorem PureExpr.cancelFactor?_eval {env : Env} {num d x : PureExpr}
    (h : PureExpr.cancelFactor? num d = some x) (hd : evalPure env d ≠ 0) :
    evalPure env num / evalPure env d = evalPure env x := by
  unfold PureExpr.cancelFactor? at h
  split at h
  · split at h
    · next hb =>
      cases h
      subst hb
      exact Int.mul_ediv_cancel _ hd
    · split at h
      · next ha =>
        cases h
        subst ha
        exact Int.mul_ediv_cancel_left _ hd
      · cases h
  · cases h

private theorem Expr.evalExpr_of_asPure {env : Env} {e : Expr} {p : PureExpr}
    (h : Expr.asPure? e = some p) : evalExpr env e = .val (evalPure env p) := by
  induction e generalizing p with
  | pure q =>
    cases h
    rfl
  | add e₁ e₂ ih₁ ih₂ | sub e₁ e₂ ih₁ ih₂ | mul e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.asPure?] at h
    cases h₁ : Expr.asPure? e₁ with
    | none => simp only [h₁] at h; cases h
    | some p₁ =>
      cases h₂ : Expr.asPure? e₂ with
      | none => simp only [h₁, h₂] at h; cases h
      | some p₂ =>
        simp only [h₁, h₂] at h
        cases h
        simp only [evalExpr, ih₁ h₁, ih₂ h₂, evalPure]
  | _ => cases h

/-- The facts recorded by `Expr.postFacts` hold whenever the expression evaluates to a value. -/
private theorem Expr.evalGuard_postFacts {env : Env} {e : Expr} {v : Int}
    (h : evalExpr env e = .val v) : evalGuard env (Expr.postFacts e) = true := by
  induction e generalizing v with
  | pure p => rfl
  | add e₁ e₂ ih₁ ih₂ | sub e₁ e₂ ih₁ ih₂ | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalExpr] at h
    cases h₁ : evalExpr env e₁ with
    | val a =>
      cases h₂ : evalExpr env e₂ with
      | val b => simp only [Expr.postFacts, evalGuard, ih₁ h₁, ih₂ h₂, Bool.and_self]
      | trap => simp only [h₁, h₂] at h; cases h
      | ub => simp only [h₁, h₂] at h; cases h
    | trap => simp only [h₁] at h; cases h
    | ub => simp only [h₁] at h; cases h
  | checkedDiv n d ihn ihd | uncheckedDiv n d ihn ihd =>
    simp only [evalExpr] at h
    cases h₁ : evalExpr env n with
    | val a =>
      cases h₂ : evalExpr env d with
      | val b =>
        simp only [h₁, h₂] at h
        have hb : b ≠ 0 := by
          intro hb
          simp only [hb, ↓reduceIte] at h
          cases h
        simp only [Expr.postFacts, evalGuard, ihn h₁, ihd h₂, Bool.and_self, Bool.true_and]
        cases hp : Expr.asPure? d with
        | none => rfl
        | some pd =>
          have hv := Expr.evalExpr_of_asPure (env := env) hp
          rw [h₂] at hv
          cases hv
          exact decide_eq_true hb
      | trap => simp only [h₁, h₂] at h; cases h
      | ub => simp only [h₁, h₂] at h; cases h
    | trap => simp only [h₁] at h; cases h
    | ub => simp only [h₁] at h; cases h
  | iteGuard g t f _ _ => rfl

private theorem Expr.evalExpr_mkBin {env : Env} {pop : PureExpr → PureExpr → PureExpr}
    {eop : Expr → Expr → Expr}
    (hop : ∀ p₁ p₂, evalExpr env (eop (.pure p₁) (.pure p₂)) = .val (evalPure env (pop p₁ p₂)))
    (e₁ e₂ : Expr) :
    evalExpr env (Expr.mkBin pop eop e₁ e₂) = evalExpr env (eop e₁ e₂) := by
  unfold Expr.mkBin
  split
  · exact (hop _ _).symm
  · rfl

private theorem Expr.evalExpr_mkSafeDiv {env : Env} {n : Expr} {pd : PureExpr}
    (hd : ∀ a, evalExpr env n = .val a → evalPure env pd ≠ 0) :
    evalExpr env (Expr.mkSafeDiv n pd) = evalExpr env (.uncheckedDiv n (.pure pd)) := by
  unfold Expr.mkSafeDiv
  split
  · next pn =>
    have hd' := hd _ rfl
    split
    · next x hx =>
      simp only [evalExpr, ite_eq_right hd', PureExpr.cancelFactor?_eval hx hd']
    · rfl
  · rfl

private theorem Expr.evalExpr_rawDiv_congr {env : Env} (checked : Bool) {n n' d d' : Expr}
    (hn : evalExpr env n' = evalExpr env n)
    (hd : ∀ a, evalExpr env n = .val a → evalExpr env d' = evalExpr env d) :
    evalExpr env (Expr.rawDiv checked n' d') = evalExpr env (Expr.rawDiv checked n d) := by
  cases checked with
  | true =>
    exact bindOutcome2_congr (f := fun x y => if y = 0 then .trap else .val (x / y)) hn hd
  | false =>
    exact bindOutcome2_congr (f := fun x y => if y = 0 then .ub else .val (x / y)) hn hd

private theorem Expr.evalExpr_uncheckedDiv_eq_rawDiv {env : Env} (checked : Bool) {n : Expr}
    {pd : PureExpr} (hnz : ∀ a, evalExpr env n = .val a → evalPure env pd ≠ 0) :
    evalExpr env (.uncheckedDiv n (.pure pd)) =
      evalExpr env (Expr.rawDiv checked n (.pure pd)) := by
  cases checked with
  | false => rfl
  | true =>
    simp only [Expr.rawDiv, evalExpr]
    cases h : evalExpr env n with
    | val a => simp only [ite_eq_right (hnz a h)]
    | trap => rfl
    | ub => rfl

/-- Soundness of the optimizer's non-zero query, obtained from the universal property
    (Heyting adjunction) of `synthesizeGuardIR`: a trivial residual guard means that the
    context already forces the divisor to be non-zero. -/
private theorem evalPure_ne_zero_of_entails {env : Env} {K : GuardIR} {pd : PureExpr}
    (h : GuardIR.entails K (.nonZero pd) = true)
    (hK : evalGuard env K = true) : evalPure env pd ≠ 0 := by
  have htop : synthesizeGuardIR K (.nonZero pd) = .top :=
    GuardIR.isTop_iff.mp (GuardIR.entails_eq K (.nonZero pd) ▸ h)
  have hle : denoteGuard K ⊓ denoteGuard K ≤ denoteGuard (.nonZero pd) :=
    (synthesizeGuardIR_universal K (.nonZero pd) (denoteGuard K)).mpr
      (by rw [htop]; intro _ _; rfl)
  exact of_decide_eq_true (hle env (And.intro hK hK))

private theorem Expr.evalExpr_mkDiv {env : Env} (checked : Bool) {K : GuardIR}
    {n n' d d' : Expr}
    (hn : evalExpr env n' = evalExpr env n)
    (hd : ∀ a, evalExpr env n = .val a → evalExpr env d' = evalExpr env d)
    (hK : ∀ a b, evalExpr env n = .val a → evalExpr env d = .val b → evalGuard env K = true) :
    evalExpr env (Expr.mkDiv checked K n' d') = evalExpr env (Expr.rawDiv checked n d) := by
  have hraw : evalExpr env (Expr.rawDiv checked n' d') =
      evalExpr env (Expr.rawDiv checked n d) := Expr.evalExpr_rawDiv_congr checked hn hd
  unfold Expr.mkDiv
  split
  · next pd =>
    split
    · next hk =>
      have hnz : ∀ a, evalExpr env n' = .val a → evalPure env pd ≠ 0 := by
        intro a ha
        rw [hn] at ha
        exact evalPure_ne_zero_of_entails hk (hK a _ ha (hd a ha).symm)
      rw [← hraw, Expr.evalExpr_mkSafeDiv hnz]
      exact Expr.evalExpr_uncheckedDiv_eq_rawDiv checked hnz
    · exact hraw
  · exact hraw

private theorem Expr.evalExpr_mkIte {env : Env} {sf : Bool} {g r : GuardIR}
    {t t' f f' : Expr}
    (hsf : sf = true → evalGuard env g = false)
    (hr : evalGuard env r = evalGuard env g)
    (ht : evalGuard env g = true → evalExpr env t' = evalExpr env t)
    (hf : evalGuard env g = false → evalExpr env f' = evalExpr env f) :
    evalExpr env (Expr.mkIte sf r t' f') = evalExpr env (.iteGuard g t f) := by
  have key : evalExpr env (.iteGuard r t' f') = evalExpr env (.iteGuard g t f) := by
    simp only [evalExpr, hr]
    cases hg : evalGuard env g with
    | true => simp only [↓reduceIte]; exact ht hg
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hf hg
  unfold Expr.mkIte
  split
  · have hg := hsf rfl
    rw [hf hg]
    simp only [evalExpr, hg, Bool.false_eq_true, ↓reduceIte]
  · have hg : evalGuard env g = true := by rw [← hr]; rfl
    rw [ht hg]
    simp only [evalExpr, hg, ↓reduceIte]
  · exact key

/-- Operational soundness of `optimizeExpr`, by structural induction on the expression. -/
private theorem optimizeExpr_sound_aux (e : Expr) :
    ∀ (ctx : GuardIR) (env : Env), evalGuard env ctx = true →
      evalExpr env (optimizeExpr ctx e) = evalExpr env e := by
  induction e with
  | pure p => intro ctx env _; rfl
  | add e₁ e₂ ih₁ ih₂ =>
    intro ctx env hctx
    rw [optimizeExpr, Expr.evalExpr_mkBin (fun _ _ => rfl)]
    exact bindOutcome2_congr (f := fun x y => .val (x + y)) (ih₁ ctx env hctx)
      (fun a ha => ih₂ _ env (GuardIR.evalGuard_conj_intro hctx (Expr.evalGuard_postFacts ha)))
  | sub e₁ e₂ ih₁ ih₂ =>
    intro ctx env hctx
    rw [optimizeExpr, Expr.evalExpr_mkBin (fun _ _ => rfl)]
    exact bindOutcome2_congr (f := fun x y => .val (x - y)) (ih₁ ctx env hctx)
      (fun a ha => ih₂ _ env (GuardIR.evalGuard_conj_intro hctx (Expr.evalGuard_postFacts ha)))
  | mul e₁ e₂ ih₁ ih₂ =>
    intro ctx env hctx
    rw [optimizeExpr, Expr.evalExpr_mkBin (fun _ _ => rfl)]
    exact bindOutcome2_congr (f := fun x y => .val (x * y)) (ih₁ ctx env hctx)
      (fun a ha => ih₂ _ env (GuardIR.evalGuard_conj_intro hctx (Expr.evalGuard_postFacts ha)))
  | checkedDiv n d ihn ihd =>
    intro ctx env hctx
    rw [optimizeExpr]
    exact Expr.evalExpr_mkDiv true (ihn ctx env hctx)
      (fun a ha => ihd _ env (GuardIR.evalGuard_conj_intro hctx (Expr.evalGuard_postFacts ha)))
      (fun a b ha hb => GuardIR.evalGuard_conj_intro
        (GuardIR.evalGuard_conj_intro hctx (Expr.evalGuard_postFacts ha))
        (Expr.evalGuard_postFacts hb))
  | uncheckedDiv n d ihn ihd =>
    intro ctx env hctx
    rw [optimizeExpr]
    exact Expr.evalExpr_mkDiv false (ihn ctx env hctx)
      (fun a ha => ihd _ env (GuardIR.evalGuard_conj_intro hctx (Expr.evalGuard_postFacts ha)))
      (fun a b ha hb => GuardIR.evalGuard_conj_intro
        (GuardIR.evalGuard_conj_intro hctx (Expr.evalGuard_postFacts ha))
        (Expr.evalGuard_postFacts hb))
  | iteGuard g t f iht ihf =>
    intro ctx env hctx
    rw [optimizeExpr]
    refine Expr.evalExpr_mkIte ?_ (evalGuard_simplifyUnder hctx g) ?_ ?_
    · intro hsf
      rw [← GuardIR.evalGuard_nf, GuardIR.isBot_iff.mp hsf]
      rfl
    · intro hg
      exact iht _ env (GuardIR.evalGuard_conj_intro hctx hg)
    · intro hg
      refine ihf _ env (GuardIR.evalGuard_conj_intro hctx ?_)
      simp only [evalGuard, hg, Bool.not_false, Bool.true_or]

/-- Stage-Guarded Soundness of `optimizeExpr` via `GuardedEquiv` and `liftEval`. -/
theorem optimizeExpr_guardedEquiv (ctx : GuardIR) (e : Expr) :
    GuardedEquiv (liftEval evalExpr) (denoteGuard ctx) (optimizeExpr ctx e) e := by
  exact (liftEval_guardedEquiv_iff evalExpr (denoteGuard ctx) (optimizeExpr ctx e) e).mpr
    (fun env h => optimizeExpr_sound_aux e ctx env h)

/-- Concrete Operational Soundness of `optimizeExpr`: Whenever `evalGuard env ctx = true`,
    the optimized expression evaluates to the exact same `Outcome` as the original expression. -/
theorem optimizeExpr_sound (ctx : GuardIR) (e : Expr) (env : Env) :
    evalGuard env ctx = true → evalExpr env (optimizeExpr ctx e) = evalExpr env e := by
  exact optimizeExpr_sound_aux e ctx env

/-! ### Static counts and runtime check cost -/

private theorem Expr.count_mkBin {cnt : Expr → Nat} {pop : PureExpr → PureExpr → PureExpr}
    {eop : Expr → Expr → Expr} (hpure : ∀ p, cnt (.pure p) = 0)
    (hop : ∀ a b, cnt (eop a b) = cnt a + cnt b) (e₁ e₂ : Expr) :
    cnt (Expr.mkBin pop eop e₁ e₂) = cnt e₁ + cnt e₂ := by
  unfold Expr.mkBin
  split
  · simp only [hpure]
  · exact hop _ _

private theorem Expr.count_mkSafeDiv {cnt : Expr → Nat} (hpure : ∀ p, cnt (.pure p) = 0)
    (hdiv : ∀ a b, cnt (.uncheckedDiv a b) = cnt a + cnt b) (n : Expr) (pd : PureExpr) :
    cnt (Expr.mkSafeDiv n pd) = cnt n := by
  unfold Expr.mkSafeDiv
  split
  · split
    · simp only [hpure]
    · simp only [hdiv, hpure]
  · simp only [hdiv, hpure, Nat.add_zero]

/-- An expression without checked divisions or guard branches performs no runtime checks. -/
private theorem execCheckCost_eq_zero {env : Env} {e : Expr}
    (h₁ : checkedDivCount e = 0) (h₂ : guardBranchCount e = 0) : execCheckCost env e = 0 := by
  induction e with
  | pure p => rfl
  | add e₁ e₂ ih₁ ih₂ | sub e₁ e₂ ih₁ ih₂ | mul e₁ e₂ ih₁ ih₂ | uncheckedDiv e₁ e₂ ih₁ ih₂ =>
    simp only [checkedDivCount, Nat.add_eq_zero_iff] at h₁
    simp only [guardBranchCount, Nat.add_eq_zero_iff] at h₂
    simp only [execCheckCost, ih₁ h₁.1 h₂.1, ih₂ h₁.2 h₂.2]
    cases evalExpr env e₁ <;> rfl
  | checkedDiv e₁ e₂ _ _ =>
    simp only [checkedDivCount] at h₁
    omega
  | iteGuard g t f _ _ =>
    simp only [guardBranchCount] at h₂
    omega

private theorem execCheckCost_checkedDiv_add_pure (env : Env) (x d y : PureExpr) :
    execCheckCost env (.add (.checkedDiv (.pure x) (.pure d)) (.pure y)) = 1 := by
  simp only [execCheckCost, evalExpr, ↓reduceIte]
  cases (if evalPure env d = 0 then Outcome.trap
    else Outcome.val (evalPure env x / evalPure env d)) <;> rfl

private theorem execCheckCost_mkDualDivExpr {env : Env} (x y : PureExpr) {d : PureExpr}
    (h : evalPure env d ≠ 0) : execCheckCost env (mkDualDivExpr x y d) = 2 := by
  simp only [mkDualDivExpr, execCheckCost, evalExpr, ite_eq_right h, ↓reduceIte]

private theorem evalExpr_mkDualDivExpr_trap {env : Env} (x y : PureExpr) {d : PureExpr}
    (h : evalPure env d = 0) : evalExpr env (mkDualDivExpr x y d) = .trap := by
  simp only [mkDualDivExpr, evalExpr, h, ↓reduceIte]

/-- Known-Context Check Elimination: Under context `v₀ ≠ 0`, `optimizeExpr` eliminates all
    checked divisions, introduces zero runtime guard branches, and incurs zero runtime check cost. -/
theorem optimizeExpr_known_ctx_elim (env : Env) :
    checkedDivCount (optimizeExpr (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
      guardBranchCount (optimizeExpr (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
      execCheckCost env (optimizeExpr (.nonZero (.var 0)) m1BenchExpr) = 0 := by
  have hopt : optimizeExpr (.nonZero (.var 0)) m1BenchExpr =
      .add (.uncheckedDiv (.pure (.var 1)) (.pure (.var 0))) (.pure (.var 2)) := by decide
  rw [hopt]
  exact ⟨rfl, rfl, execCheckCost_eq_zero rfl rfl⟩

/-- Guarded Algebraic Cancellation: Under context `v₀ ≠ 0`, `(v₁ * v₀) / v₀` eliminates division completely. -/
theorem optimizeExpr_cancel_div :
    divOpCount (optimizeExpr (.nonZero (.var 0)) m1CancelExpr) = 0 := by
  decide

/-- Unknown-Context Guard Deduplication: Under trivial context `.top`, `optimizeExpr` reduces
    runtime check cost on `m1BenchExpr` from `2` down to at most `1` whenever `v₀ ≠ 0`. -/
theorem optimizeExpr_unknown_ctx_dedup (env : Env) (h : env 0 ≠ 0) :
    execCheckCost env (optimizeExpr .top m1BenchExpr) ≤ 1 ∧
      execCheckCost env m1BenchExpr = 2 := by
  have hopt : optimizeExpr .top m1BenchExpr =
      .add (.checkedDiv (.pure (.var 1)) (.pure (.var 0))) (.pure (.var 2)) := by decide
  rw [hopt, execCheckCost_checkedDiv_add_pure]
  exact ⟨Nat.le_refl 1, execCheckCost_mkDualDivExpr (.var 1) (.var 2) (d := .var 0) h⟩

/-- Trap Preservation (Negative Safety Test): Under trivial context `.top`, when `v₀ = 0`,
    `optimizeExpr .top m1BenchExpr` still safely traps rather than triggering `.ub` or fabricating a value. -/
theorem optimizeExpr_zero_div_trap (env : Env) (h : env 0 = 0) :
    evalExpr env (optimizeExpr .top m1BenchExpr) = .trap := by
  rw [optimizeExpr_sound .top m1BenchExpr env rfl]
  exact evalExpr_mkDualDivExpr_trap (.var 1) (.var 2) (d := .var 0) h

/-- Right-Top Residual Normalization: Synthesizing `.top` from any context `a` yields `.top`. -/
theorem synthesizeGuardIR_top_right (a : GuardIR) :
    synthesizeGuardIR a .top = .top := by
  rfl

/-- Left-Bottom Residual Normalization: Synthesizing any target `b` from inconsistent context `.bot` yields `.top`. -/
theorem synthesizeGuardIR_bot_left (b : GuardIR) :
    synthesizeGuardIR .bot b = .top := by
  unfold synthesizeGuardIR GuardIR.simplifyUnder
  rw [show GuardIR.nf .bot = .bot from rfl, GuardIR.residual_of_hasHyp_bot (c := .bot) rfl]

/-- Top-Antecedent Atomic Normalization: Synthesizing `.nonZero p` from trivial context `.top`
    returns `.nonZero p` directly rather than an unsimplified `.imp .top (.nonZero p)` wrapper. -/
theorem synthesizeGuardIR_top_left_nonZero (p : PureExpr) :
    synthesizeGuardIR .top (.nonZero p) = .nonZero p := by
  rfl

/-- Left Conjunctive Context Discharge: Synthesizing `.nonZero p` when `.nonZero p` appears on the
    left of a conjunctive context yields `.top`. -/
theorem synthesizeGuardIR_discharge_conj_left (p : PureExpr) (rest : GuardIR) :
    synthesizeGuardIR (.conj (.nonZero p) rest) (.nonZero p) = .top := by
  apply synthesizeGuardIR_eq_top_of_hasHyp
  simp only [GuardIR.nf, GuardIR.hasHyp_mkConj, GuardIR.hasHyp, decide_true, Bool.true_or]

/-- Right Conjunctive Context Discharge: Synthesizing `.nonZero p` when `.nonZero p` appears on the
    right of a conjunctive context yields `.top`. -/
theorem synthesizeGuardIR_discharge_conj_right (rest : GuardIR) (p : PureExpr) :
    synthesizeGuardIR (.conj rest (.nonZero p)) (.nonZero p) = .top := by
  apply synthesizeGuardIR_eq_top_of_hasHyp
  simp only [GuardIR.nf, GuardIR.hasHyp_mkConj, GuardIR.hasHyp, decide_true, Bool.or_true]

/-- Duplicate Conjunctive Target Normalization: Synthesizing `.conj (.nonZero p) (.nonZero p)` from
    `.top` deduplicates the residual guard to `.nonZero p`. -/
theorem synthesizeGuardIR_dedup_conj (p : PureExpr) :
    synthesizeGuardIR .top (.conj (.nonZero p) (.nonZero p)) = .nonZero p := by
  simp only [synthesizeGuardIR, GuardIR.simplifyUnder, GuardIR.nf, GuardIR.mkConj,
    GuardIR.residual, GuardIR.hasHyp, GuardIR.wrapImp, decide_true, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte]

/-! ### Symbolic evaluation of the optimizer on the parametric shapes -/

/-- For a `.nonZero` target the optimizer's query is plain hypothesis lookup. -/
private theorem GuardIR.entails_nonZero (K : GuardIR) (pd : PureExpr) :
    GuardIR.entails K (.nonZero pd) = GuardIR.hasHyp (GuardIR.nf K) (.nonZero pd) := by
  show GuardIR.isTop
    (if GuardIR.hasHyp (GuardIR.nf K) (.nonZero pd) = true then GuardIR.top
     else .nonZero pd) = _
  cases GuardIR.hasHyp (GuardIR.nf K) (.nonZero pd) <;> rfl

private theorem Expr.mkBin_pure_pure (pop : PureExpr → PureExpr → PureExpr)
    (eop : Expr → Expr → Expr) (p q : PureExpr) :
    Expr.mkBin pop eop (.pure p) (.pure q) = .pure (pop p q) := rfl

private theorem Expr.mkSafeDiv_pure_mul_right (x d : PureExpr) :
    Expr.mkSafeDiv (.pure (.mul x d)) d = .pure x := by
  simp only [Expr.mkSafeDiv, PureExpr.cancelFactor?, ↓reduceIte]

private theorem Expr.mkSafeDiv_pure_mul_left (x d : PureExpr) :
    ∃ z, Expr.mkSafeDiv (.pure (.mul d x)) d = .pure z :=
  if h : x = d then
    ⟨d, by simp only [Expr.mkSafeDiv, PureExpr.cancelFactor?, h, ↓reduceIte]⟩
  else
    ⟨x, by simp only [Expr.mkSafeDiv, PureExpr.cancelFactor?, h, ↓reduceIte]⟩

/-- A checked division by a pure divisor whose non-zeroness is a hypothesis of the context
    is lowered by `Expr.mkSafeDiv`. -/
private theorem optimizeExpr_checkedDiv_pure_of_hasHyp {ctx : GuardIR} (num d : PureExpr)
    (h : GuardIR.hasHyp (GuardIR.nf ctx) (.nonZero d) = true) :
    optimizeExpr ctx (.checkedDiv (.pure num) (.pure d)) = Expr.mkSafeDiv (.pure num) d := by
  simp only [optimizeExpr, Expr.postFacts, Expr.mkDiv, GuardIR.entails_nonZero,
    GuardIR.nf, GuardIR.mkConj_top_right, h, ↓reduceIte]

private theorem optimizeExpr_top_mkDualDivExpr (x y d : PureExpr) :
    optimizeExpr .top (mkDualDivExpr x y d) =
      .add (.checkedDiv (.pure x) (.pure d)) (.pure y) := by
  simp only [mkDualDivExpr, optimizeExpr, Expr.postFacts, Expr.asPure?, Expr.mkBin, Expr.mkDiv,
    GuardIR.entails_nonZero, GuardIR.nf, GuardIR.mkConj, GuardIR.hasHyp,
    Expr.mkSafeDiv_pure_mul_right, Expr.rawDiv, decide_true, Bool.false_eq_true, ↓reduceIte]

private theorem optimizeExpr_nonZero_mkDualDivExpr (x y d : PureExpr) :
    optimizeExpr (.nonZero d) (mkDualDivExpr x y d) =
      Expr.mkBin .add .add (Expr.mkSafeDiv (.pure x) d) (.pure y) := by
  simp only [mkDualDivExpr, optimizeExpr, Expr.postFacts, Expr.asPure?, Expr.mkBin_pure_pure,
    Expr.mkDiv, GuardIR.entails_nonZero, GuardIR.nf, GuardIR.mkConj, GuardIR.hasHyp,
    Expr.mkSafeDiv_pure_mul_right, decide_true, Bool.or_true, ↓reduceIte]

/-- Parametric Checked-Division Elimination: For arbitrary pure operands `num, d` and extra context `extra`,
    `optimizeExpr` eliminates `.checkedDiv (.pure num) (.pure d)` under `.nonZero d` and conjunctive
    contexts containing `.nonZero d` with zero guard branches and zero runtime check cost. -/
theorem optimizeExpr_elim_checkedDiv_param (num d : PureExpr) (extra : GuardIR) (env : Env) :
    checkedDivCount (optimizeExpr (.nonZero d) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      checkedDivCount (optimizeExpr (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      checkedDivCount (optimizeExpr (.conj extra (.nonZero d)) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      guardBranchCount (optimizeExpr (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      execCheckCost env (optimizeExpr (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 := by
  have h₁ : GuardIR.hasHyp (GuardIR.nf (.nonZero d)) (.nonZero d) = true := by
    simp only [GuardIR.nf, GuardIR.hasHyp, decide_true]
  have h₂ : GuardIR.hasHyp (GuardIR.nf (.conj (.nonZero d) extra)) (.nonZero d) = true := by
    simp only [GuardIR.nf, GuardIR.hasHyp_mkConj, GuardIR.hasHyp, decide_true, Bool.true_or]
  have h₃ : GuardIR.hasHyp (GuardIR.nf (.conj extra (.nonZero d))) (.nonZero d) = true := by
    simp only [GuardIR.nf, GuardIR.hasHyp_mkConj, GuardIR.hasHyp, decide_true, Bool.or_true]
  have hc : checkedDivCount (Expr.mkSafeDiv (.pure num) d) = 0 :=
    Expr.count_mkSafeDiv (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl) _ _
  have hg : guardBranchCount (Expr.mkSafeDiv (.pure num) d) = 0 :=
    Expr.count_mkSafeDiv (cnt := guardBranchCount) (fun _ => rfl) (fun _ _ => rfl) _ _
  rw [optimizeExpr_checkedDiv_pure_of_hasHyp num d h₁,
    optimizeExpr_checkedDiv_pure_of_hasHyp num d h₂,
    optimizeExpr_checkedDiv_pure_of_hasHyp num d h₃]
  exact ⟨hc, hc, hc, hg, execCheckCost_eq_zero hc hg⟩

/-- Parametric Guarded Algebraic Cancellation: Under `.nonZero d`, both `(x * d) / d` and `(d * x) / d`
    eliminate division completely for arbitrary `PureExpr` operands `x, d`. -/
theorem optimizeExpr_cancel_div_param (x d : PureExpr) :
    divOpCount (optimizeExpr (.nonZero d) (mkCancelExpr x d)) = 0 ∧
      divOpCount (optimizeExpr (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d))) = 0 := by
  have h₁ : optimizeExpr (.nonZero d) (mkCancelExpr x d) = .pure x := by
    simp only [mkCancelExpr, optimizeExpr, Expr.postFacts, Expr.mkBin_pure_pure, Expr.mkDiv,
      GuardIR.entails_nonZero, GuardIR.nf, GuardIR.mkConj, GuardIR.hasHyp,
      Expr.mkSafeDiv_pure_mul_right, decide_true, ↓reduceIte]
  have h₂ : optimizeExpr (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d)) =
      Expr.mkSafeDiv (.pure (.mul d x)) d := by
    simp only [optimizeExpr, Expr.postFacts, Expr.mkBin_pure_pure, Expr.mkDiv,
      GuardIR.entails_nonZero, GuardIR.nf, GuardIR.mkConj, GuardIR.hasHyp,
      decide_true, ↓reduceIte]
  obtain ⟨z, hz⟩ := Expr.mkSafeDiv_pure_mul_left x d
  rw [h₁, h₂, hz]
  exact ⟨rfl, rfl⟩

/-! ### Monotonicity of the optimizer in its context

`optimizeExpr` optimizes the right operand of a binary node under a context strengthened by
the facts established by the left operand. Compositionality therefore needs the following
property: a stronger context never leaves more checked divisions behind. -/

private theorem Expr.mkBin_eq_pure {pop : PureExpr → PureExpr → PureExpr}
    {eop : Expr → Expr → Expr} (hop : ∀ a b p, eop a b ≠ .pure p) {e₁ e₂ : Expr}
    {p : PureExpr} (h : Expr.mkBin pop eop e₁ e₂ = .pure p) :
    ∃ p₁ p₂, e₁ = .pure p₁ ∧ e₂ = .pure p₂ := by
  unfold Expr.mkBin at h
  split at h
  · exact ⟨_, _, rfl, rfl⟩
  · exact absurd h (hop _ _ _)

private theorem Expr.mkSafeDiv_eq_pure {n : Expr} {pd p : PureExpr}
    (h : Expr.mkSafeDiv n pd = .pure p) : ∃ pn, n = .pure pn := by
  unfold Expr.mkSafeDiv at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

private theorem Expr.rawDiv_ne_pure (checked : Bool) (n d : Expr) (p : PureExpr) :
    Expr.rawDiv checked n d ≠ .pure p := by
  cases checked <;> exact fun h => Expr.noConfusion h

private theorem Expr.cdc_rawDiv_mono (checked : Bool) {n n' d d' : Expr}
    (hn : checkedDivCount n' ≤ checkedDivCount n) (hd : checkedDivCount d' ≤ checkedDivCount d) :
    checkedDivCount (Expr.rawDiv checked n' d') ≤ checkedDivCount (Expr.rawDiv checked n d) := by
  cases checked with
  | true => exact Nat.add_le_add (Nat.add_le_add_left hn 1) hd
  | false => exact Nat.add_le_add hn hd

private theorem Expr.mkDiv_pure_known {checked : Bool} {K : GuardIR} {n : Expr} {pd : PureExpr}
    (hk : GuardIR.entails K (.nonZero pd) = true) :
    Expr.mkDiv checked K n (.pure pd) = Expr.mkSafeDiv n pd := by
  simp only [Expr.mkDiv, hk, ↓reduceIte]

private theorem Expr.mkDiv_pure_unknown {checked : Bool} {K : GuardIR} {n : Expr}
    {pd : PureExpr} (hk : GuardIR.entails K (.nonZero pd) = false) :
    Expr.mkDiv checked K n (.pure pd) = Expr.rawDiv checked n (.pure pd) := by
  simp only [Expr.mkDiv, hk, Bool.false_eq_true, ↓reduceIte]

private theorem Expr.mkDiv_not_pure {checked : Bool} {K : GuardIR} {n d : Expr}
    (hd : ∀ pd, d ≠ .pure pd) : Expr.mkDiv checked K n d = Expr.rawDiv checked n d := by
  unfold Expr.mkDiv
  split
  · next pd => exact absurd rfl (hd pd)
  · rfl

private theorem Expr.pure_or_not (d : Expr) : (∃ pd, d = .pure pd) ∨ ∀ pd, d ≠ .pure pd := by
  cases d with
  | pure pd => exact Or.inl ⟨pd, rfl⟩
  | _ => exact Or.inr (fun _ h => Expr.noConfusion h)

private theorem Expr.cdc_mkDiv_le (checked : Bool) (K : GuardIR) (n d : Expr) :
    checkedDivCount (Expr.mkDiv checked K n d) ≤ checkedDivCount (Expr.rawDiv checked n d) := by
  rcases Expr.pure_or_not d with ⟨pd, rfl⟩ | hnp
  · cases hk : GuardIR.entails K (.nonZero pd) with
    | true =>
      rw [Expr.mkDiv_pure_known hk,
        Expr.count_mkSafeDiv (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl)]
      cases checked with
      | true => exact Nat.le_trans (Nat.le_add_left _ 1) (Nat.le_add_right _ _)
      | false => exact Nat.le_add_right _ _
    | false => exact Nat.le_of_eq (congrArg checkedDivCount (Expr.mkDiv_pure_unknown hk))
  · exact Nat.le_of_eq (congrArg checkedDivCount (Expr.mkDiv_not_pure hnp))

/-- `CtxLe c c'`: every hypothesis available in the context `c` is available in `c'`. -/
private def GuardIR.CtxLe (c c' : GuardIR) : Prop :=
  ∀ h, GuardIR.hasHyp (GuardIR.nf c) h = true → GuardIR.hasHyp (GuardIR.nf c') h = true

private theorem GuardIR.CtxLe.conj {c c' : GuardIR} (hle : GuardIR.CtxLe c c') (F : GuardIR) :
    GuardIR.CtxLe (.conj c F) (.conj c' F) := by
  intro h
  simp only [GuardIR.nf, GuardIR.hasHyp_mkConj, Bool.or_eq_true]
  exact Or.imp_left (hle h)

private theorem GuardIR.CtxLe.conj_right (c F : GuardIR) : GuardIR.CtxLe c (.conj c F) := by
  intro h hh
  simp only [GuardIR.nf, GuardIR.hasHyp_mkConj, Bool.or_eq_true]
  exact Or.inl hh

private theorem GuardIR.CtxLe.simplifyUnder_top {c c' : GuardIR} (hle : GuardIR.CtxLe c c')
    {g : GuardIR} (h : GuardIR.simplifyUnder c g = .top) : GuardIR.simplifyUnder c' g = .top :=
  GuardIR.residual_top_mono hle _ h

private theorem GuardIR.CtxLe.entails_mono {c c' : GuardIR} (hle : GuardIR.CtxLe c c')
    {g : GuardIR} (h : GuardIR.entails c g = true) : GuardIR.entails c' g = true :=
  GuardIR.isTop_iff.mpr (hle.simplifyUnder_top (GuardIR.isTop_iff.mp h))

/-- Refinement between two optimizer outputs: no more checked divisions, and a pure result
    stays the same pure result. -/
private def Expr.Refines (e' e : Expr) : Prop :=
  checkedDivCount e' ≤ checkedDivCount e ∧ ∀ p, e = .pure p → e' = .pure p

private theorem Expr.mkBin_refines {pop : PureExpr → PureExpr → PureExpr}
    {eop : Expr → Expr → Expr}
    (hcnt : ∀ a b, checkedDivCount (eop a b) = checkedDivCount a + checkedDivCount b)
    (hnp : ∀ a b p, eop a b ≠ .pure p) {a a' b b' : Expr}
    (ha : Expr.Refines a' a) (hb : Expr.Refines b' b) :
    Expr.Refines (Expr.mkBin pop eop a' b') (Expr.mkBin pop eop a b) := by
  refine ⟨?_, ?_⟩
  · rw [Expr.count_mkBin (cnt := checkedDivCount) (fun _ => rfl) hcnt,
      Expr.count_mkBin (cnt := checkedDivCount) (fun _ => rfl) hcnt]
    exact Nat.add_le_add ha.1 hb.1
  · intro p h
    obtain ⟨p₁, p₂, rfl, rfl⟩ := Expr.mkBin_eq_pure hnp h
    rw [ha.2 p₁ rfl, hb.2 p₂ rfl]
    exact h

private theorem Expr.mkDiv_refines (checked : Bool) {K K' : GuardIR}
    (hK : GuardIR.CtxLe K K') {n n' d d' : Expr}
    (hn : Expr.Refines n' n) (hd : Expr.Refines d' d) :
    Expr.Refines (Expr.mkDiv checked K' n' d') (Expr.mkDiv checked K n d) := by
  have hraw : checkedDivCount (Expr.mkDiv checked K' n' d') ≤
      checkedDivCount (Expr.rawDiv checked n d) :=
    Nat.le_trans (Expr.cdc_mkDiv_le checked K' n' d') (Expr.cdc_rawDiv_mono checked hn.1 hd.1)
  rcases Expr.pure_or_not d with ⟨pd, rfl⟩ | hnp
  · cases hk : GuardIR.entails K (.nonZero pd) with
    | true =>
      rw [hd.2 pd rfl, Expr.mkDiv_pure_known hk, Expr.mkDiv_pure_known (hK.entails_mono hk)]
      refine ⟨?_, ?_⟩
      · rw [Expr.count_mkSafeDiv (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl),
          Expr.count_mkSafeDiv (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl)]
        exact hn.1
      · intro p hp
        obtain ⟨pn, rfl⟩ := Expr.mkSafeDiv_eq_pure hp
        rw [hn.2 pn rfl]
        exact hp
    | false =>
      rw [Expr.mkDiv_pure_unknown hk]
      exact ⟨hraw, fun p hp => absurd hp (Expr.rawDiv_ne_pure _ _ _ _)⟩
  · rw [Expr.mkDiv_not_pure hnp]
    exact ⟨hraw, fun p hp => absurd hp (Expr.rawDiv_ne_pure _ _ _ _)⟩

private theorem Expr.mkIte_refines (sf : Bool) {r r' : GuardIR} (hr : r = .top → r' = .top)
    {t t' f f' : Expr} (ht : Expr.Refines t' t) (hf : Expr.Refines f' f) :
    Expr.Refines (Expr.mkIte sf r' t' f') (Expr.mkIte sf r t f) := by
  cases sf with
  | true => exact hf
  | false =>
    cases r with
    | top => rw [hr rfl]; exact ht
    | _ =>
      refine ⟨?_, fun p hp => Expr.noConfusion hp⟩
      cases r' with
      | top => exact Nat.le_trans ht.1 (Nat.le_add_right _ _)
      | _ => exact Nat.add_le_add ht.1 hf.1

/-- A stronger context never leaves more checked divisions behind. -/
private theorem optimizeExpr_refines (e : Expr) :
    ∀ c c' : GuardIR, GuardIR.CtxLe c c' →
      Expr.Refines (optimizeExpr c' e) (optimizeExpr c e) := by
  induction e with
  | pure p => intro c c' _; exact ⟨Nat.le_refl _, fun _ h => h⟩
  | add e₁ e₂ ih₁ ih₂ =>
    intro c c' hle
    rw [optimizeExpr, optimizeExpr]
    exact Expr.mkBin_refines (fun _ _ => rfl) (fun _ _ _ h => Expr.noConfusion h)
      (ih₁ c c' hle) (ih₂ _ _ (hle.conj _))
  | sub e₁ e₂ ih₁ ih₂ =>
    intro c c' hle
    rw [optimizeExpr, optimizeExpr]
    exact Expr.mkBin_refines (fun _ _ => rfl) (fun _ _ _ h => Expr.noConfusion h)
      (ih₁ c c' hle) (ih₂ _ _ (hle.conj _))
  | mul e₁ e₂ ih₁ ih₂ =>
    intro c c' hle
    rw [optimizeExpr, optimizeExpr]
    exact Expr.mkBin_refines (fun _ _ => rfl) (fun _ _ _ h => Expr.noConfusion h)
      (ih₁ c c' hle) (ih₂ _ _ (hle.conj _))
  | checkedDiv n d ihn ihd =>
    intro c c' hle
    rw [optimizeExpr, optimizeExpr]
    exact Expr.mkDiv_refines true ((hle.conj _).conj _) (ihn c c' hle) (ihd _ _ (hle.conj _))
  | uncheckedDiv n d ihn ihd =>
    intro c c' hle
    rw [optimizeExpr, optimizeExpr]
    exact Expr.mkDiv_refines false ((hle.conj _).conj _) (ihn c c' hle) (ihd _ _ (hle.conj _))
  | iteGuard g t f iht ihf =>
    intro c c' hle
    rw [optimizeExpr, optimizeExpr]
    exact Expr.mkIte_refines _ hle.simplifyUnder_top (iht _ _ (hle.conj _)) (ihf _ _ (hle.conj _))

/-- Binary Context Compositionality: If `optimizeExpr (.nonZero d)` eliminates all checked divisions
    and introduces no guard branches on `e₁` and `e₂`, then it also eliminates all checked divisions on
    `.add e₁ e₂`, `.sub e₁ e₂`, and `.mul e₁ e₂`. -/
theorem optimizeExpr_compositional_binary (d : PureExpr) (e₁ e₂ : Expr)
    (h₁ : checkedDivCount (optimizeExpr (.nonZero d) e₁) = 0 ∧
          guardBranchCount (optimizeExpr (.nonZero d) e₁) = 0)
    (h₂ : checkedDivCount (optimizeExpr (.nonZero d) e₂) = 0 ∧
          guardBranchCount (optimizeExpr (.nonZero d) e₂) = 0) :
    checkedDivCount (optimizeExpr (.nonZero d) (.add e₁ e₂)) = 0 ∧
      checkedDivCount (optimizeExpr (.nonZero d) (.sub e₁ e₂)) = 0 ∧
      checkedDivCount (optimizeExpr (.nonZero d) (.mul e₁ e₂)) = 0 := by
  have hmono : checkedDivCount
      (optimizeExpr (.conj (.nonZero d) (Expr.postFacts e₁)) e₂) = 0 :=
    Nat.eq_zero_of_le_zero
      (h₂.1 ▸ (optimizeExpr_refines e₂ _ _ (GuardIR.CtxLe.conj_right _ _)).1)
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [optimizeExpr,
      Expr.count_mkBin (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl), h₁.1, hmono]

/-- Parametric Known-Context Elimination: Under `.nonZero d`, `optimizeExpr` on `mkDualDivExpr x y d`
    eliminates all checked divisions, introduces zero guard branches, and incurs zero runtime check cost. -/
theorem optimizeExpr_known_ctx_elim_param (x y d : PureExpr) (env : Env) :
    checkedDivCount (optimizeExpr (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
      guardBranchCount (optimizeExpr (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
      execCheckCost env (optimizeExpr (.nonZero d) (mkDualDivExpr x y d)) = 0 := by
  have hc : checkedDivCount (optimizeExpr (.nonZero d) (mkDualDivExpr x y d)) = 0 := by
    rw [optimizeExpr_nonZero_mkDualDivExpr,
      Expr.count_mkBin (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl),
      Expr.count_mkSafeDiv (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl)]
    rfl
  have hg : guardBranchCount (optimizeExpr (.nonZero d) (mkDualDivExpr x y d)) = 0 := by
    rw [optimizeExpr_nonZero_mkDualDivExpr,
      Expr.count_mkBin (cnt := guardBranchCount) (fun _ => rfl) (fun _ _ => rfl),
      Expr.count_mkSafeDiv (cnt := guardBranchCount) (fun _ => rfl) (fun _ _ => rfl)]
    rfl
  exact ⟨hc, hg, execCheckCost_eq_zero hc hg⟩

/-- Parametric Unknown-Context Guard Deduplication: Under `.top`, for any `x, y, d` and `env` with
    `evalPure env d ≠ 0`, `optimizeExpr` reduces runtime check cost on `mkDualDivExpr x y d` from `2` to `≤ 1`. -/
theorem optimizeExpr_unknown_ctx_dedup_param (x y d : PureExpr) (env : Env)
    (h : evalPure env d ≠ 0) :
    execCheckCost env (optimizeExpr .top (mkDualDivExpr x y d)) ≤ 1 ∧
      execCheckCost env (mkDualDivExpr x y d) = 2 := by
  rw [optimizeExpr_top_mkDualDivExpr, execCheckCost_checkedDiv_add_pure]
  exact ⟨Nat.le_refl 1, execCheckCost_mkDualDivExpr x y h⟩

/-- Parametric Trap Preservation: Under `.top`, for any `x, y, d` and `env` with `evalPure env d = 0`,
    `optimizeExpr .top (mkDualDivExpr x y d)` safely traps. -/
theorem optimizeExpr_zero_div_trap_param (x y d : PureExpr) (env : Env)
    (h : evalPure env d = 0) :
    evalExpr env (optimizeExpr .top (mkDualDivExpr x y d)) = .trap := by
  rw [optimizeExpr_sound .top (mkDualDivExpr x y d) env rfl]
  exact evalExpr_mkDualDivExpr_trap x y h

/-! ## Milestone 2: Imperative CFG Statements, Syntactic Pullbacks & Diamond Block Optimization -/

/-! ### Arithmetic-aware guard normalisation

Unlike the Milestone 1 normaliser, which treats atoms as opaque, `GuardIR.norm` evaluates
literal atoms, splits `nonZero (a * b)` into `nonZero a ∧ nonZero b`, rewrites `e = 0` as
`¬ nonZero e`, and removes double negations. Every rule is an equivalence, so the result
can be used both as a hypothesis and as a target. -/

/-- Constant folding of pure arithmetic. -/
private def PureExpr.fold : PureExpr → PureExpr
  | .add a b =>
    match PureExpr.fold a, PureExpr.fold b with
    | .lit m, .lit n => .lit (m + n)
    | a', b' => .add a' b'
  | .sub a b =>
    match PureExpr.fold a, PureExpr.fold b with
    | .lit m, .lit n => .lit (m - n)
    | a', b' => .sub a' b'
  | .mul a b =>
    match PureExpr.fold a, PureExpr.fold b with
    | .lit m, .lit n => .lit (m * n)
    | a', b' => .mul a' b'
  | e => e

/-- Normal form of `nonZero e`: literals are decided and products are split, since the
    integers have no zero divisors. -/
private def GuardIR.mkNonZero : PureExpr → GuardIR
  | .lit n => if n = 0 then .bot else .top
  | .mul a b => GuardIR.mkConj (GuardIR.mkNonZero a) (GuardIR.mkNonZero b)
  | e => .nonZero e

/-- Negation with double-negation elimination (guards are Boolean-valued). -/
private def GuardIR.mkNot : GuardIR → GuardIR
  | .top => .bot
  | .bot => .top
  | .imp g .bot => g
  | g => .imp g .bot

/-- Normal form of `a = b`: syntactically equal sides and literal pairs are decided,
    comparison with the literal `0` becomes `¬ nonZero`, and comparison with a non-zero
    literal additionally records that the other side is non-zero. -/
private def GuardIR.mkEq (a b : PureExpr) : GuardIR :=
  if a = b then .top
  else
    match a, b with
    | .lit _, .lit _ => .bot
    | e, .lit n =>
      if n = 0 then GuardIR.mkNot (GuardIR.mkNonZero e)
      else GuardIR.mkConj (GuardIR.mkNonZero e) (.eq e (.lit n))
    | .lit n, e =>
      if n = 0 then GuardIR.mkNot (GuardIR.mkNonZero e)
      else GuardIR.mkConj (GuardIR.mkNonZero e) (.eq (.lit n) e)
    | a, b => .eq a b

/-- Implication of normal forms: `g ⇨ g` is `⊤` and `g ⇨ ⊥` is built with `GuardIR.mkNot`. -/
private def GuardIR.impN (a b : GuardIR) : GuardIR :=
  if a = b then .top
  else
    match b with
    | .bot => GuardIR.mkNot a
    | b => GuardIR.mkImp a b

/-- Arithmetic-aware normal form of a guard. -/
private def GuardIR.norm : GuardIR → GuardIR
  | .top => .top
  | .bot => .bot
  | .nonZero e => GuardIR.mkNonZero (PureExpr.fold e)
  | .eq a b => GuardIR.mkEq (PureExpr.fold a) (PureExpr.fold b)
  | .conj g h => GuardIR.mkConj (GuardIR.norm g) (GuardIR.norm h)
  | .imp g h => GuardIR.impN (GuardIR.norm g) (GuardIR.norm h)

/-! ### Syntactic pullback across statements -/

/-- Substitution `p[v := r]`. -/
private def PureExpr.subst (v : VarId) (r : PureExpr) : PureExpr → PureExpr
  | .lit n => .lit n
  | .var w => if w = v then r else .var w
  | .add a b => .add (PureExpr.subst v r a) (PureExpr.subst v r b)
  | .sub a b => .sub (PureExpr.subst v r a) (PureExpr.subst v r b)
  | .mul a b => .mul (PureExpr.subst v r a) (PureExpr.subst v r b)

/-- Substitution `g[v := r]` in every atom of a guard: the weakest precondition of `g`
    across the assignment `v := r`. -/
private def GuardIR.subst (v : VarId) (r : PureExpr) : GuardIR → GuardIR
  | .top => .top
  | .bot => .bot
  | .nonZero e => .nonZero (PureExpr.subst v r e)
  | .eq a b => .eq (PureExpr.subst v r a) (PureExpr.subst v r b)
  | .conj g h => .conj (GuardIR.subst v r g) (GuardIR.subst v r h)
  | .imp g h => .imp (GuardIR.subst v r g) (GuardIR.subst v r h)

/-- Weakest precondition at a two-way branch on `c`, given the preconditions `gt` and `gf`
    of the two arms: `(c → gt) ∧ (¬ c → gf)`. The arms are normalised first; if they then
    agree the branch condition is irrelevant and no case split is recorded. -/
private def GuardIR.branch (c gt gf : GuardIR) : GuardIR :=
  let t := GuardIR.norm gt
  let f := GuardIR.norm gf
  if t = f then t
  else
    let c' := GuardIR.norm c
    GuardIR.mkConj (GuardIR.impN c' t) (GuardIR.impN (GuardIR.mkNot c') f)

/-- Computable syntactic weakest-precondition pullback of a `GuardIR` across an imperative `Stmt`. -/
def pullbackGuardIR (s : Stmt) (g : GuardIR) : GuardIR :=
  match s with
  | .skip => g
  | .assign v rhs => GuardIR.subst v rhs g
  | .seq s₁ s₂ => pullbackGuardIR s₁ (pullbackGuardIR s₂ g)
  | .ite c t f => GuardIR.branch c (pullbackGuardIR t g) (pullbackGuardIR f g)

/-- Computable edge guard synthesis across an imperative `Stmt` from pre-context `a` to post-guard `b`. -/
def synthesizeStmtGuardIR (s : Stmt) (a b : GuardIR) : GuardIR :=
  synthesizeGuardIR (GuardIR.norm a) (GuardIR.norm (pullbackGuardIR s b))

/-! ### Statement and block rewriting -/

/-- `entailsAfter s a b`: every execution of `s` from a state satisfying `a` ends in a state
    satisfying `b`. Equivalently (`GuardIR.entailsAfter_eq`), the edge guard
    `synthesizeStmtGuardIR s a b` is `.top`. -/
private def GuardIR.entailsAfter (s : Stmt) (a b : GuardIR) : Bool :=
  GuardIR.entails (GuardIR.norm a) (GuardIR.norm (pullbackGuardIR s b))

/-- Sequencing that drops `skip`. -/
private def Stmt.mkSeq (s₁ s₂ : Stmt) : Stmt :=
  match s₁, s₂ with
  | .skip, s => s
  | s, .skip => s
  | s₁, s₂ => .seq s₁ s₂

/-- Branching that drops the guard when both arms are the same statement. -/
private def Stmt.mkIte (c : GuardIR) (t f : Stmt) : Stmt :=
  if t = f then t else .ite c t f

/-- `Stmt.optimize K pre s` rewrites `s`, which runs after the prefix `pre` from entry states
    satisfying `K`. A branch is pruned when the entry context entails, across `pre`, that
    its condition holds or fails; otherwise both arms are rewritten under the entry context
    extended with the pulled-back path condition. -/
private def Stmt.optimize : GuardIR → Stmt → Stmt → Stmt
  | _, _, .skip => .skip
  | _, _, .assign v rhs => .assign v rhs
  | K, pre, .seq s₁ s₂ =>
    Stmt.mkSeq (Stmt.optimize K pre s₁) (Stmt.optimize K (.seq pre s₁) s₂)
  | K, pre, .ite c t f =>
    if GuardIR.entailsAfter pre K c then Stmt.optimize K pre t
    else if GuardIR.entailsAfter pre K (.imp c .bot) then Stmt.optimize K pre f
    else
      Stmt.mkIte c (Stmt.optimize (.conj K (pullbackGuardIR pre c)) pre t)
        (Stmt.optimize (.conj K (pullbackGuardIR pre (.imp c .bot))) pre f)

/-- The conjuncts of a guard. -/
private def GuardIR.conjuncts : GuardIR → List GuardIR
  | .conj g h => GuardIR.conjuncts g ++ GuardIR.conjuncts h
  | g => [g]

/-- Guards whose truth in the final state would let `optimizeExpr` simplify `e`: the
    non-zeroness of every pure divisor and the conjuncts of every guard-branch condition. -/
private def Expr.factCandidates : Expr → List GuardIR
  | .pure _ => []
  | .add a b | .sub a b | .mul a b => Expr.factCandidates a ++ Expr.factCandidates b
  | .checkedDiv n d | .uncheckedDiv n d =>
    (match Expr.asPure? d with
     | some pd => [GuardIR.nonZero pd]
     | none => []) ++ (Expr.factCandidates n ++ Expr.factCandidates d)
  | .iteGuard g t f =>
    GuardIR.conjuncts g ++ (Expr.factCandidates t ++ Expr.factCandidates f)

/-- Conjunction of the candidates accepted by `p`. -/
private def GuardIR.collect (p : GuardIR → Bool) : List GuardIR → GuardIR
  | [] => .top
  | g :: gs => if p g then .conj g (GuardIR.collect p gs) else GuardIR.collect p gs

/-- Computable context-sensitive block optimizer across `BlockProg` statement prefixes and return expressions. -/
def optimizeBlock (ctx : GuardIR) (prog : BlockProg) : BlockProg :=
  let body := Stmt.optimize ctx .skip prog.body
  { body := body
    ret := optimizeExpr
      (GuardIR.collect (GuardIR.entailsAfter body ctx) (Expr.factCandidates prog.ret)) prog.ret }

/-! ### Semantics of the arithmetic-aware normaliser -/

private theorem PureExpr.evalPure_fold (env : Env) (p : PureExpr) :
    evalPure env (PureExpr.fold p) = evalPure env p := by
  induction p with
  | add a b iha ihb =>
    simp only [PureExpr.fold]
    rw [evalPure, ← iha, ← ihb]
    generalize PureExpr.fold a = x
    generalize PureExpr.fold b = y
    split <;> rfl
  | sub a b iha ihb =>
    simp only [PureExpr.fold]
    rw [evalPure, ← iha, ← ihb]
    generalize PureExpr.fold a = x
    generalize PureExpr.fold b = y
    split <;> rfl
  | mul a b iha ihb =>
    simp only [PureExpr.fold]
    rw [evalPure, ← iha, ← ihb]
    generalize PureExpr.fold a = x
    generalize PureExpr.fold b = y
    split <;> rfl
  | _ => rfl

private theorem GuardIR.evalGuard_mkNonZero (env : Env) (e : PureExpr) :
    evalGuard env (GuardIR.mkNonZero e) = decide (evalPure env e ≠ 0) := by
  induction e with
  | lit n =>
    simp only [GuardIR.mkNonZero, evalPure]
    split
    · next h => exact (decide_eq_false (fun hne => hne h)).symm
    · next h => exact (decide_eq_true h).symm
  | mul a b iha ihb =>
    simp only [GuardIR.mkNonZero, GuardIR.evalGuard_mkConj, iha, ihb, evalPure]
    rw [← Bool.decide_and]
    exact decide_eq_decide.mpr Int.mul_ne_zero_iff.symm
  | _ => rfl

private theorem GuardIR.evalGuard_mkNot (env : Env) (g : GuardIR) :
    evalGuard env (GuardIR.mkNot g) = !evalGuard env g := by
  cases g with
  | imp g₁ g₂ => cases g₂ <;> simp [GuardIR.mkNot, evalGuard]
  | _ => simp [GuardIR.mkNot, evalGuard]

private theorem Int.not_decide_ne_zero (x : Int) : (!decide (x ≠ 0)) = decide (x = 0) :=
  if h : x = 0 then by
    rw [decide_eq_true h, decide_eq_false (fun hne : x ≠ 0 => hne h)]
    rfl
  else by
    rw [decide_eq_false h, decide_eq_true h]
    rfl

/-- A value equal to a non-zero literal is itself non-zero. -/
private theorem Int.decide_ne_zero_and_eq {n : Int} (hn : n ≠ 0) (x : Int) :
    (decide (x ≠ 0) && decide (x = n)) = decide (x = n) :=
  if h : x = n then by
    have hx : x ≠ 0 := fun hx => hn (h ▸ hx)
    rw [decide_eq_true h, decide_eq_true hx]
    rfl
  else by
    rw [decide_eq_false h, Bool.and_false]

private theorem Int.decide_ne_zero_and_eq' {n : Int} (hn : n ≠ 0) (x : Int) :
    (decide (x ≠ 0) && decide (n = x)) = decide (n = x) :=
  if h : n = x then by
    have hx : x ≠ 0 := fun hx => hn (h.trans hx)
    rw [decide_eq_true h, decide_eq_true hx]
    rfl
  else by
    rw [decide_eq_false h, Bool.and_false]

private theorem GuardIR.evalGuard_mkEq (env : Env) (a b : PureExpr) :
    evalGuard env (GuardIR.mkEq a b) = decide (evalPure env a = evalPure env b) := by
  unfold GuardIR.mkEq
  split
  · next h => subst h; exact (decide_eq_true rfl).symm
  · next hab =>
    split
    · next m n =>
      exact (decide_eq_false (fun h : m = n => hab (h ▸ rfl))).symm
    · next e n =>
      split
      · next hn =>
        subst hn
        rw [GuardIR.evalGuard_mkNot, GuardIR.evalGuard_mkNonZero]
        exact Int.not_decide_ne_zero _
      · next hn =>
        rw [GuardIR.evalGuard_mkConj, GuardIR.evalGuard_mkNonZero]
        exact Int.decide_ne_zero_and_eq hn _
    · next n e =>
      split
      · next hn =>
        subst hn
        rw [GuardIR.evalGuard_mkNot, GuardIR.evalGuard_mkNonZero]
        exact (Int.not_decide_ne_zero _).trans (decide_eq_decide.mpr eq_comm)
      · next hn =>
        rw [GuardIR.evalGuard_mkConj, GuardIR.evalGuard_mkNonZero]
        exact Int.decide_ne_zero_and_eq' hn _
    · rfl

private theorem GuardIR.evalGuard_impN (env : Env) (a b : GuardIR) :
    evalGuard env (GuardIR.impN a b) = (!evalGuard env a || evalGuard env b) := by
  unfold GuardIR.impN
  split
  · next h =>
    subst h
    cases evalGuard env a <;> rfl
  · cases b <;> simp [GuardIR.evalGuard_mkNot, GuardIR.evalGuard_mkImp, evalGuard]

/-- Normalisation preserves the Boolean value of a guard in every environment. -/
private theorem GuardIR.evalGuard_norm (env : Env) (g : GuardIR) :
    evalGuard env (GuardIR.norm g) = evalGuard env g := by
  induction g with
  | top => rfl
  | bot => rfl
  | nonZero e =>
    rw [GuardIR.norm, GuardIR.evalGuard_mkNonZero, PureExpr.evalPure_fold]
    rfl
  | eq a b =>
    rw [GuardIR.norm, GuardIR.evalGuard_mkEq, PureExpr.evalPure_fold, PureExpr.evalPure_fold]
    rfl
  | conj g h ihg ihh =>
    rw [GuardIR.norm, GuardIR.evalGuard_mkConj, ihg, ihh]
    rfl
  | imp g h ihg ihh =>
    rw [GuardIR.norm, GuardIR.evalGuard_impN, ihg, ihh]
    rfl

/-! ### Semantics of the pullback -/

private theorem PureExpr.evalPure_subst (env : Env) (v : VarId) (r : PureExpr) (p : PureExpr) :
    evalPure env (PureExpr.subst v r p) = evalPure (updateEnv env v (evalPure env r)) p := by
  induction p with
  | lit n => rfl
  | var w =>
    simp only [PureExpr.subst, updateEnv, evalPure]
    split
    · next h => rw [ite_eq_left (decide_eq_true h)]
    · next h => rw [ite_eq_right (fun hd => h (of_decide_eq_true hd))]; rfl
  | add a b iha ihb => simp only [PureExpr.subst, evalPure, iha, ihb]
  | sub a b iha ihb => simp only [PureExpr.subst, evalPure, iha, ihb]
  | mul a b iha ihb => simp only [PureExpr.subst, evalPure, iha, ihb]

/-- Substitution lemma: evaluating `g[v := r]` is evaluating `g` after the assignment. -/
private theorem GuardIR.evalGuard_subst (env : Env) (v : VarId) (r : PureExpr) (g : GuardIR) :
    evalGuard env (GuardIR.subst v r g) = evalGuard (updateEnv env v (evalPure env r)) g := by
  induction g with
  | top => rfl
  | bot => rfl
  | nonZero e => simp only [GuardIR.subst, evalGuard, PureExpr.evalPure_subst]
  | eq a b => simp only [GuardIR.subst, evalGuard, PureExpr.evalPure_subst]
  | conj g h ihg ihh => simp only [GuardIR.subst, evalGuard, ihg, ihh]
  | imp g h ihg ihh => simp only [GuardIR.subst, evalGuard, ihg, ihh]

private theorem GuardIR.evalGuard_branch (env : Env) (c gt gf : GuardIR) :
    evalGuard env (GuardIR.branch c gt gf) =
      (if evalGuard env c = true then evalGuard env gt else evalGuard env gf) := by
  have ht := GuardIR.evalGuard_norm env gt
  have hf := GuardIR.evalGuard_norm env gf
  have hc := GuardIR.evalGuard_norm env c
  unfold GuardIR.branch
  simp only []
  split
  · next h =>
    rw [h] at ht
    rw [← ht, ← hf, h]
    cases evalGuard env c <;> rfl
  · rw [GuardIR.evalGuard_mkConj, GuardIR.evalGuard_impN, GuardIR.evalGuard_impN,
      GuardIR.evalGuard_mkNot, ht, hf, hc]
    cases evalGuard env c <;> cases evalGuard env gt <;> cases evalGuard env gf <;> rfl

/-- Pointwise Boolean semantics of the pullback: evaluate the guard after running `s`. -/
private theorem evalGuard_pullbackGuardIR (s : Stmt) :
    ∀ (g : GuardIR) (env : Env),
      evalGuard env (pullbackGuardIR s g) = evalGuard (execStmt s env) g := by
  induction s with
  | skip => intro g env; rfl
  | assign v rhs => intro g env; exact GuardIR.evalGuard_subst env v rhs g
  | seq s₁ s₂ ih₁ ih₂ =>
    intro g env
    rw [pullbackGuardIR, ih₁, ih₂]
    rfl
  | ite c t f iht ihf =>
    intro g env
    rw [pullbackGuardIR, GuardIR.evalGuard_branch, iht, ihf]
    simp only [execStmt]
    cases evalGuard env c <;> rfl

/-- Pointwise Boolean semantics of the edge guard: `a → b after s`. -/
private theorem evalGuard_synthesizeStmtGuardIR (env : Env) (s : Stmt) (a b : GuardIR) :
    evalGuard env (synthesizeStmtGuardIR s a b) =
      (!evalGuard env a || evalGuard (execStmt s env) b) := by
  unfold synthesizeStmtGuardIR
  rw [evalGuard_synthesizeGuardIR, GuardIR.evalGuard_norm, GuardIR.evalGuard_norm,
    evalGuard_pullbackGuardIR]

private theorem denoteGuard_norm (g : GuardIR) : denoteGuard (GuardIR.norm g) = denoteGuard g := by
  funext env
  show (evalGuard env (GuardIR.norm g) = true) = (evalGuard env g = true)
  rw [GuardIR.evalGuard_norm]

/-! ### Milestone 2 target theorems: bridge, pullback and edge-guard synthesis -/

/-- Pulled-Back State-Transfer Lifting Equivalence: `GuardedEquiv` along
    `pullbackEval (stateTransfer step) (liftEval run)` at predicate `P` holds if and only if
    `t₁` and `t₂` produce identical concrete outcomes in `step s` whenever `P s` holds. -/
theorem pullbackEval_stateTransfer_liftEval_iff {Out : Type*}
    (step : S₁ → S₂) (run : S₂ → Term → Out) (P : S₁ → Prop) (t₁ t₂ : Term) :
    GuardedEquiv (pullbackEval (stateTransfer step) (liftEval run)) P t₁ t₂ ↔
      ∀ s, P s → run (step s) t₁ = run (step s) t₂ := by
  constructor
  · intro h s hs
    have hP : pullbackEval (stateTransfer step) (liftEval run) P t₁ =
        pullbackEval (stateTransfer step) (liftEval run) P t₂ := h P (le_refl P)
    have hEq : ((∃ s₁, step s₁ = step s ∧ P s₁) ∧ run (step s) t₁ = run (step s) t₁) =
        ((∃ s₁, step s₁ = step s ∧ P s₁) ∧ run (step s) t₂ = run (step s) t₁) :=
      congrFun (congrFun hP (step s)) (run (step s) t₁)
    exact (hEq ▸ And.intro (Exists.intro s (And.intro rfl hs)) rfl).2.symm
  · intro h stage hst
    funext s₂ out
    apply propext
    show ((∃ s₁, step s₁ = s₂ ∧ stage s₁) ∧ run s₂ t₁ = out) ↔
      ((∃ s₁, step s₁ = s₂ ∧ stage s₁) ∧ run s₂ t₂ = out)
    constructor
    · rintro ⟨⟨s₁, rfl, hs⟩, he⟩
      exact ⟨⟨s₁, rfl, hs⟩, (h s₁ (hst s₁ hs)) ▸ he⟩
    · rintro ⟨⟨s₁, rfl, hs⟩, he⟩
      exact ⟨⟨s₁, rfl, hs⟩, (h s₁ (hst s₁ hs)).symm ▸ he⟩

/-- Categorical Realization of `pullbackGuardIR`: Denotation commutes with `(stateTransfer (execStmt s)).pullback`. -/
theorem pullbackGuardIR_denote (s : Stmt) (g : GuardIR) :
    denoteGuard (pullbackGuardIR s g) =
      (stateTransfer (execStmt s)).pullback (denoteGuard g) := by
  funext env
  show (evalGuard env (pullbackGuardIR s g) = true) = (evalGuard (execStmt s env) g = true)
  rw [evalGuard_pullbackGuardIR]

/-- Contravariant Compositionality of `pullbackGuardIR` on Sequential Statements:
    Denotation on `.seq s₁ s₂` equals the composed `CFGTransfer` pullback. -/
theorem pullbackGuardIR_seq (s₁ s₂ : Stmt) (g : GuardIR) :
    denoteGuard (pullbackGuardIR (.seq s₁ s₂) g) =
      ((stateTransfer (execStmt s₁)).comp (stateTransfer (execStmt s₂))).pullback (denoteGuard g) := by
  rw [pullbackGuardIR_denote]
  rfl

/-- Categorical Realization of `synthesizeStmtGuardIR`: Denotation commutes with abstract `synthesizeEdgeGuard`
    along `stateTransfer (execStmt s)`. -/
theorem synthesizeStmtGuardIR_denote (s : Stmt) (a b : GuardIR) :
    denoteGuard (synthesizeStmtGuardIR s a b) =
      synthesizeEdgeGuard (stateTransfer (execStmt s)) (denoteGuard a) (denoteGuard b) := by
  unfold synthesizeStmtGuardIR synthesizeEdgeGuard
  rw [synthesizeGuardIR_denote, denoteGuard_norm, denoteGuard_norm, pullbackGuardIR_denote]

/-- Universal Property (Kripke-Joyal / Galois Adjunction) of `synthesizeStmtGuardIR`:
    `ForcesAfter` across `execStmt s` under `denoteGuard a ⊓ g` holds iff `g` implies the synthesized guard. -/
theorem synthesizeStmtGuardIR_universal (s : Stmt) (a b : GuardIR) (g : Env → Prop) :
    ForcesAfter (stateTransfer (execStmt s)) (denoteGuard a ⊓ g) (denoteGuard b) ↔
      g ≤ denoteGuard (synthesizeStmtGuardIR s a b) := by
  rw [synthesizeStmtGuardIR_denote, forcesAfter_iff_pullback, forces_guard_iff]
  exact Iff.rfl

/-- Operational Diamond Join Rewrite Soundness via `synthesizeStmtGuardIR`:
    Given a downstream rewrite `GuardedEquiv (liftEval evalExpr) (denoteGuard req) e₁ e₂`,
    conjoining `ctx` with the conjunction of branch edge guards guarantees `e₁` and `e₂`
    evaluate to identical `Outcome`s after both `s₁` and `s₂`. -/
theorem synthesizeStmtGuardIR_diamond_sound (s₁ s₂ : Stmt) (ctx req : GuardIR)
    (e₁ e₂ : Expr) (h : GuardedEquiv (liftEval evalExpr) (denoteGuard req) e₁ e₂) :
    let g := GuardIR.conj (synthesizeStmtGuardIR s₁ ctx req) (synthesizeStmtGuardIR s₂ ctx req)
    ∀ env : Env, evalGuard env ctx = true → evalGuard env g = true →
      evalExpr (execStmt s₁ env) e₁ = evalExpr (execStmt s₁ env) e₂ ∧
        evalExpr (execStmt s₂ env) e₁ = evalExpr (execStmt s₂ env) e₂ := by
  intro g env hctx hg
  have hreq := (liftEval_guardedEquiv_iff evalExpr (denoteGuard req) e₁ e₂).mp h
  have hg' : (evalGuard env (synthesizeStmtGuardIR s₁ ctx req) &&
      evalGuard env (synthesizeStmtGuardIR s₂ ctx req)) = true := hg
  rw [evalGuard_synthesizeStmtGuardIR, evalGuard_synthesizeStmtGuardIR, hctx] at hg'
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hg'
  exact ⟨hreq _ hg'.1, hreq _ hg'.2⟩

/-- Every target whose hypotheses are all available in the context is discharged. -/
private theorem GuardIR.residual_eq_top_of_hasHyp (t : GuardIR) :
    ∀ {c : GuardIR}, (∀ x, GuardIR.hasHyp t x = true → GuardIR.hasHyp c x = true) →
      GuardIR.residual c t = .top := by
  induction t with
  | top => intro c _; rfl
  | bot =>
    intro c h
    simp only [GuardIR.residual, h .bot rfl, ↓reduceIte]
  | nonZero e =>
    intro c h
    simp only [GuardIR.residual, h (.nonZero e) (decide_eq_true rfl), ↓reduceIte]
  | eq a b =>
    intro c h
    simp only [GuardIR.residual, h (.eq a b) (decide_eq_true rfl), ↓reduceIte]
  | conj t₁ t₂ ih₁ ih₂ =>
    intro c h
    have h₁ : GuardIR.residual c t₁ = .top :=
      ih₁ (fun x hx => h x (by simp only [GuardIR.hasHyp, hx, Bool.true_or]))
    have h₂ : GuardIR.residual (.conj c t₁) t₂ = .top :=
      ih₂ (fun x hx => by
        simp only [GuardIR.hasHyp, h x (by simp only [GuardIR.hasHyp, hx, Bool.or_true]),
          Bool.true_or])
    simp only [GuardIR.residual, h₁, h₂]
    rfl
  | imp t₁ t₂ _ _ =>
    intro c h
    simp only [GuardIR.residual, h (.imp t₁ t₂) (decide_eq_true rfl), ↓reduceIte]

/-- Reflexivity of the Milestone 1 entailment test. -/
private theorem GuardIR.entails_self (g : GuardIR) : GuardIR.entails g g = true := by
  unfold GuardIR.entails GuardIR.simplifyUnder
  rw [GuardIR.residual_eq_top_of_hasHyp (GuardIR.nf g) (fun _ h => h)]
  rfl

/-- Reflexivity of guard synthesis: `a ⇨ a` normalises to `.top`. -/
private theorem synthesizeGuardIR_self (g : GuardIR) : synthesizeGuardIR g g = .top :=
  GuardIR.isTop_iff.mp ((GuardIR.entails_eq g g) ▸ GuardIR.entails_self g)

/-- Non-Zero Literal Discharge: Synthesizing `.nonZero (.lit n)` across `.skip` from `.top`
    normalizes to `.top` whenever `n ≠ 0`. -/
theorem synthesizeStmtGuardIR_lit_nonZero (n : Int) (hn : n ≠ 0) :
    synthesizeStmtGuardIR .skip .top (.nonZero (.lit n)) = .top := by
  have h : GuardIR.norm (.nonZero (.lit n)) = .top := by
    simp only [GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero, ite_eq_right hn]
  unfold synthesizeStmtGuardIR
  rw [pullbackGuardIR, h]
  rfl

/-- Assignment Pullback Self-Discharge: Across `v := rhs`, pre-context `.nonZero rhs`
    discharges post-requirement `.nonZero (.var v)` to `.top`. -/
theorem synthesizeStmtGuardIR_assign_self (v : VarId) (rhs : PureExpr) :
    synthesizeStmtGuardIR (.assign v rhs) (.nonZero rhs) (.nonZero (.var v)) = .top := by
  have h : pullbackGuardIR (.assign v rhs) (.nonZero (.var v)) = .nonZero rhs := by
    simp only [pullbackGuardIR, GuardIR.subst, PureExpr.subst, ↓reduceIte]
  unfold synthesizeStmtGuardIR
  rw [h]
  exact synthesizeGuardIR_self _

/-- Diamond Safe-Divisor Discharge: Across `if x == 0 then d := n else d := x` with `n ≠ 0`,
    post-requirement `.nonZero (.var d)` discharges unconditionally from `.top` to `.top`. -/
theorem synthesizeStmtGuardIR_diamond_safe (x d : VarId) (n : Int) (hn : n ≠ 0) :
    synthesizeStmtGuardIR
      (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)))
      .top (.nonZero (.var d)) = .top := by
  have hwp : pullbackGuardIR
      (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)))
      (.nonZero (.var d)) = .top := by
    simp only [pullbackGuardIR, GuardIR.subst, PureExpr.subst, GuardIR.branch, GuardIR.norm,
      PureExpr.fold, GuardIR.mkNonZero, GuardIR.mkEq, GuardIR.mkNot, GuardIR.impN,
      GuardIR.mkConj, GuardIR.mkImp, ite_eq_right hn, reduceCtorEq, ↓reduceIte]
  unfold synthesizeStmtGuardIR
  rw [hwp]
  rfl

/-! ### Soundness of the statement and block optimizers -/

/-- The optimizer's query is exactly triviality of the synthesized edge guard. -/
private theorem GuardIR.entailsAfter_eq (s : Stmt) (a b : GuardIR) :
    GuardIR.entailsAfter s a b = GuardIR.isTop (synthesizeStmtGuardIR s a b) :=
  GuardIR.entails_eq _ _

/-- Soundness of the optimizer's query, obtained from the universal property (Kripke-Joyal
    forcing) of `synthesizeStmtGuardIR`: a trivial edge guard means that every state reached
    from the pre-context forces the post-guard. -/
private theorem GuardIR.entailsAfter_sound {s : Stmt} {a b : GuardIR} {env : Env}
    (h : GuardIR.entailsAfter s a b = true) (ha : evalGuard env a = true) :
    evalGuard (execStmt s env) b = true := by
  have htop : synthesizeStmtGuardIR s a b = .top :=
    GuardIR.isTop_iff.mp (GuardIR.entailsAfter_eq s a b ▸ h)
  have hforce : ForcesAfter (stateTransfer (execStmt s)) (denoteGuard a ⊓ denoteGuard a)
      (denoteGuard b) :=
    (synthesizeStmtGuardIR_universal s a b (denoteGuard a)).mpr (by rw [htop]; intro _ _; rfl)
  exact hforce (execStmt s env) (Exists.intro env (And.intro rfl (And.intro ha ha)))

private theorem evalGuard_eq_false_of_imp_bot {env : Env} {c : GuardIR}
    (h : evalGuard env (.imp c .bot) = true) : evalGuard env c = false := by
  have h' : (!evalGuard env c || false) = true := h
  cases hc : evalGuard env c with
  | false => rfl
  | true => rw [hc] at h'; exact absurd h' (by decide)

private theorem evalGuard_imp_bot_of_eq_false {env : Env} {c : GuardIR}
    (h : evalGuard env c = false) : evalGuard env (.imp c .bot) = true := by
  show (!evalGuard env c || false) = true
  rw [h]
  rfl

private theorem Stmt.execStmt_mkSeq (s₁ s₂ : Stmt) (env : Env) :
    execStmt (Stmt.mkSeq s₁ s₂) env = execStmt s₂ (execStmt s₁ env) := by
  unfold Stmt.mkSeq
  split <;> rfl

private theorem Stmt.execStmt_mkIte (c : GuardIR) (t f : Stmt) (env : Env) :
    execStmt (Stmt.mkIte c t f) env = execStmt (.ite c t f) env := by
  unfold Stmt.mkIte
  split
  · next h =>
    subst h
    simp only [execStmt]
    cases evalGuard env c <;> rfl
  · rfl

/-- The rewritten statement performs the same state transition as the original from every
    state reachable through the prefix from an entry state satisfying the context. -/
private theorem Stmt.execStmt_optimize (s : Stmt) :
    ∀ (K : GuardIR) (pre : Stmt) (env : Env), evalGuard env K = true →
      execStmt (Stmt.optimize K pre s) (execStmt pre env) = execStmt s (execStmt pre env) := by
  induction s with
  | skip => intro K pre env _; rfl
  | assign v rhs => intro K pre env _; rfl
  | seq s₁ s₂ ih₁ ih₂ =>
    intro K pre env hK
    rw [Stmt.optimize, Stmt.execStmt_mkSeq, ih₁ K pre env hK]
    exact ih₂ K (.seq pre s₁) env hK
  | ite c t f iht ihf =>
    intro K pre env hK
    rw [Stmt.optimize]
    split
    · next hc =>
      have hc' : evalGuard (execStmt pre env) c = true := GuardIR.entailsAfter_sound hc hK
      rw [iht K pre env hK]
      simp only [execStmt, hc', ↓reduceIte]
    · split
      · next hnc =>
        have hc' : evalGuard (execStmt pre env) c = false :=
          evalGuard_eq_false_of_imp_bot (GuardIR.entailsAfter_sound hnc hK)
        rw [ihf K pre env hK]
        simp only [execStmt, hc', Bool.false_eq_true, ↓reduceIte]
      · rw [Stmt.execStmt_mkIte]
        simp only [execStmt]
        cases hc : evalGuard (execStmt pre env) c with
        | true =>
          simp only [↓reduceIte]
          exact iht _ pre env (GuardIR.evalGuard_conj_intro hK
            (by rw [evalGuard_pullbackGuardIR]; exact hc))
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ihf _ pre env (GuardIR.evalGuard_conj_intro hK
            (by rw [evalGuard_pullbackGuardIR]; exact evalGuard_imp_bot_of_eq_false hc))

private theorem GuardIR.evalGuard_collect {env : Env} {p : GuardIR → Bool}
    (hp : ∀ g, p g = true → evalGuard env g = true) (l : List GuardIR) :
    evalGuard env (GuardIR.collect p l) = true := by
  induction l with
  | nil => rfl
  | cons g gs ih =>
    unfold GuardIR.collect
    split
    · next h => exact GuardIR.evalGuard_conj_intro (hp g h) ih
    · exact ih

/-- Operational soundness of `optimizeBlock`: the rewritten body reaches the same final
    state, and every fact handed to `optimizeExpr` holds in that state. -/
private theorem optimizeBlock_sound_aux (ctx : GuardIR) (prog : BlockProg) (env : Env)
    (hctx : evalGuard env ctx = true) :
    evalBlock env (optimizeBlock ctx prog) = evalBlock env prog := by
  have hbody : execStmt (Stmt.optimize ctx .skip prog.body) env = execStmt prog.body env :=
    Stmt.execStmt_optimize prog.body ctx .skip env hctx
  show evalExpr (execStmt (Stmt.optimize ctx .skip prog.body) env)
      (optimizeExpr
        (GuardIR.collect (GuardIR.entailsAfter (Stmt.optimize ctx .skip prog.body) ctx)
          (Expr.factCandidates prog.ret)) prog.ret) =
    evalExpr (execStmt prog.body env) prog.ret
  rw [optimizeExpr_sound _ _ _
    (GuardIR.evalGuard_collect (fun g hg => GuardIR.entailsAfter_sound hg hctx) _), hbody]

/-- Stage-Guarded Soundness of `optimizeBlock` via `GuardedEquiv` and `liftEval evalBlock`. -/
theorem optimizeBlock_guardedEquiv (ctx : GuardIR) (prog : BlockProg) :
    GuardedEquiv (liftEval evalBlock) (denoteGuard ctx) (optimizeBlock ctx prog) prog := by
  exact (liftEval_guardedEquiv_iff evalBlock (denoteGuard ctx) (optimizeBlock ctx prog) prog).mpr
    (fun env h => optimizeBlock_sound_aux ctx prog env h)

/-- Concrete Operational Soundness of `optimizeBlock`: Whenever `evalGuard env ctx = true`,
    `optimizeBlock ctx prog` produces the exact same `Outcome` as `prog`. -/
theorem optimizeBlock_sound (ctx : GuardIR) (prog : BlockProg) (env : Env) :
    evalGuard env ctx = true → evalBlock env (optimizeBlock ctx prog) = evalBlock env prog := by
  exact optimizeBlock_sound_aux ctx prog env

/-! ### Symbolic evaluation of the block optimizer on the parametric shapes -/

/-- With the hypothesis `nonZero d` available, the dual-division expression is fully lowered. -/
private theorem optimizeExpr_mkDualDivExpr_of_hasHyp {K : GuardIR} (x y d : PureExpr)
    (h : GuardIR.hasHyp (GuardIR.nf K) (.nonZero d) = true) :
    optimizeExpr K (mkDualDivExpr x y d) =
      Expr.mkBin .add .add (Expr.mkSafeDiv (.pure x) d) (.pure y) := by
  simp only [mkDualDivExpr, optimizeExpr, Expr.postFacts, Expr.asPure?, Expr.mkBin_pure_pure,
    Expr.mkDiv, GuardIR.entails_nonZero, GuardIR.nf, GuardIR.hasHyp_mkConj, h,
    Expr.mkSafeDiv_pure_mul_right, Bool.true_or, ↓reduceIte]

/-- With the hypothesis `nonZero d` available, `(x * d) / d` is cancelled to `x`. -/
private theorem optimizeExpr_mkCancelExpr_of_hasHyp {K : GuardIR} (x d : PureExpr)
    (h : GuardIR.hasHyp (GuardIR.nf K) (.nonZero d) = true) :
    optimizeExpr K (mkCancelExpr x d) = .pure x := by
  simp only [mkCancelExpr, optimizeExpr, Expr.postFacts, Expr.mkBin_pure_pure, Expr.mkDiv,
    GuardIR.entails_nonZero, GuardIR.nf, GuardIR.hasHyp_mkConj, h,
    Expr.mkSafeDiv_pure_mul_right, Bool.true_or, ↓reduceIte]

/-- An accepted candidate at the head of the list is a hypothesis of the collected context. -/
private theorem GuardIR.hasHyp_collect_head {p : GuardIR → Bool} {d : PureExpr}
    (gs : List GuardIR) (h : p (.nonZero d) = true) :
    GuardIR.hasHyp (GuardIR.nf (GuardIR.collect p (.nonZero d :: gs))) (.nonZero d) = true := by
  simp only [GuardIR.collect, h, ↓reduceIte, GuardIR.nf, GuardIR.hasHyp_mkConj, GuardIR.hasHyp,
    decide_true, Bool.true_or]

private theorem Expr.divOpCount_mkSafeDiv_pure_le (pn pd : PureExpr) :
    divOpCount (Expr.mkSafeDiv (.pure pn) pd) ≤ 1 := by
  simp only [Expr.mkSafeDiv]
  split
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1

/-- If the rewritten body establishes `nonZero d`, the dual-division return expression loses
    both checks and one division. -/
private theorem optimizeBlock_dualDiv_ret {ctx : GuardIR} {body : Stmt} (x y d : PureExpr)
    (h : GuardIR.entailsAfter (Stmt.optimize ctx .skip body) ctx (.nonZero d) = true) :
    checkedDivCount (optimizeBlock ctx { body := body, ret := mkDualDivExpr x y d }).ret = 0 ∧
      divOpCount (optimizeBlock ctx { body := body, ret := mkDualDivExpr x y d }).ret ≤ 1 ∧
      guardBranchCount (optimizeBlock ctx { body := body, ret := mkDualDivExpr x y d }).ret = 0 ∧
      ∀ env, execCheckCost env
        (optimizeBlock ctx { body := body, ret := mkDualDivExpr x y d }).ret = 0 := by
  have hret : (optimizeBlock ctx { body := body, ret := mkDualDivExpr x y d }).ret =
      Expr.mkBin .add .add (Expr.mkSafeDiv (.pure x) d) (.pure y) :=
    optimizeExpr_mkDualDivExpr_of_hasHyp x y d (GuardIR.hasHyp_collect_head _ h)
  have hc : checkedDivCount (Expr.mkBin .add .add (Expr.mkSafeDiv (.pure x) d) (.pure y)) = 0 := by
    rw [Expr.count_mkBin (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl),
      Expr.count_mkSafeDiv (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl)]
    rfl
  have hg : guardBranchCount (Expr.mkBin .add .add (Expr.mkSafeDiv (.pure x) d) (.pure y)) = 0 := by
    rw [Expr.count_mkBin (cnt := guardBranchCount) (fun _ => rfl) (fun _ _ => rfl),
      Expr.count_mkSafeDiv (cnt := guardBranchCount) (fun _ => rfl) (fun _ _ => rfl)]
    rfl
  have hd : divOpCount (Expr.mkBin .add .add (Expr.mkSafeDiv (.pure x) d) (.pure y)) ≤ 1 := by
    rw [Expr.count_mkBin (cnt := divOpCount) (fun _ => rfl) (fun _ _ => rfl)]
    exact Expr.divOpCount_mkSafeDiv_pure_le x d
  rw [hret]
  exact ⟨hc, hd, hg, fun _ => execCheckCost_eq_zero hc hg⟩

/-- Parametric Non-Zero Literal Divisor Elimination: On `{ body := .skip, ret := mkDualDivExpr num y (.lit n) }`
    with `n ≠ 0` under `.top`, `optimizeBlock` eliminates all checked divisions, cancels the algebraic
    factor, introduces zero guard branches, and reduces block runtime check cost to `0`. -/
theorem optimizeBlock_literal_div_elim_param (num y : PureExpr) (n : Int) (hn : n ≠ 0) (env : Env) :
    let prog : BlockProg := { body := .skip, ret := mkDualDivExpr num y (.lit n) }
    checkedDivCount (optimizeBlock .top prog).ret = 0 ∧
      divOpCount (optimizeBlock .top prog).ret ≤ 1 ∧
      guardBranchCount (optimizeBlock .top prog).ret = 0 ∧
      execBlockCheckCost env (optimizeBlock .top prog) = 0 := by
  intro prog
  have hfact : GuardIR.entailsAfter (Stmt.optimize .top .skip .skip) .top
      (.nonZero (.lit n)) = true := by
    show GuardIR.entailsAfter .skip .top (.nonZero (.lit n)) = true
    rw [GuardIR.entailsAfter_eq, synthesizeStmtGuardIR_lit_nonZero n hn]
    rfl
  obtain ⟨hc, hd, hg, hcost⟩ := optimizeBlock_dualDiv_ret num y (.lit n) hfact
  exact ⟨hc, hd, hg, (Nat.zero_add _).trans (hcost _)⟩

/-- Parametric Sequential Aliasing & Clobber Elimination: Under `.nonZero (.var x)` with `d ≠ x`,
    across `d := x; x := 0`, `optimizeBlock` preserves `d ≠ 0` despite clobbering `x` and eliminates
    all checked divisions on divisor `d` with zero runtime check cost. -/
theorem optimizeBlock_seq_clobber_elim_param (x d : VarId) (hxd : d ≠ x)
    (num y : PureExpr) (env : Env) :
    checkedDivCount (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret = 0 ∧
      divOpCount (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret ≤ 1 ∧
      guardBranchCount (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret = 0 ∧
      execBlockCheckCost env (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y d)) = 0 := by
  have hfact : GuardIR.entailsAfter
      (Stmt.optimize (.nonZero (.var x)) .skip (.seq (.assign d (.var x)) (.assign x (.lit 0))))
      (.nonZero (.var x)) (.nonZero (.var d)) = true := by
    have hwp : pullbackGuardIR (.assign x (.lit 0)) (.nonZero (.var d)) = .nonZero (.var d) := by
      simp only [pullbackGuardIR, GuardIR.subst, PureExpr.subst, ite_eq_right hxd]
    show GuardIR.entailsAfter (.assign d (.var x)) (.nonZero (.var x))
      (pullbackGuardIR (.assign x (.lit 0)) (.nonZero (.var d))) = true
    rw [hwp, GuardIR.entailsAfter_eq, synthesizeStmtGuardIR_assign_self]
    rfl
  obtain ⟨hc, hd, hg, hcost⟩ := optimizeBlock_dualDiv_ret num y (.var d) hfact
  exact ⟨hc, hd, hg, (Nat.zero_add _).trans (hcost _)⟩

/-- Parametric Clobbered Divisor Trap Preservation: Under `.nonZero (.var x)`, across `d := x; x := 0`,
    dividing by the clobbered variable `x` must still safely return `.trap` (never `.ub`). -/
theorem optimizeBlock_clobber_trap_param (x d : VarId) (num y : PureExpr)
    (env : Env) (hx : evalGuard env (.nonZero (.var x)) = true) :
    evalBlock env (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y x)) = .trap := by
  rw [optimizeBlock_sound _ _ env hx]
  apply evalExpr_mkDualDivExpr_trap
  show updateEnv (updateEnv env d (evalPure env (.var x))) x 0 x = 0
  simp only [updateEnv, decide_true, ↓reduceIte]

/-- Parametric Diamond CFG Safe-Divisor Elimination: Under `.top` with `n ≠ 0`, across
    `if x == 0 then d := n else d := x`, `optimizeBlock` proves `d ≠ 0` at the diamond join,
    eliminates all terminal checked divisions and guard branches, and reduces total block
    runtime check cost from `3` to `≤ 1`. -/
theorem optimizeBlock_diamond_elim_param (x d : VarId) (n : Int) (hn : n ≠ 0)
    (num y : PureExpr) (env : Env) :
    checkedDivCount (optimizeBlock .top (mkDiamondSafeBlock x d n num y)).ret = 0 ∧
      divOpCount (optimizeBlock .top (mkDiamondSafeBlock x d n num y)).ret ≤ 1 ∧
      guardBranchCount (optimizeBlock .top (mkDiamondSafeBlock x d n num y)).ret = 0 ∧
      execBlockCheckCost env (optimizeBlock .top (mkDiamondSafeBlock x d n num y)) ≤ 1 ∧
      execBlockCheckCost env (mkDiamondSafeBlock x d n num y) = 3 := by
  have hbody : Stmt.optimize .top .skip
      (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) =
      .ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)) := by
    simp only [Stmt.optimize, Stmt.mkIte, GuardIR.entailsAfter, pullbackGuardIR, GuardIR.norm,
      PureExpr.fold, GuardIR.mkEq, GuardIR.mkNonZero, GuardIR.mkNot, GuardIR.impN,
      GuardIR.entails, GuardIR.simplifyUnder, GuardIR.nf, GuardIR.mkImp, GuardIR.residual,
      GuardIR.hasHyp, GuardIR.isTop, Stmt.assign.injEq, reduceCtorEq, decide_false,
      Bool.false_or, Bool.false_eq_true, and_false, ↓reduceIte]
  have hfact : GuardIR.entailsAfter
      (Stmt.optimize .top .skip
        (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))))
      .top (.nonZero (.var d)) = true := by
    rw [hbody, GuardIR.entailsAfter_eq, synthesizeStmtGuardIR_diamond_safe x d n hn]
    rfl
  have hguard : ∀ env' : Env, stmtGuardCost env'
      (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) = 1 := by
    intro env'
    simp only [stmtGuardCost, guardEvalCost]
    cases evalGuard env' (.eq (.var x) (.lit 0)) <;> rfl
  obtain ⟨hc, hd, hg, hcost⟩ := optimizeBlock_dualDiv_ret num y (.var d) hfact
  refine ⟨hc, hd, hg, ?_, ?_⟩
  · have hopt : execBlockCheckCost env (optimizeBlock .top (mkDiamondSafeBlock x d n num y)) =
        1 + 0 := by
      show stmtGuardCost env (Stmt.optimize .top .skip
          (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)))) +
        execCheckCost _ (optimizeBlock .top (mkDiamondSafeBlock x d n num y)).ret = 1 + 0
      rw [hbody, hguard]
      exact congrArg (1 + ·) (hcost _)
    exact Nat.le_of_eq hopt
  · have hpost : evalPure
        (execStmt (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) env)
        (.var d) ≠ 0 := by
      show execStmt (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)))
        env d ≠ 0
      cases h0 : evalGuard env (.eq (.var x) (.lit 0)) with
      | true =>
        have hexec : execStmt
            (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) env =
            updateEnv env d n := by
          simp only [execStmt, h0, ↓reduceIte, evalPure]
        rw [hexec]
        simp only [updateEnv, decide_true, ↓reduceIte]
        exact hn
      | false =>
        have hexec : execStmt
            (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) env =
            updateEnv env d (env x) := by
          simp only [execStmt, h0, Bool.false_eq_true, ↓reduceIte, evalPure]
        rw [hexec]
        simp only [updateEnv, decide_true, ↓reduceIte]
        exact of_decide_eq_false h0
    show stmtGuardCost env
        (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) +
      execCheckCost
        (execStmt (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x))) env)
        (mkDualDivExpr num y (.var d)) = 3
    rw [hguard, execCheckCost_mkDualDivExpr num y hpost]

/-- Parametric Dead-Branch Pruning & Guarded Cancellation: Under `.nonZero p` with `n ≠ 0`,
    `optimizeBlock` prunes the unreachable zero-assignment branch in `mkDeadBranchBlock p d n y`,
    propagates `d ≠ 0`, cancels `(y * d) / d`, and achieves `0` total block check cost. -/
theorem optimizeBlock_dead_branch_elim_param (p : PureExpr) (d : VarId)
    (n : Int) (hn : n ≠ 0) (y : PureExpr) (env : Env) :
    checkedDivCount (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)).ret = 0 ∧
      divOpCount (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)).ret = 0 ∧
      execBlockCheckCost env (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)) = 0 := by
  have hbody : Stmt.optimize (.nonZero p) .skip
      (.ite (.nonZero p) (.assign d (.lit n)) (.assign d (.lit 0))) = .assign d (.lit n) := by
    have h : GuardIR.entailsAfter .skip (.nonZero p) (.nonZero p) = true :=
      GuardIR.entails_self _
    simp only [Stmt.optimize, h, ↓reduceIte]
  have hfact : GuardIR.entailsAfter (.assign d (.lit n)) (.nonZero p)
      (.nonZero (.var d)) = true := by
    have hwp : GuardIR.norm (pullbackGuardIR (.assign d (.lit n)) (.nonZero (.var d))) = .top := by
      simp only [pullbackGuardIR, GuardIR.subst, PureExpr.subst, GuardIR.norm, PureExpr.fold,
        GuardIR.mkNonZero, ite_eq_right hn, ↓reduceIte]
    unfold GuardIR.entailsAfter
    rw [hwp]
    rfl
  have hret : (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)).ret = .pure y := by
    show optimizeExpr
        (GuardIR.collect
          (GuardIR.entailsAfter
            (Stmt.optimize (.nonZero p) .skip
              (.ite (.nonZero p) (.assign d (.lit n)) (.assign d (.lit 0))))
            (.nonZero p))
          (Expr.factCandidates (mkCancelExpr y (.var d))))
        (mkCancelExpr y (.var d)) = .pure y
    rw [hbody]
    exact optimizeExpr_mkCancelExpr_of_hasHyp y (.var d) (GuardIR.hasHyp_collect_head _ hfact)
  have hb : (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)).body =
      .assign d (.lit n) := hbody
  refine ⟨by rw [hret]; rfl, by rw [hret]; rfl, ?_⟩
  show stmtGuardCost env (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)).body +
    execCheckCost (execStmt (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)).body env)
      (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)).ret = 0
  rw [hb, hret]
  rfl

/-! ## Milestone 3: Fuel-Indexed Imperative Loops, Inductive Strengthening & Preheader Guard Hoisting -/

/-! ### Loop passes

`havocGuardIR` quantifies a guard over every value of the accumulator,
`strengthenLoopInvariantIR` searches backwards for an inductive invariant, `hoistLoopGuardIR`
is the edge guard across the preheader, and `optimizeLoop` combines the three to remove
runtime checks from the loop body. -/

/-- Computable conservative universal-quantification pullback of a `GuardIR` across a write to `v`. -/
def havocGuardIR (v : VarId) (g : GuardIR) : GuardIR :=
  if guardMentionsVar v g then
    match g with
    | .conj g₁ g₂ => GuardIR.mkConj (havocGuardIR v g₁) (havocGuardIR v g₂)
    | .imp g₁ g₂ =>
      if guardMentionsVar v g₁ then havocGuardIR v g₂
      else GuardIR.mkImp g₁ (havocGuardIR v g₂)
    | g =>
      let g' := GuardIR.norm g
      if guardMentionsVar v g' then .bot else g'
  else g

/-! `strengthenLoopInvariantIR` tries four candidates in order and returns the first that it
can show closed under one loop iteration:

1. the target itself;
2. the target together with its exact backward image, when the conservative backward image
   of that new conjunct is already entailed (this keeps path conditions such as
   `c ⇨ nonZero d₁` when the branch condition and the sources are stable);
3. the same candidate under the literal one-step test on its exact backward image;
4. bounded backward saturation with a path-insensitive precondition, which finds the
   conjunctions needed by pipelines and by branches whose condition changes. -/

/-- Exact backward image of a guard across one abstract loop iteration
    (`accVar := *; latch`). -/
private def GuardIR.loopStep (accVar : VarId) (latch : Stmt) (g : GuardIR) : GuardIR :=
  havocGuardIR accVar (pullbackGuardIR latch g)

/-- `g` entails `step`, either literally (the Milestone 1 test, i.e.
    `synthesizeGuardIR g step = .top`) or after arithmetic normalisation of both sides.
    With `step` the backward image of `g`, this says that `g` is closed under one loop
    iteration. -/
private def GuardIR.closedBy (g step : GuardIR) : Bool :=
  GuardIR.entails g step || GuardIR.entails (GuardIR.norm g) (GuardIR.norm step)

/-- Number of connectives and atoms of a guard. -/
private def GuardIR.size : GuardIR → Nat
  | .conj g h | .imp g h => GuardIR.size g + GuardIR.size h + 1
  | _ => 1

/-- Path-insensitive join of the preconditions of the two arms of a branch: both are
    required, without recording the branch condition. Conjuncts of `b` already present in
    `a` are dropped. Distinct arms that are too large to compare, or whose join grows beyond
    a fixed budget, give up with `.bot`; this keeps the work of the conservative
    precondition bounded on branch-heavy latches. -/
private def GuardIR.join (a b : GuardIR) : GuardIR :=
  if a = b then a
  else if 512 < GuardIR.size a + GuardIR.size b then .bot
  else
    let j := GuardIR.mkConj a (GuardIR.residual a b)
    if 256 < GuardIR.size j then .bot else j

/-- Conservative precondition of `g` across a statement: assignments substitute, and a
    branch requires the preconditions of both arms. Unlike `pullbackGuardIR` it is not
    exact, but it keeps a conjunction of atoms a conjunction of atoms. -/
private def Stmt.pullbackAll : Stmt → GuardIR → GuardIR
  | .skip, g => g
  | .assign v rhs, g => GuardIR.subst v rhs g
  | .seq s₁ s₂, g => Stmt.pullbackAll s₁ (Stmt.pullbackAll s₂ g)
  | .ite _ t f, g => GuardIR.join (Stmt.pullbackAll t g) (Stmt.pullbackAll f g)

/-- What `g` still lacks to be closed under one loop iteration, computed with the
    conservative precondition: `.top` means that `g` is inductive. -/
private def GuardIR.backStep (accVar : VarId) (latch : Stmt) (g : GuardIR) : GuardIR :=
  GuardIR.simplifyUnder (GuardIR.norm g)
    (GuardIR.norm (havocGuardIR accVar (Stmt.pullbackAll latch g)))

/-- Bounded backward saturation: conjoins the missing part of the backward image until the
    candidate is closed. Gives up when the missing part is contradictory or the fuel runs
    out. -/
private def GuardIR.saturate (accVar : VarId) (latch : Stmt) : Nat → GuardIR → Option GuardIR
  | 0, _ => none
  | fuel + 1, g =>
    match GuardIR.backStep accVar latch g with
    | .top => some g
    | .bot => none
    | r => GuardIR.saturate accVar latch fuel (.conj g r)

/-- Computable bounded backward inductive-invariant strengthening across `(accVar, latch)` for `target`. -/
def strengthenLoopInvariantIR (accVar : VarId) (latch : Stmt) (target : GuardIR) : Option GuardIR :=
  let step := GuardIR.loopStep accVar latch target
  if GuardIR.closedBy target step then some target
  else
    let cand := GuardIR.conj target step
    if GuardIR.closedBy cand (havocGuardIR accVar (Stmt.pullbackAll latch step)) then some cand
    else if GuardIR.closedBy cand (GuardIR.loopStep accVar latch cand) then some cand
    else GuardIR.saturate accVar latch 8 target

/-- Computable preheader loop-hoisted guard synthesis across `init` from `ctx` to `inv`. -/
def hoistLoopGuardIR (init : Stmt) (ctx inv : GuardIR) : GuardIR :=
  synthesizeStmtGuardIR init ctx inv

/-- Removes repeated candidates, keeping the last occurrence of each. -/
private def dedupGuards : List GuardIR → List GuardIR
  | [] => []
  | c :: cs => if cs.contains c then dedupGuards cs else c :: dedupGuards cs

/-- The candidate facts that strengthen to an inductive invariant which is not
    contradictory, each paired with that invariant. -/
private def loopInvariants (accVar : VarId) (latch : Stmt) :
    List GuardIR → List (GuardIR × GuardIR)
  | [] => []
  | c :: cs =>
    match strengthenLoopInvariantIR accVar latch c with
    | some inv =>
      if GuardIR.isBot (GuardIR.norm inv) then loopInvariants accVar latch cs
      else (c, inv) :: loopInvariants accVar latch cs
    | none => loopInvariants accVar latch cs

/-- Conjunction of the facts, and conjunction of their invariants, over the pairs whose
    invariant passes `accept`. -/
private def selectFacts (accept : GuardIR → Bool) :
    List (GuardIR × GuardIR) → GuardIR × GuardIR
  | [] => (.top, .top)
  | p :: ps =>
    let rest := selectFacts accept ps
    if accept p.2 then (GuardIR.mkConj p.1 rest.1, GuardIR.mkConj p.2 rest.2) else rest

/-- The loop with its body and exit expression rewritten by `optimizeBlock` under the
    loop-header facts `F`: the body additionally knows that the loop condition holds, the
    exit expression that it fails. -/
private def WhileLoop.withFacts (F : GuardIR) (w : WhileLoop) : WhileLoop :=
  { w with
    body := (optimizeBlock (.conj F w.cond) { body := .skip, ret := w.body }).ret
    ret := (optimizeBlock (.conj F (.imp w.cond .bot)) { body := .skip, ret := w.ret }).ret }

/-- The loop rewritten under the facts whose invariant the entry context already
    establishes across `init`, i.e. whose hoisted guard is `.top`. -/
private def WhileLoop.staticVersion (ctx : GuardIR) (invs : List (GuardIR × GuardIR))
    (w : WhileLoop) : WhileLoop :=
  w.withFacts (selectFacts (fun inv => GuardIR.isTop (hoistLoopGuardIR w.init ctx inv)) invs).1

/-- Loop versioning. The facts that the body and the exit expression would profit from are
    strengthened to inductive invariants, and the conjunction of those invariants is pulled
    back across `init` and simplified under the entry context. If nothing is left (the
    hoisted guard is `.top`), the loop is rewritten under all facts. Otherwise the residual
    preheader guard selects at run time between that fast loop and the loop rewritten under
    the facts the context does establish. No branch is emitted when the two loops coincide
    (the extra facts buy nothing) or when the context refutes the residual guard (the fast
    loop is unreachable); the second loop is then used alone. -/
private def WhileLoop.version (ctx : GuardIR) (w : WhileLoop) : LoopProg :=
  let invs := loopInvariants w.accVar w.latch
    (dedupGuards (Expr.factCandidates w.body ++ Expr.factCandidates w.ret))
  let dyn := selectFacts (fun _ => true) invs
  match GuardIR.simplifyUnder (GuardIR.norm ctx)
      (GuardIR.norm (pullbackGuardIR w.init dyn.2)) with
  | .top => .whileLoop (w.withFacts dyn.1)
  | pre =>
    let fast := w.withFacts dyn.1
    let slow := w.staticVersion ctx invs
    if fast = slow then .whileLoop slow
    else if GuardIR.entails (GuardIR.norm ctx) (GuardIR.norm (.imp pre .bot)) then
      .whileLoop slow
    else .iteLoop pre (.whileLoop fast) (.whileLoop slow)

/-- Computable context-sensitive loop optimizer performing inductive invariant strengthening,
    preheader guard hoisting / loop versioning, and loop-body check elimination. -/
def optimizeLoop (ctx : GuardIR) (prog : LoopProg) : LoopProg :=
  match prog with
  | .whileLoop w => WhileLoop.version ctx w
  | .iteLoop g thenBr elseBr =>
    if GuardIR.entailsAfter .skip ctx g then optimizeLoop ctx thenBr
    else if GuardIR.entailsAfter .skip ctx (.imp g .bot) then optimizeLoop ctx elseBr
    else
      .iteLoop g (optimizeLoop (.conj ctx g) thenBr)
        (optimizeLoop (.conj ctx (.imp g .bot)) elseBr)

/-! ### Frame properties: variables a guard does not mention, variables a statement does not write -/

private theorem evalPure_updateEnv_of_not_mentions {v : VarId} {p : PureExpr}
    (h : pureMentionsVar v p = false) (env : Env) (val : Int) :
    evalPure (updateEnv env v val) p = evalPure env p := by
  induction p with
  | lit n => rfl
  | var w =>
    have hw : decide (w = v) = false := h
    show (if decide (w = v) then val else env w) = env w
    rw [hw]
    simp only [Bool.false_eq_true, ↓reduceIte]
  | add a b iha ihb =>
    have h' := Bool.or_eq_false_iff.mp (h : (pureMentionsVar v a || pureMentionsVar v b) = false)
    simp only [evalPure, iha h'.1, ihb h'.2]
  | sub a b iha ihb =>
    have h' := Bool.or_eq_false_iff.mp (h : (pureMentionsVar v a || pureMentionsVar v b) = false)
    simp only [evalPure, iha h'.1, ihb h'.2]
  | mul a b iha ihb =>
    have h' := Bool.or_eq_false_iff.mp (h : (pureMentionsVar v a || pureMentionsVar v b) = false)
    simp only [evalPure, iha h'.1, ihb h'.2]

/-- A guard that does not mention `v` cannot observe a write to `v`. -/
private theorem evalGuard_updateEnv_of_not_mentions {v : VarId} {g : GuardIR}
    (h : guardMentionsVar v g = false) (env : Env) (val : Int) :
    evalGuard (updateEnv env v val) g = evalGuard env g := by
  induction g with
  | top => rfl
  | bot => rfl
  | nonZero e =>
    simp only [evalGuard, evalPure_updateEnv_of_not_mentions (h : pureMentionsVar v e = false)]
  | eq a b =>
    have h' := Bool.or_eq_false_iff.mp (h : (pureMentionsVar v a || pureMentionsVar v b) = false)
    simp only [evalGuard, evalPure_updateEnv_of_not_mentions h'.1,
      evalPure_updateEnv_of_not_mentions h'.2]
  | conj g₁ g₂ ih₁ ih₂ =>
    have h' := Bool.or_eq_false_iff.mp
      (h : (guardMentionsVar v g₁ || guardMentionsVar v g₂) = false)
    simp only [evalGuard, ih₁ h'.1, ih₂ h'.2]
  | imp g₁ g₂ ih₁ ih₂ =>
    have h' := Bool.or_eq_false_iff.mp
      (h : (guardMentionsVar v g₁ || guardMentionsVar v g₂) = false)
    simp only [evalGuard, ih₁ h'.1, ih₂ h'.2]

private theorem PureExpr.subst_of_not_mentions {v : VarId} (r : PureExpr) {p : PureExpr}
    (h : pureMentionsVar v p = false) : PureExpr.subst v r p = p := by
  induction p with
  | lit n => rfl
  | var w =>
    have hw : ¬ w = v := of_decide_eq_false h
    simp only [PureExpr.subst, hw, ↓reduceIte]
  | add a b iha ihb =>
    have h' := Bool.or_eq_false_iff.mp (h : (pureMentionsVar v a || pureMentionsVar v b) = false)
    simp only [PureExpr.subst, iha h'.1, ihb h'.2]
  | sub a b iha ihb =>
    have h' := Bool.or_eq_false_iff.mp (h : (pureMentionsVar v a || pureMentionsVar v b) = false)
    simp only [PureExpr.subst, iha h'.1, ihb h'.2]
  | mul a b iha ihb =>
    have h' := Bool.or_eq_false_iff.mp (h : (pureMentionsVar v a || pureMentionsVar v b) = false)
    simp only [PureExpr.subst, iha h'.1, ihb h'.2]

/-- Substituting for a variable that the guard does not mention changes nothing. -/
private theorem GuardIR.subst_of_not_mentions {v : VarId} (r : PureExpr) {g : GuardIR}
    (h : guardMentionsVar v g = false) : GuardIR.subst v r g = g := by
  induction g with
  | top => rfl
  | bot => rfl
  | nonZero e =>
    simp only [GuardIR.subst, PureExpr.subst_of_not_mentions r (h : pureMentionsVar v e = false)]
  | eq a b =>
    have h' := Bool.or_eq_false_iff.mp (h : (pureMentionsVar v a || pureMentionsVar v b) = false)
    simp only [GuardIR.subst, PureExpr.subst_of_not_mentions r h'.1,
      PureExpr.subst_of_not_mentions r h'.2]
  | conj g₁ g₂ ih₁ ih₂ =>
    have h' := Bool.or_eq_false_iff.mp
      (h : (guardMentionsVar v g₁ || guardMentionsVar v g₂) = false)
    simp only [GuardIR.subst, ih₁ h'.1, ih₂ h'.2]
  | imp g₁ g₂ ih₁ ih₂ =>
    have h' := Bool.or_eq_false_iff.mp
      (h : (guardMentionsVar v g₁ || guardMentionsVar v g₂) = false)
    simp only [GuardIR.subst, ih₁ h'.1, ih₂ h'.2]

/-- A statement leaves every variable it does not write unchanged. -/
private theorem execStmt_of_not_writes {v : VarId} {s : Stmt} (h : stmtWritesVar v s = false) :
    ∀ env : Env, execStmt s env v = env v := by
  induction s with
  | skip => intro env; rfl
  | assign w rhs =>
    intro env
    have hw : ¬ w = v := of_decide_eq_false h
    have hvw : decide (v = w) = false := decide_eq_false (fun e => hw e.symm)
    show (if decide (v = w) then evalPure env rhs else env v) = env v
    rw [hvw]
    simp only [Bool.false_eq_true, ↓reduceIte]
  | seq s₁ s₂ ih₁ ih₂ =>
    intro env
    have h' := Bool.or_eq_false_iff.mp (h : (stmtWritesVar v s₁ || stmtWritesVar v s₂) = false)
    show execStmt s₂ (execStmt s₁ env) v = env v
    rw [ih₂ h'.2, ih₁ h'.1]
  | ite c t f iht ihf =>
    intro env
    have h' := Bool.or_eq_false_iff.mp (h : (stmtWritesVar v t || stmtWritesVar v f) = false)
    show (if evalGuard env c then execStmt t env else execStmt f env) v = env v
    cases evalGuard env c with
    | true => simp only [↓reduceIte]; exact iht h'.1 env
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ihf h'.2 env

/-! ### Semantics of `havocGuardIR` -/

/-- `havocGuardIR` returns a guard that does not mention the variable unchanged. -/
private theorem havocGuardIR_of_not_mentions {v : VarId} {g : GuardIR}
    (h : guardMentionsVar v g = false) : havocGuardIR v g = g := by
  rw [havocGuardIR.eq_def, h]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- Pointwise soundness of `havocGuardIR`: where the result holds, `g` holds for every
    value written to `v`. -/
private theorem evalGuard_havocGuardIR {v : VarId} {g : GuardIR} {env : Env}
    (h : evalGuard env (havocGuardIR v g) = true) (val : Int) :
    evalGuard (updateEnv env v val) g = true := by
  have hnm : ∀ g' : GuardIR, guardMentionsVar v g' = false →
      evalGuard env (havocGuardIR v g') = true → evalGuard (updateEnv env v val) g' = true := by
    intro g' hm h'
    rw [havocGuardIR_of_not_mentions hm] at h'
    rw [evalGuard_updateEnv_of_not_mentions hm]
    exact h'
  have hatom : ∀ g' : GuardIR,
      evalGuard env (if guardMentionsVar v (GuardIR.norm g') then .bot else GuardIR.norm g') = true →
      evalGuard (updateEnv env v val) g' = true := by
    intro g' h'
    cases hm : guardMentionsVar v (GuardIR.norm g') with
    | true =>
      rw [hm] at h'
      exact absurd h' (by simp [evalGuard])
    | false =>
      rw [hm] at h'
      simp only [Bool.false_eq_true, ↓reduceIte] at h'
      rw [← GuardIR.evalGuard_norm, evalGuard_updateEnv_of_not_mentions hm]
      exact h'
  induction g with
  | top => rfl
  | bot => exact hnm .bot rfl h
  | nonZero e =>
    cases hm : guardMentionsVar v (.nonZero e) with
    | false => exact hnm _ hm h
    | true =>
      rw [havocGuardIR.eq_def, hm] at h
      simp only [↓reduceIte] at h
      exact hatom _ h
  | eq a b =>
    cases hm : guardMentionsVar v (.eq a b) with
    | false => exact hnm _ hm h
    | true =>
      rw [havocGuardIR.eq_def, hm] at h
      simp only [↓reduceIte] at h
      exact hatom _ h
  | conj g₁ g₂ ih₁ ih₂ =>
    cases hm : guardMentionsVar v (.conj g₁ g₂) with
    | false => exact hnm _ hm h
    | true =>
      rw [havocGuardIR, hm] at h
      simp only [↓reduceIte, GuardIR.evalGuard_mkConj, Bool.and_eq_true] at h
      show (evalGuard (updateEnv env v val) g₁ && evalGuard (updateEnv env v val) g₂) = true
      rw [ih₁ h.1, ih₂ h.2]
      rfl
  | imp g₁ g₂ _ ih₂ =>
    cases hm : guardMentionsVar v (.imp g₁ g₂) with
    | false => exact hnm _ hm h
    | true =>
      rw [havocGuardIR, hm] at h
      simp only [↓reduceIte] at h
      show (!evalGuard (updateEnv env v val) g₁ || evalGuard (updateEnv env v val) g₂) = true
      cases hm₁ : guardMentionsVar v g₁ with
      | true =>
        rw [hm₁] at h
        simp only [↓reduceIte] at h
        rw [ih₂ h]
        exact Bool.or_true _
      | false =>
        rw [hm₁] at h
        simp only [Bool.false_eq_true, ↓reduceIte, GuardIR.evalGuard_mkImp] at h
        rw [evalGuard_updateEnv_of_not_mentions hm₁]
        cases h₁ : evalGuard env g₁ with
        | false => rfl
        | true =>
          rw [h₁] at h
          rw [ih₂ h]
          rfl

/-! ### Semantics of the conservative precondition and of backward saturation -/

private theorem GuardIR.evalGuard_join {env : Env} {a b : GuardIR}
    (h : evalGuard env (GuardIR.join a b) = true) :
    evalGuard env a = true ∧ evalGuard env b = true := by
  unfold GuardIR.join at h
  split at h
  · next hab => subst hab; exact ⟨h, h⟩
  · split at h
    · exact absurd h (by simp [evalGuard])
    · simp only [] at h
      split at h
      · exact absurd h (by simp [evalGuard])
      · rw [GuardIR.evalGuard_mkConj, Bool.and_eq_true] at h
        refine ⟨h.1, ?_⟩
        rw [← GuardIR.evalGuard_residual h.1 b]
        exact h.2

/-- Soundness of the conservative precondition: it implies the exact one. -/
private theorem Stmt.evalGuard_pullbackAll (s : Stmt) :
    ∀ (g : GuardIR) (env : Env), evalGuard env (Stmt.pullbackAll s g) = true →
      evalGuard (execStmt s env) g = true := by
  induction s with
  | skip => intro g env h; exact h
  | assign v rhs =>
    intro g env h
    rw [Stmt.pullbackAll, GuardIR.evalGuard_subst] at h
    exact h
  | seq s₁ s₂ ih₁ ih₂ =>
    intro g env h
    exact ih₂ g _ (ih₁ _ env h)
  | ite c t f iht ihf =>
    intro g env h
    have hj := GuardIR.evalGuard_join h
    show evalGuard (if evalGuard env c then execStmt t env else execStmt f env) g = true
    cases evalGuard env c with
    | true => simp only [↓reduceIte]; exact iht g env hj.1
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ihf g env hj.2

/-- Soundness of the Milestone 1 entailment test. -/
private theorem GuardIR.entails_sound {c g : GuardIR} {env : Env}
    (h : GuardIR.entails c g = true) (hc : evalGuard env c = true) : evalGuard env g = true := by
  have htop : GuardIR.simplifyUnder c g = .top := GuardIR.isTop_iff.mp h
  have := evalGuard_simplifyUnder hc g
  rw [htop] at this
  exact this.symm

/-- The exact backward image is sound for one concrete loop iteration. -/
private theorem GuardIR.evalGuard_loopStep {accVar : VarId} {latch : Stmt} {g : GuardIR}
    {env : Env} (h : evalGuard env (GuardIR.loopStep accVar latch g) = true) (val : Int) :
    evalGuard (execStmt latch (updateEnv env accVar val)) g = true := by
  have := evalGuard_havocGuardIR h val
  rw [evalGuard_pullbackGuardIR] at this
  exact this

/-- Soundness of the closure test: `step` holds wherever `g` does. -/
private theorem GuardIR.closedBy_sound {g step : GuardIR} {env : Env}
    (h : GuardIR.closedBy g step = true) (hg : evalGuard env g = true) :
    evalGuard env step = true := by
  unfold GuardIR.closedBy at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact GuardIR.entails_sound h hg
  · have := GuardIR.entails_sound (env := env) h (by rw [GuardIR.evalGuard_norm]; exact hg)
    rw [GuardIR.evalGuard_norm] at this
    exact this

/-- A vanishing conservative residual means the guard is preserved by every iteration. -/
private theorem GuardIR.backStep_sound {accVar : VarId} {latch : Stmt} {g : GuardIR}
    (h : GuardIR.backStep accVar latch g = .top) (env : Env) (val : Int)
    (hg : evalGuard env g = true) :
    evalGuard (execStmt latch (updateEnv env accVar val)) g = true := by
  have hn : evalGuard env (GuardIR.norm g) = true := by rw [GuardIR.evalGuard_norm]; exact hg
  have := evalGuard_simplifyUnder hn
    (GuardIR.norm (havocGuardIR accVar (Stmt.pullbackAll latch g)))
  unfold GuardIR.backStep at h
  rw [h, GuardIR.evalGuard_norm] at this
  exact Stmt.evalGuard_pullbackAll latch g _ (evalGuard_havocGuardIR this.symm val)

/-- Every result of the saturation implies its starting point and is preserved by every
    concrete loop iteration. -/
private theorem GuardIR.saturate_sound {accVar : VarId} {latch : Stmt} :
    ∀ (fuel : Nat) (g inv : GuardIR), GuardIR.saturate accVar latch fuel g = some inv →
      (∀ env, evalGuard env inv = true → evalGuard env g = true) ∧
        ∀ env val, evalGuard env inv = true →
          evalGuard (execStmt latch (updateEnv env accVar val)) inv = true := by
  intro fuel
  induction fuel with
  | zero => intro g inv h; exact absurd h (by simp [GuardIR.saturate])
  | succ fuel ih =>
    intro g inv h
    rw [GuardIR.saturate] at h
    split at h
    · next hr =>
      have hinv : g = inv := Option.some.inj h
      subst hinv
      exact ⟨fun _ hg => hg, fun env val hg => GuardIR.backStep_sound hr env val hg⟩
    · exact absurd h (by simp)
    · have := ih _ inv h
      refine ⟨fun env hinv => ?_, this.2⟩
      have hc := this.1 env hinv
      simp only [evalGuard, Bool.and_eq_true] at hc
      exact hc.1

/-- Concrete soundness of `strengthenLoopInvariantIR`: the result implies the target and is
    preserved by every loop iteration, whatever value the body writes to the accumulator. -/
private theorem strengthenLoopInvariantIR_sound {accVar : VarId} {latch : Stmt}
    {target inv : GuardIR} (h : strengthenLoopInvariantIR accVar latch target = some inv) :
    (∀ env, evalGuard env inv = true → evalGuard env target = true) ∧
      ∀ env val, evalGuard env inv = true →
        evalGuard (execStmt latch (updateEnv env accVar val)) inv = true := by
  unfold strengthenLoopInvariantIR at h
  simp only [] at h
  split at h
  · next hc =>
    have hinv : target = inv := Option.some.inj h
    subst hinv
    exact ⟨fun _ hg => hg, fun env val hg =>
      GuardIR.evalGuard_loopStep (GuardIR.closedBy_sound hc hg) val⟩
  · split at h
    · next hc =>
      have hinv := Option.some.inj h
      subst hinv
      refine ⟨fun env hg => ?_, fun env val hg => ?_⟩
      · simp only [evalGuard, Bool.and_eq_true] at hg
        exact hg.1
      · have hg' := hg
        simp only [evalGuard, Bool.and_eq_true] at hg'
        exact GuardIR.evalGuard_conj_intro (GuardIR.evalGuard_loopStep hg'.2 val)
          (Stmt.evalGuard_pullbackAll latch _ _
            (evalGuard_havocGuardIR (GuardIR.closedBy_sound hc hg) val))
    · split at h
      · next hc =>
        have hinv := Option.some.inj h
        subst hinv
        refine ⟨fun env hg => ?_, fun env val hg =>
          GuardIR.evalGuard_loopStep (GuardIR.closedBy_sound hc hg) val⟩
        simp only [evalGuard, Bool.and_eq_true] at hg
        exact hg.1
      · exact GuardIR.saturate_sound _ _ _ h

/-! ### Milestone 3 target theorems: havoc and inductive strengthening -/

/-- Iterated State-Transfer Pullback Characterization: The `n`-fold `CFGTransfer.iterate` pullback
    of `stateTransfer step` at `Q` and `s` holds if and only if `Q (step^[n] s)` holds. -/
theorem stateTransfer_iterate_pullback_iff (step : S → S) (Q : S → Prop) (n : ℕ) (s : S) :
    ((stateTransfer step).iterate n).pullback Q s ↔ Q (step^[n] s) := by
  induction n generalizing Q with
  | zero => exact Iff.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih (fun s' => Q (step s'))

/-- Soundness of `havocGuardIR`: Denotation implies the semantic universal pullback `(havocTransfer v).pullback`. -/
theorem havocGuardIR_sound (v : VarId) (g : GuardIR) :
    denoteGuard (havocGuardIR v g) ≤ (havocTransfer v).pullback (denoteGuard g) := by
  intro env h val
  exact evalGuard_havocGuardIR h val

/-- Exactness of `havocGuardIR` on Non-Mentioning Guards: When `guardMentionsVar v g = false`,
    `havocGuardIR v g` denotes the exact semantic pullback `(havocTransfer v).pullback (denoteGuard g)`. -/
theorem havocGuardIR_exact_of_nonMention (v : VarId) (g : GuardIR)
    (h : guardMentionsVar v g = false) :
    denoteGuard (havocGuardIR v g) = (havocTransfer v).pullback (denoteGuard g) := by
  rw [havocGuardIR_of_not_mentions h]
  funext env
  apply propext
  constructor
  · intro hg val
    show evalGuard (updateEnv env v val) g = true
    rw [evalGuard_updateEnv_of_not_mentions h]
    exact hg
  · intro hall
    have h0 : evalGuard (updateEnv env v 0) g = true := hall 0
    rw [evalGuard_updateEnv_of_not_mentions h] at h0
    exact h0

/-- Categorical Inductive Soundness of `strengthenLoopInvariantIR`: Any synthesized `some inv`
    satisfies `IsInductiveFor (loopStepTransfer accVar latch) (denoteGuard inv) (denoteGuard target)`. -/
theorem strengthenLoopInvariantIR_inductive (accVar : VarId) (latch : Stmt)
    (target inv : GuardIR) (h : strengthenLoopInvariantIR accVar latch target = some inv) :
    IsInductiveFor (loopStepTransfer accVar latch) (denoteGuard inv) (denoteGuard target) := by
  have hs := strengthenLoopInvariantIR_sound h
  refine And.intro ?_ (fun env hinv => hs.1 env hinv)
  rintro env' ⟨env₁, hstep, env, val, hupd, hinv⟩
  subst hupd
  subst hstep
  exact hs.2 env val hinv

/-! ### Guards that hold whenever a set of variables is non-zero

The invariants found for the divisor-copying latches below are not always syntactically
predictable (a branch condition is arbitrary), but they always belong to the following
class, which is all that coverage and preheader discharge need. -/

/-- `GuardIR.Pos P g`: `g` is built from `.top`, atoms `nonZero (var u)` with `P u`,
    conjunctions, and implications with an arbitrary hypothesis. -/
private inductive GuardIR.Pos (P : VarId → Prop) : GuardIR → Prop
  | top : GuardIR.Pos P .top
  | var {u : VarId} (hu : P u) : GuardIR.Pos P (.nonZero (.var u))
  | conj {g h : GuardIR} (hg : GuardIR.Pos P g) (hh : GuardIR.Pos P h) :
    GuardIR.Pos P (.conj g h)
  | imp (a : GuardIR) {g : GuardIR} (hg : GuardIR.Pos P g) : GuardIR.Pos P (.imp a g)

private theorem GuardIR.Pos.mono {P Q : VarId → Prop} {g : GuardIR} (h : GuardIR.Pos P g)
    (hPQ : ∀ u, P u → Q u) : GuardIR.Pos Q g := by
  induction h with
  | top => exact .top
  | var hu => exact .var (hPQ _ hu)
  | conj _ _ ihg ihh => exact .conj ihg ihh
  | imp a _ ih => exact .imp a ih

/-- A `Pos P` guard holds wherever every variable of `P` is non-zero. -/
private theorem GuardIR.Pos.eval {P : VarId → Prop} {g : GuardIR} (h : GuardIR.Pos P g)
    {env : Env} (henv : ∀ u, P u → env u ≠ 0) : evalGuard env g = true := by
  induction h with
  | top => rfl
  | var hu => exact decide_eq_true (henv _ hu)
  | @conj g h _ _ ihg ihh =>
    show (evalGuard env g && evalGuard env h) = true
    rw [ihg, ihh]
    rfl
  | @imp a g _ ih =>
    show (!evalGuard env a || evalGuard env g) = true
    rw [ih]
    exact Bool.or_true _

private theorem GuardIR.Pos.mkConj {P : VarId → Prop} {a b : GuardIR}
    (ha : GuardIR.Pos P a) (hb : GuardIR.Pos P b) : GuardIR.Pos P (GuardIR.mkConj a b) := by
  unfold GuardIR.mkConj
  split
  · exact hb
  · exact ha
  · exact ha
  · exact hb
  · exact .conj ha hb

private theorem GuardIR.Pos.mkImp {P : VarId → Prop} (a : GuardIR) {g : GuardIR}
    (hg : GuardIR.Pos P g) : GuardIR.Pos P (GuardIR.mkImp a g) := by
  unfold GuardIR.mkImp
  split
  · exact .top
  · exact hg
  · exact .top
  · exact .imp a hg

private theorem GuardIR.Pos.nf {P : VarId → Prop} {g : GuardIR} (h : GuardIR.Pos P g) :
    GuardIR.Pos P (GuardIR.nf g) := by
  induction h with
  | top => exact .top
  | var hu => exact .var hu
  | conj _ _ ihg ihh => exact GuardIR.Pos.mkConj ihg ihh
  | imp a _ ih => exact GuardIR.Pos.mkImp _ ih

private theorem GuardIR.Pos.impN {P : VarId → Prop} (a : GuardIR) {g : GuardIR}
    (hg : GuardIR.Pos P g) : GuardIR.Pos P (GuardIR.impN a g) := by
  unfold GuardIR.impN
  split
  · exact .top
  · split
    · cases hg
    · exact GuardIR.Pos.mkImp a hg

private theorem GuardIR.Pos.norm {P : VarId → Prop} {g : GuardIR} (h : GuardIR.Pos P g) :
    GuardIR.Pos P (GuardIR.norm g) := by
  induction h with
  | top => exact .top
  | var hu => exact .var hu
  | conj _ _ ihg ihh => exact GuardIR.Pos.mkConj ihg ihh
  | imp a _ ih => exact GuardIR.Pos.impN _ ih

/-- Copying `x` into `v`: afterwards the guard depends on `x` and on the old variables other
    than `v`. -/
private theorem GuardIR.Pos.subst_var {P : VarId → Prop} {g : GuardIR} (h : GuardIR.Pos P g)
    (v x : VarId) :
    GuardIR.Pos (fun u => u = x ∨ (P u ∧ u ≠ v)) (GuardIR.subst v (.var x) g) := by
  induction h with
  | top => exact .top
  | @var u hu =>
    show GuardIR.Pos _ (.nonZero (if u = v then .var x else .var u))
    split
    · exact .var (Or.inl rfl)
    · next hne => exact .var (Or.inr ⟨hu, hne⟩)
  | conj _ _ ihg ihh => exact .conj ihg ihh
  | imp a _ ih => exact .imp _ ih

private theorem GuardIR.Pos.subst_closed {P : VarId → Prop} {g : GuardIR}
    (h : GuardIR.Pos P g) (v : VarId) {x : VarId} (hx : P x) :
    GuardIR.Pos P (GuardIR.subst v (.var x) g) :=
  (h.subst_var v x).mono (fun _ hu => hu.elim (fun e => e ▸ hx) (fun h' => h'.1))

private theorem GuardIR.Pos.subst_frame {P : VarId → Prop} {g : GuardIR}
    (h : GuardIR.Pos P g) {v : VarId} (hv : ∀ u, P u → u ≠ v) (r : PureExpr) :
    GuardIR.Pos P (GuardIR.subst v r g) := by
  induction h with
  | top => exact .top
  | @var u hu =>
    simp only [GuardIR.subst, PureExpr.subst, hv u hu, ↓reduceIte]
    exact .var hu
  | conj _ _ ihg ihh => exact .conj ihg ihh
  | imp a _ ih => exact .imp _ ih

private theorem GuardIR.Pos.branch {P : VarId → Prop} (c : GuardIR) {gt gf : GuardIR}
    (ht : GuardIR.Pos P gt) (hf : GuardIR.Pos P gf) :
    GuardIR.Pos P (GuardIR.branch c gt gf) := by
  unfold GuardIR.branch
  simp only []
  split
  · exact ht.norm
  · exact GuardIR.Pos.mkConj (GuardIR.Pos.impN _ ht.norm) (GuardIR.Pos.impN _ hf.norm)

/-- The exact precondition across a statement that writes no variable of `P` stays in the
    class, whatever its branch conditions are. -/
private theorem GuardIR.Pos.pullback_frame {P : VarId → Prop} {s : Stmt}
    (hs : ∀ u, P u → stmtWritesVar u s = false) :
    ∀ {g : GuardIR}, GuardIR.Pos P g → GuardIR.Pos P (pullbackGuardIR s g) := by
  induction s with
  | skip => intro g hg; exact hg
  | assign v rhs =>
    intro g hg
    exact hg.subst_frame (fun u hu e => (of_decide_eq_false (hs u hu)) e.symm) rhs
  | seq s₁ s₂ ih₁ ih₂ =>
    intro g hg
    exact ih₁ (fun u hu => (Bool.or_eq_false_iff.mp (hs u hu)).1)
      (ih₂ (fun u hu => (Bool.or_eq_false_iff.mp (hs u hu)).2) hg)
  | ite c t f iht ihf =>
    intro g hg
    exact GuardIR.Pos.branch c
      (iht (fun u hu => (Bool.or_eq_false_iff.mp (hs u hu)).1) hg)
      (ihf (fun u hu => (Bool.or_eq_false_iff.mp (hs u hu)).2) hg)

private theorem GuardIR.Pos.havoc {P : VarId → Prop} {g : GuardIR} (h : GuardIR.Pos P g)
    {v : VarId} (hv : ¬ P v) : GuardIR.Pos P (havocGuardIR v g) := by
  induction h with
  | top =>
    rw [havocGuardIR_of_not_mentions rfl]
    exact .top
  | @var u hu =>
    have hm : guardMentionsVar v (.nonZero (.var u)) = false :=
      decide_eq_false (fun e => hv (e ▸ hu))
    rw [havocGuardIR_of_not_mentions hm]
    exact .var hu
  | @conj g h hg hh ihg ihh =>
    cases hm : guardMentionsVar v (.conj g h) with
    | false =>
      rw [havocGuardIR_of_not_mentions hm]
      exact .conj hg hh
    | true =>
      rw [havocGuardIR, hm]
      simp only [↓reduceIte]
      exact GuardIR.Pos.mkConj ihg ihh
  | @imp a g hg ih =>
    cases hm : guardMentionsVar v (.imp a g) with
    | false =>
      rw [havocGuardIR_of_not_mentions hm]
      exact .imp a hg
    | true =>
      rw [havocGuardIR, hm]
      simp only [↓reduceIte]
      split
      · exact ih
      · exact GuardIR.Pos.mkImp a ih

/-- A `Pos P` target is discharged by any context in which every `nonZero (var u)`, `P u`, is
    a hypothesis. -/
private theorem GuardIR.Pos.residual_eq_top {P : VarId → Prop} {g : GuardIR}
    (h : GuardIR.Pos P g) :
    ∀ {c : GuardIR}, (∀ u, P u → GuardIR.hasHyp c (.nonZero (.var u)) = true) →
      GuardIR.residual c g = .top := by
  induction h with
  | top => intro c _; rfl
  | var hu =>
    intro c hc
    simp only [GuardIR.residual, hc _ hu, ↓reduceIte]
  | @conj g h _ _ ihg ihh =>
    intro c hc
    have h₂ : GuardIR.residual (.conj c g) h = .top :=
      ihh (fun u hu => by simp only [GuardIR.hasHyp, hc u hu, Bool.true_or])
    simp only [GuardIR.residual, ihg hc, h₂]
    rfl
  | @imp a g _ ih =>
    intro c hc
    have h₂ : GuardIR.residual (.conj c a) g = .top :=
      ih (fun u hu => by simp only [GuardIR.hasHyp, hc u hu, Bool.true_or])
    simp only [GuardIR.residual, h₂, GuardIR.mkImp_top_right, ite_self]

/-- Preheader discharge: a `Pos Q` guard is entailed, after normalisation, by any context
    that lists `nonZero (var u)` for every `Q u` among its hypotheses. -/
private theorem synthesizeGuardIR_norm_eq_top_of_pos {Q : VarId → Prop} {ctx g : GuardIR}
    (hg : GuardIR.Pos Q g)
    (hctx : ∀ u, Q u →
      GuardIR.hasHyp (GuardIR.nf (GuardIR.norm ctx)) (.nonZero (.var u)) = true) :
    synthesizeGuardIR (GuardIR.norm ctx) (GuardIR.norm g) = .top := by
  have hres : GuardIR.simplifyUnder (GuardIR.norm ctx) (GuardIR.norm g) = .top :=
    hg.norm.nf.residual_eq_top hctx
  unfold synthesizeGuardIR
  rw [hres]

private theorem hoistLoopGuardIR_assign1_of_pos {d : VarId} {inv : GuardIR}
    (hinv : GuardIR.Pos (fun u => u = d) inv) (x : VarId) :
    hoistLoopGuardIR (.assign d (.var x)) (.nonZero (.var x)) inv = .top := by
  have hp : GuardIR.Pos (fun u => u = x) (pullbackGuardIR (.assign d (.var x)) inv) :=
    (hinv.subst_var d x).mono (fun u hu => hu.elim id (fun h => absurd h.1 h.2))
  refine synthesizeGuardIR_norm_eq_top_of_pos hp (fun u hu => ?_)
  subst hu
  exact decide_eq_true rfl

private theorem hoistLoopGuardIR_assign2_of_pos {d e : VarId} {inv : GuardIR}
    (hinv : GuardIR.Pos (fun u => u = d ∨ u = e) inv) (x z : VarId) :
    hoistLoopGuardIR (.seq (.assign d (.var x)) (.assign e (.var z)))
      (.conj (.nonZero (.var x)) (.nonZero (.var z))) inv = .top := by
  have hp : GuardIR.Pos (fun u => u = x ∨ u = z)
      (pullbackGuardIR (.seq (.assign d (.var x)) (.assign e (.var z))) inv) :=
    ((hinv.subst_var e z).subst_var d x).mono (by
      rintro u (hu | ⟨hu | ⟨hu | hu, hne⟩, hne'⟩)
      · exact Or.inl hu
      · exact Or.inr hu
      · exact absurd hu hne'
      · exact absurd hu hne)
  refine synthesizeGuardIR_norm_eq_top_of_pos hp (fun u hu => ?_)
  show (decide (GuardIR.nonZero (.var x) = GuardIR.nonZero (.var u)) ||
    decide (GuardIR.nonZero (.var z) = GuardIR.nonZero (.var u))) = true
  rcases hu with rfl | rfl
  · rw [decide_eq_true rfl]; rfl
  · rw [decide_eq_true (rfl : GuardIR.nonZero (.var u) = GuardIR.nonZero (.var u))]
    exact Bool.or_true _

private theorem hoistLoopGuardIR_assign3_of_pos {d d₁ d₂ : VarId} {inv : GuardIR}
    (hinv : GuardIR.Pos (fun u => u = d ∨ u = d₁ ∨ u = d₂) inv) (x w z : VarId) :
    hoistLoopGuardIR
      (.seq (.assign d (.var x)) (.seq (.assign d₁ (.var w)) (.assign d₂ (.var z))))
      (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z))))
      inv = .top := by
  have hp : GuardIR.Pos (fun u => u = x ∨ u = w ∨ u = z)
      (pullbackGuardIR
        (.seq (.assign d (.var x)) (.seq (.assign d₁ (.var w)) (.assign d₂ (.var z)))) inv) :=
    (((hinv.subst_var d₂ z).subst_var d₁ w).subst_var d x).mono (by
      rintro u (hu | ⟨hu | ⟨hu | ⟨hu | hu | hu, hne₂⟩, hne₁⟩, hne⟩)
      · exact Or.inl hu
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr hu)
      · exact absurd hu hne
      · exact absurd hu hne₁
      · exact absurd hu hne₂)
  refine synthesizeGuardIR_norm_eq_top_of_pos hp (fun u hu => ?_)
  show (decide (GuardIR.nonZero (.var x) = GuardIR.nonZero (.var u)) ||
    (decide (GuardIR.nonZero (.var w) = GuardIR.nonZero (.var u)) ||
      decide (GuardIR.nonZero (.var z) = GuardIR.nonZero (.var u)))) = true
  rcases hu with rfl | rfl | rfl
  · rw [decide_eq_true rfl]; rfl
  · rw [decide_eq_true (rfl : GuardIR.nonZero (.var u) = GuardIR.nonZero (.var u))]
    simp only [Bool.true_or, Bool.or_true]
  · rw [decide_eq_true (rfl : GuardIR.nonZero (.var u) = GuardIR.nonZero (.var u))]
    simp only [Bool.or_true]

/-! ### Strengthening on divisor-copying latches -/

/-- Across a statement that does not write `d`, the exact precondition of `nonZero (var d)`
    is the guard itself. -/
private theorem pullbackGuardIR_nonZero_var_of_not_writes {d : VarId} {s : Stmt}
    (h : stmtWritesVar d s = false) :
    pullbackGuardIR s (.nonZero (.var d)) = .nonZero (.var d) := by
  induction s with
  | skip => rfl
  | assign v rhs =>
    have hv : ¬ d = v := fun e => (of_decide_eq_false h) e.symm
    simp only [pullbackGuardIR, GuardIR.subst, PureExpr.subst, hv, ↓reduceIte]
  | seq s₁ s₂ ih₁ ih₂ =>
    have h' := Bool.or_eq_false_iff.mp (h : (stmtWritesVar d s₁ || stmtWritesVar d s₂) = false)
    rw [pullbackGuardIR, ih₂ h'.2, ih₁ h'.1]
  | ite c t f iht ihf =>
    have h' := Bool.or_eq_false_iff.mp (h : (stmtWritesVar d t || stmtWritesVar d f) = false)
    rw [pullbackGuardIR, iht h'.1, ihf h'.2]
    simp only [GuardIR.branch, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero, ↓reduceIte]

/-- A divisor that the latch never writes is its own inductive invariant. -/
private theorem strengthenLoopInvariantIR_frame {accVar d : VarId} {latch : Stmt}
    (hda : d ≠ accVar) (hw : stmtWritesVar d latch = false) :
    strengthenLoopInvariantIR accVar latch (.nonZero (.var d)) = some (.nonZero (.var d)) := by
  have hstep : GuardIR.loopStep accVar latch (.nonZero (.var d)) = .nonZero (.var d) := by
    unfold GuardIR.loopStep
    rw [pullbackGuardIR_nonZero_var_of_not_writes hw]
    exact havocGuardIR_of_not_mentions (decide_eq_false hda)
  have hclosed : GuardIR.closedBy (.nonZero (.var d)) (.nonZero (.var d)) = true := by
    unfold GuardIR.closedBy
    rw [GuardIR.entails_self]
    rfl
  unfold strengthenLoopInvariantIR
  simp only [hstep, hclosed, ↓reduceIte]

/-- If the target, its exact backward image and the result of the saturation all stay in
    `Pos P`, so does whatever `strengthenLoopInvariantIR` returns. -/
private theorem strengthenLoopInvariantIR_pos {P : VarId → Prop} {accVar : VarId}
    {latch : Stmt} {target : GuardIR} (htarget : GuardIR.Pos P target)
    (hstep : GuardIR.Pos P (pullbackGuardIR latch target)) (hacc : ¬ P accVar)
    (hsat : ∃ inv, GuardIR.saturate accVar latch 8 target = some inv ∧ GuardIR.Pos P inv) :
    ∃ inv, strengthenLoopInvariantIR accVar latch target = some inv ∧ GuardIR.Pos P inv := by
  unfold strengthenLoopInvariantIR
  simp only []
  split
  · exact ⟨target, rfl, htarget⟩
  · split
    · exact ⟨_, rfl, .conj htarget (hstep.havoc hacc)⟩
    · split
      · exact ⟨_, rfl, .conj htarget (hstep.havoc hacc)⟩
      · exact hsat

/-- The conservative precondition across a statement that writes no variable the guard
    mentions is the guard itself. -/
private theorem Stmt.pullbackAll_of_not_writes {s : Stmt} {g : GuardIR}
    (h : ∀ v, guardMentionsVar v g = true → stmtWritesVar v s = false) :
    Stmt.pullbackAll s g = g := by
  induction s with
  | skip => rfl
  | assign v rhs =>
    show GuardIR.subst v rhs g = g
    refine GuardIR.subst_of_not_mentions rhs ?_
    cases hm : guardMentionsVar v g with
    | false => rfl
    | true => exact absurd rfl (of_decide_eq_false (h v hm))
  | seq s₁ s₂ ih₁ ih₂ =>
    rw [Stmt.pullbackAll, ih₂ (fun v hv => (Bool.or_eq_false_iff.mp (h v hv)).2),
      ih₁ (fun v hv => (Bool.or_eq_false_iff.mp (h v hv)).1)]
  | ite c t f iht ihf =>
    rw [Stmt.pullbackAll, iht (fun v hv => (Bool.or_eq_false_iff.mp (h v hv)).1),
      ihf (fun v hv => (Bool.or_eq_false_iff.mp (h v hv)).2)]
    unfold GuardIR.join
    simp only [↓reduceIte]

/-- Conjunctions of atoms `nonZero (var u)` with `P u`: the shape of the invariants that
    the saturation builds on divisor-copying latches. -/
private inductive GuardIR.NZTree (P : VarId → Prop) : GuardIR → Prop
  | var {u : VarId} (hu : P u) : GuardIR.NZTree P (.nonZero (.var u))
  | conj {g h : GuardIR} (hg : GuardIR.NZTree P g) (hh : GuardIR.NZTree P h) :
    GuardIR.NZTree P (.conj g h)

private theorem GuardIR.NZTree.mentions {P : VarId → Prop} {g : GuardIR}
    (h : GuardIR.NZTree P g) {v : VarId} (hv : guardMentionsVar v g = true) : P v := by
  induction h with
  | @var u hu => exact (of_decide_eq_true hv : u = v) ▸ hu
  | @conj g h _ _ ihg ihh =>
    rcases Bool.or_eq_true_iff.mp (hv : (guardMentionsVar v g || guardMentionsVar v h) = true)
      with hv' | hv'
    · exact ihg hv'
    · exact ihh hv'

private theorem GuardIR.NZTree.pullbackAll_frame {P : VarId → Prop} {s : Stmt} {g : GuardIR}
    (hs : ∀ v, P v → stmtWritesVar v s = false) (h : GuardIR.NZTree P g) :
    Stmt.pullbackAll s g = g :=
  Stmt.pullbackAll_of_not_writes (fun _ hv => hs _ (h.mentions hv))

private theorem GuardIR.NZTree.havoc {P : VarId → Prop} {g : GuardIR}
    (h : GuardIR.NZTree P g) {v : VarId} (hv : ¬ P v) : havocGuardIR v g = g := by
  apply havocGuardIR_of_not_mentions
  cases hm : guardMentionsVar v g with
  | false => rfl
  | true => exact absurd (h.mentions hm) hv

private theorem GuardIR.saturate_of_top {accVar : VarId} {latch : Stmt} {g : GuardIR} (k : Nat)
    (h : GuardIR.backStep accVar latch g = .top) :
    GuardIR.saturate accVar latch (k + 1) g = some g := by
  rw [GuardIR.saturate, h]

private theorem GuardIR.saturate_of_nonZero {accVar : VarId} {latch : Stmt} {g : GuardIR}
    (k : Nat) {e : PureExpr} (h : GuardIR.backStep accVar latch g = .nonZero e) :
    GuardIR.saturate accVar latch (k + 1) g =
      GuardIR.saturate accVar latch k (.conj g (.nonZero e)) := by
  rw [GuardIR.saturate, h]

private theorem GuardIR.saturate_of_conj {accVar : VarId} {latch : Stmt} {g : GuardIR}
    (k : Nat) {a b : GuardIR} (h : GuardIR.backStep accVar latch g = .conj a b) :
    GuardIR.saturate accVar latch (k + 1) g =
      GuardIR.saturate accVar latch k (.conj g (.conj a b)) := by
  rw [GuardIR.saturate, h]

/-- Two-stage pipeline `d := nextD; i := stepRhs`: the invariant is `d ≠ 0 ∧ nextD ≠ 0`, or
    in any case a guard over these two variables. -/
private theorem strengthenLoopInvariantIR_pipeline_pos (accVar d nextD i : VarId)
    (hda : d ≠ accVar) (hna : nextD ≠ accVar)
    (hdi : d ≠ i) (hni : nextD ≠ i) (hdn : d ≠ nextD) (stepRhs : PureExpr) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq (.assign d (.var nextD)) (.assign i stepRhs))
        (.nonZero (.var d)) = some inv ∧
      GuardIR.Pos (fun u => u = d ∨ u = nextD) inv := by
  have hb1 : GuardIR.backStep accVar (.seq (.assign d (.var nextD)) (.assign i stepRhs))
      (.nonZero (.var d)) = .nonZero (.var nextD) := by
    have hpb : Stmt.pullbackAll (.seq (.assign d (.var nextD)) (.assign i stepRhs))
        (.nonZero (.var d)) = .nonZero (.var nextD) := by
      simp [Stmt.pullbackAll, GuardIR.subst, PureExpr.subst, hdi]
    unfold GuardIR.backStep
    rw [hpb, havocGuardIR_of_not_mentions (v := accVar) (g := .nonZero (.var nextD))
      (decide_eq_false hna)]
    simp [GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero, GuardIR.nf,
      GuardIR.residual, GuardIR.hasHyp, hdn]
  have hb2 : GuardIR.backStep accVar (.seq (.assign d (.var nextD)) (.assign i stepRhs))
      (.conj (.nonZero (.var d)) (.nonZero (.var nextD))) = .top := by
    have hpb : Stmt.pullbackAll (.seq (.assign d (.var nextD)) (.assign i stepRhs))
        (.conj (.nonZero (.var d)) (.nonZero (.var nextD))) =
        .conj (.nonZero (.var nextD)) (.nonZero (.var nextD)) := by
      simp [Stmt.pullbackAll, GuardIR.subst, PureExpr.subst, hdi, hni, Ne.symm hdn]
    have hm : guardMentionsVar accVar
        (.conj (.nonZero (.var nextD)) (.nonZero (.var nextD))) = false := by
      simp [guardMentionsVar, pureMentionsVar, hna]
    unfold GuardIR.backStep
    rw [hpb, havocGuardIR_of_not_mentions hm]
    simp [GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero,
      GuardIR.mkConj, GuardIR.nf, GuardIR.residual, GuardIR.hasHyp]
  refine strengthenLoopInvariantIR_pos (.var (Or.inl rfl)) ?_ ?_
    ⟨_, ?_, .conj (.var (Or.inl rfl)) (.var (Or.inr rfl))⟩
  · exact (GuardIR.Pos.subst_frame (.var (Or.inl rfl))
      (fun u hu => by rcases hu with rfl | rfl; exact hdi; exact hni) stepRhs).subst_closed d
        (Or.inr rfl)
  · rintro (h | h)
    · exact hda h.symm
    · exact hna h.symm
  · exact (GuardIR.saturate_of_nonZero 7 hb1).trans (GuardIR.saturate_of_top 6 hb2)

/-- Swap latch `preLatch; tmp := d; d := altD; altD := tmp; postLatch`: the invariant is
    `d ≠ 0 ∧ altD ≠ 0`, or in any case a guard over these two variables. -/
private theorem strengthenLoopInvariantIR_swap_pos (accVar d altD tmp : VarId)
    (preLatch postLatch : Stmt)
    (hda : d ≠ accVar) (hala : altD ≠ accVar)
    (hdal : d ≠ altD) (hdt : d ≠ tmp) (halt : altD ≠ tmp)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreAlt : stmtWritesVar altD preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostAlt : stmtWritesVar altD postLatch = false) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq preLatch
          (.seq (.assign tmp (.var d))
            (.seq (.assign d (.var altD))
              (.seq (.assign altD (.var tmp)) postLatch))))
        (.nonZero (.var d)) = some inv ∧
      GuardIR.Pos (fun u => u = d ∨ u = altD) inv := by
  have hPre : ∀ v, (fun u => u = d ∨ u = altD) v → stmtWritesVar v preLatch = false := by
    rintro v (rfl | rfl) <;> assumption
  have hPost : ∀ v, (fun u => u = d ∨ u = altD) v → stmtWritesVar v postLatch = false := by
    rintro v (rfl | rfl) <;> assumption
  have hacc : ¬ (fun u => u = d ∨ u = altD) accVar := by
    rintro (h | h)
    · exact hda h.symm
    · exact hala h.symm
  have hhav : ∀ {g : GuardIR}, GuardIR.NZTree (fun u => u = d ∨ u = altD) g →
      havocGuardIR accVar g = g := fun h => h.havoc hacc
  have hpb : ∀ g : GuardIR,
      Stmt.pullbackAll
        (.seq preLatch
          (.seq (.assign tmp (.var d))
            (.seq (.assign d (.var altD))
              (.seq (.assign altD (.var tmp)) postLatch)))) g =
      Stmt.pullbackAll preLatch
        (GuardIR.subst tmp (.var d)
          (GuardIR.subst d (.var altD)
            (GuardIR.subst altD (.var tmp) (Stmt.pullbackAll postLatch g)))) := fun _ => rfl
  have hb1 : GuardIR.backStep accVar
      (.seq preLatch
        (.seq (.assign tmp (.var d))
          (.seq (.assign d (.var altD))
            (.seq (.assign altD (.var tmp)) postLatch))))
      (.nonZero (.var d)) = .nonZero (.var altD) := by
    unfold GuardIR.backStep
    rw [hpb, GuardIR.NZTree.pullbackAll_frame hPost (.var (Or.inl rfl))]
    simp only [GuardIR.subst, PureExpr.subst, hdal, halt, ↓reduceIte]
    rw [GuardIR.NZTree.pullbackAll_frame hPre (.var (Or.inr rfl)),
      hhav (.var (Or.inr rfl))]
    simp [GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero, GuardIR.nf,
      GuardIR.residual, GuardIR.hasHyp, hdal]
  have hb2 : GuardIR.backStep accVar
      (.seq preLatch
        (.seq (.assign tmp (.var d))
          (.seq (.assign d (.var altD))
            (.seq (.assign altD (.var tmp)) postLatch))))
      (.conj (.nonZero (.var d)) (.nonZero (.var altD))) = .top := by
    unfold GuardIR.backStep
    rw [hpb, GuardIR.NZTree.pullbackAll_frame hPost (.conj (.var (Or.inl rfl)) (.var (Or.inr rfl)))]
    simp only [GuardIR.subst, PureExpr.subst, hdal, halt, Ne.symm hdt, ↓reduceIte]
    rw [GuardIR.NZTree.pullbackAll_frame hPre (.conj (.var (Or.inr rfl)) (.var (Or.inl rfl))),
      hhav (.conj (.var (Or.inr rfl)) (.var (Or.inl rfl)))]
    simp [GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero,
      GuardIR.mkConj, GuardIR.nf, GuardIR.residual, GuardIR.hasHyp]
  refine strengthenLoopInvariantIR_pos (.var (Or.inl rfl)) ?_ hacc
    ⟨_, (GuardIR.saturate_of_nonZero 7 hb1).trans (GuardIR.saturate_of_top 6 hb2),
      .conj (.var (Or.inl rfl)) (.var (Or.inr rfl))⟩
  refine GuardIR.Pos.pullback_frame hPre ?_
  refine ((((GuardIR.Pos.pullback_frame hPost (.var (Or.inl rfl))).subst_var altD tmp).subst_var
    d altD).subst_var tmp d).mono ?_
  rintro u (hu | ⟨hu | ⟨hu | ⟨hu | hu, hne₁⟩, hne₂⟩, hne₃⟩)
  · exact Or.inl hu
  · exact Or.inr hu
  · exact absurd hu hne₃
  · exact absurd hu hne₂
  · exact absurd hu hne₁

/-- Three-stage pipeline `preLatch; d := d₁; d₁ := d₂; postLatch`: two backward steps reach
    `d ≠ 0 ∧ d₁ ≠ 0 ∧ d₂ ≠ 0`; in any case the invariant is a guard over these variables. -/
private theorem strengthenLoopInvariantIR_pipeline3_pos (accVar d d₁ d₂ : VarId)
    (preLatch postLatch : Stmt)
    (hda : d ≠ accVar) (hd₁a : d₁ ≠ accVar) (hd₂a : d₂ ≠ accVar)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : stmtWritesVar d₂ postLatch = false) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq preLatch
          (.seq (.assign d (.var d₁))
            (.seq (.assign d₁ (.var d₂)) postLatch)))
        (.nonZero (.var d)) = some inv ∧
      GuardIR.Pos (fun u => u = d ∨ u = d₁ ∨ u = d₂) inv := by
  have hPre : ∀ v, (fun u => u = d ∨ u = d₁ ∨ u = d₂) v →
      stmtWritesVar v preLatch = false := by
    rintro v (rfl | rfl | rfl) <;> assumption
  have hPost : ∀ v, (fun u => u = d ∨ u = d₁ ∨ u = d₂) v →
      stmtWritesVar v postLatch = false := by
    rintro v (rfl | rfl | rfl) <;> assumption
  have hacc : ¬ (fun u => u = d ∨ u = d₁ ∨ u = d₂) accVar := by
    rintro (h | h | h)
    · exact hda h.symm
    · exact hd₁a h.symm
    · exact hd₂a h.symm
  have hhav : ∀ {g : GuardIR}, GuardIR.NZTree (fun u => u = d ∨ u = d₁ ∨ u = d₂) g →
      havocGuardIR accVar g = g := fun h => h.havoc hacc
  have hpb : ∀ g : GuardIR,
      Stmt.pullbackAll
        (.seq preLatch
          (.seq (.assign d (.var d₁))
            (.seq (.assign d₁ (.var d₂)) postLatch))) g =
      Stmt.pullbackAll preLatch
        (GuardIR.subst d (.var d₁)
          (GuardIR.subst d₁ (.var d₂) (Stmt.pullbackAll postLatch g))) := fun _ => rfl
  have hb1 : GuardIR.backStep accVar
      (.seq preLatch
        (.seq (.assign d (.var d₁))
          (.seq (.assign d₁ (.var d₂)) postLatch)))
      (.nonZero (.var d)) = .nonZero (.var d₁) := by
    unfold GuardIR.backStep
    rw [hpb, GuardIR.NZTree.pullbackAll_frame hPost (.var (Or.inl rfl))]
    simp only [GuardIR.subst, PureExpr.subst, hdd₁, ↓reduceIte]
    rw [GuardIR.NZTree.pullbackAll_frame hPre (.var (Or.inr (Or.inl rfl))),
      hhav (.var (Or.inr (Or.inl rfl)))]
    simp [GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero, GuardIR.nf,
      GuardIR.residual, GuardIR.hasHyp, hdd₁]
  have hb2 : GuardIR.backStep accVar
      (.seq preLatch
        (.seq (.assign d (.var d₁))
          (.seq (.assign d₁ (.var d₂)) postLatch)))
      (.conj (.nonZero (.var d)) (.nonZero (.var d₁))) = .nonZero (.var d₂) := by
    unfold GuardIR.backStep
    rw [hpb, GuardIR.NZTree.pullbackAll_frame hPost
      (.conj (.var (Or.inl rfl)) (.var (Or.inr (Or.inl rfl))))]
    simp only [GuardIR.subst, PureExpr.subst, hdd₁, Ne.symm hdd₂, ↓reduceIte]
    rw [GuardIR.NZTree.pullbackAll_frame hPre
        (.conj (.var (Or.inr (Or.inl rfl))) (.var (Or.inr (Or.inr rfl)))),
      hhav
        (.conj (.var (Or.inr (Or.inl rfl))) (.var (Or.inr (Or.inr rfl))))]
    simp [GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero,
      GuardIR.mkConj, GuardIR.nf, GuardIR.residual, GuardIR.hasHyp, hdd₂, hd₁d₂]
  have hb3 : GuardIR.backStep accVar
      (.seq preLatch
        (.seq (.assign d (.var d₁))
          (.seq (.assign d₁ (.var d₂)) postLatch)))
      (.conj (.conj (.nonZero (.var d)) (.nonZero (.var d₁))) (.nonZero (.var d₂))) = .top := by
    unfold GuardIR.backStep
    rw [hpb, GuardIR.NZTree.pullbackAll_frame hPost
      (.conj (.conj (.var (Or.inl rfl)) (.var (Or.inr (Or.inl rfl))))
        (.var (Or.inr (Or.inr rfl))))]
    simp only [GuardIR.subst, PureExpr.subst, hdd₁, Ne.symm hdd₂, Ne.symm hd₁d₂, ↓reduceIte]
    rw [GuardIR.NZTree.pullbackAll_frame hPre
        (.conj (.conj (.var (Or.inr (Or.inl rfl))) (.var (Or.inr (Or.inr rfl))))
          (.var (Or.inr (Or.inr rfl)))),
      hhav
        (.conj (.conj (.var (Or.inr (Or.inl rfl))) (.var (Or.inr (Or.inr rfl))))
          (.var (Or.inr (Or.inr rfl))))]
    simp [GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero,
      GuardIR.mkConj, GuardIR.nf, GuardIR.residual, GuardIR.hasHyp]
  refine strengthenLoopInvariantIR_pos (.var (Or.inl rfl)) ?_ hacc
    ⟨_, ((GuardIR.saturate_of_nonZero 7 hb1).trans (GuardIR.saturate_of_nonZero 6 hb2)).trans
        (GuardIR.saturate_of_top 5 hb3),
      .conj (.conj (.var (Or.inl rfl)) (.var (Or.inr (Or.inl rfl))))
        (.var (Or.inr (Or.inr rfl)))⟩
  exact GuardIR.Pos.pullback_frame hPre
    (((GuardIR.Pos.pullback_frame hPost (.var (Or.inl rfl))).subst_closed d₁
      (Or.inr (Or.inr rfl))).subst_closed d (Or.inr (Or.inl rfl)))

/-- Branching latch `preLatch; if branchCond { d := d₁ } else { d := d₂ }; postLatch`, for
    an arbitrary branch condition: the path-insensitive join reaches
    `d ≠ 0 ∧ d₁ ≠ 0 ∧ d₂ ≠ 0`; in any case the invariant is a guard over these variables. -/
private theorem strengthenLoopInvariantIR_ite_branch_pos (accVar d d₁ d₂ : VarId)
    (branchCond : GuardIR) (preLatch postLatch : Stmt)
    (hda : d ≠ accVar) (hd₁a : d₁ ≠ accVar) (hd₂a : d₂ ≠ accVar)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : stmtWritesVar d₂ postLatch = false) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq preLatch
          (.seq (.ite branchCond (.assign d (.var d₁)) (.assign d (.var d₂))) postLatch))
        (.nonZero (.var d)) = some inv ∧
      GuardIR.Pos (fun u => u = d ∨ u = d₁ ∨ u = d₂) inv := by
  have hPre : ∀ v, (fun u => u = d ∨ u = d₁ ∨ u = d₂) v →
      stmtWritesVar v preLatch = false := by
    rintro v (rfl | rfl | rfl) <;> assumption
  have hPost : ∀ v, (fun u => u = d ∨ u = d₁ ∨ u = d₂) v →
      stmtWritesVar v postLatch = false := by
    rintro v (rfl | rfl | rfl) <;> assumption
  have hacc : ¬ (fun u => u = d ∨ u = d₁ ∨ u = d₂) accVar := by
    rintro (h | h | h)
    · exact hda h.symm
    · exact hd₁a h.symm
    · exact hd₂a h.symm
  have hhav : ∀ {g : GuardIR}, GuardIR.NZTree (fun u => u = d ∨ u = d₁ ∨ u = d₂) g →
      havocGuardIR accVar g = g := fun h => h.havoc hacc
  have hpb : ∀ g : GuardIR,
      Stmt.pullbackAll
        (.seq preLatch
          (.seq (.ite branchCond (.assign d (.var d₁)) (.assign d (.var d₂))) postLatch)) g =
      Stmt.pullbackAll preLatch
        (GuardIR.join (GuardIR.subst d (.var d₁) (Stmt.pullbackAll postLatch g))
          (GuardIR.subst d (.var d₂) (Stmt.pullbackAll postLatch g))) := fun _ => rfl
  have hb1 : GuardIR.backStep accVar
      (.seq preLatch
        (.seq (.ite branchCond (.assign d (.var d₁)) (.assign d (.var d₂))) postLatch))
      (.nonZero (.var d)) = .conj (.nonZero (.var d₁)) (.nonZero (.var d₂)) := by
    unfold GuardIR.backStep
    rw [hpb, GuardIR.NZTree.pullbackAll_frame hPost (.var (Or.inl rfl))]
    have hj : GuardIR.join (GuardIR.subst d (.var d₁) (.nonZero (.var d)))
        (GuardIR.subst d (.var d₂) (.nonZero (.var d))) =
        .conj (.nonZero (.var d₁)) (.nonZero (.var d₂)) := by
      simp [GuardIR.join, GuardIR.size, GuardIR.subst, PureExpr.subst, GuardIR.mkConj,
        GuardIR.residual, GuardIR.hasHyp, hd₁d₂]
    rw [hj, GuardIR.NZTree.pullbackAll_frame hPre
        (.conj (.var (Or.inr (Or.inl rfl))) (.var (Or.inr (Or.inr rfl)))),
      hhav
        (.conj (.var (Or.inr (Or.inl rfl))) (.var (Or.inr (Or.inr rfl))))]
    simp [GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero,
      GuardIR.mkConj, GuardIR.nf, GuardIR.residual, GuardIR.hasHyp, hdd₁, hdd₂, hd₁d₂]
  have hb2 : GuardIR.backStep accVar
      (.seq preLatch
        (.seq (.ite branchCond (.assign d (.var d₁)) (.assign d (.var d₂))) postLatch))
      (.conj (.nonZero (.var d)) (.conj (.nonZero (.var d₁)) (.nonZero (.var d₂)))) = .top := by
    unfold GuardIR.backStep
    rw [hpb, GuardIR.NZTree.pullbackAll_frame hPost
      (.conj (.var (Or.inl rfl)) (.conj (.var (Or.inr (Or.inl rfl)))
        (.var (Or.inr (Or.inr rfl)))))]
    have hj : GuardIR.join
        (GuardIR.subst d (.var d₁)
          (.conj (.nonZero (.var d)) (.conj (.nonZero (.var d₁)) (.nonZero (.var d₂)))))
        (GuardIR.subst d (.var d₂)
          (.conj (.nonZero (.var d)) (.conj (.nonZero (.var d₁)) (.nonZero (.var d₂))))) =
        .conj (.nonZero (.var d₁)) (.conj (.nonZero (.var d₁)) (.nonZero (.var d₂))) := by
      simp [GuardIR.join, GuardIR.size, GuardIR.subst, PureExpr.subst, GuardIR.mkConj,
        GuardIR.residual, GuardIR.hasHyp, hd₁d₂, Ne.symm hdd₁, Ne.symm hdd₂]
    rw [hj, GuardIR.NZTree.pullbackAll_frame hPre
        (.conj (.var (Or.inr (Or.inl rfl))) (.conj (.var (Or.inr (Or.inl rfl)))
          (.var (Or.inr (Or.inr rfl))))),
      hhav
        (.conj (.var (Or.inr (Or.inl rfl))) (.conj (.var (Or.inr (Or.inl rfl)))
          (.var (Or.inr (Or.inr rfl)))))]
    simp [GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero,
      GuardIR.mkConj, GuardIR.nf, GuardIR.residual, GuardIR.hasHyp]
  refine strengthenLoopInvariantIR_pos (.var (Or.inl rfl)) ?_ hacc
    ⟨_, (GuardIR.saturate_of_conj 7 hb1).trans (GuardIR.saturate_of_top 6 hb2),
      .conj (.var (Or.inl rfl)) (.conj (.var (Or.inr (Or.inl rfl)))
        (.var (Or.inr (Or.inr rfl))))⟩
  exact GuardIR.Pos.pullback_frame hPre
    (GuardIR.Pos.branch branchCond
      ((GuardIR.Pos.pullback_frame hPost (.var (Or.inl rfl))).subst_closed d
        (Or.inr (Or.inl rfl)))
      ((GuardIR.Pos.pullback_frame hPost (.var (Or.inl rfl))).subst_closed d
        (Or.inr (Or.inr rfl))))

/-! ### Milestone 3 target theorems: strengthening completeness and preheader hoisting -/

/-- Stationary Divisor Strengthening Completeness: When `d` is distinct from `accVar` and `i`,
    `strengthenLoopInvariantIR` succeeds on `i := i - 1` for `.nonZero (.var d)`. -/
theorem strengthenLoopInvariantIR_stationary (accVar d i : VarId)
    (hda : d ≠ accVar) (hdi : d ≠ i) :
    ∃ inv, strengthenLoopInvariantIR accVar (.assign i (.sub (.var i) (.lit 1))) (.nonZero (.var d)) = some inv := by
  exact ⟨_, strengthenLoopInvariantIR_frame hda (decide_eq_false (Ne.symm hdi))⟩

/-- Two-Stage Pipeline Divisor Strengthening Completeness: Across `d := nextD; i := i - 1`,
    `strengthenLoopInvariantIR` strengthens `.nonZero (.var d)` to a genuine inductive invariant `some inv`. -/
theorem strengthenLoopInvariantIR_pipeline (accVar d nextD i : VarId)
    (hda : d ≠ accVar) (hna : nextD ≠ accVar)
    (hdi : d ≠ i) (hni : nextD ≠ i) (hdn : d ≠ nextD) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq (.assign d (.var nextD)) (.assign i (.sub (.var i) (.lit 1))))
        (.nonZero (.var d)) = some inv := by
  obtain ⟨inv, h, _⟩ := strengthenLoopInvariantIR_pipeline_pos accVar d nextD i hda hna hdi hni hdn
    (.sub (.var i) (.lit 1))
  exact ⟨inv, h⟩

/-- Categorical Realization of `hoistLoopGuardIR`: Denotation commutes with abstract `hoistLoopGuard`
    along `stateTransfer (execStmt init)`. -/
theorem hoistLoopGuardIR_denote (init : Stmt) (ctx inv : GuardIR) :
    denoteGuard (hoistLoopGuardIR init ctx inv) =
      hoistLoopGuard (stateTransfer (execStmt init)) (denoteGuard ctx) (denoteGuard inv) := by
  exact synthesizeStmtGuardIR_denote init ctx inv

/-- Arbitrary-Iteration Target Soundness of `hoistLoopGuardIR`: Given an inductive invariant `inv`
    for `target` under `loopStepTransfer accVar latch`, conjoining `ctx` with `hoistLoopGuardIR init ctx inv`
    establishes `target` after `init` and `n` abstract loop iterations for every `n : ℕ`. -/
theorem hoistLoopGuardIR_iterate_target (init : Stmt) (accVar : VarId) (latch : Stmt)
    (ctx target inv : GuardIR)
    (hInd : IsInductiveFor (loopStepTransfer accVar latch) (denoteGuard inv) (denoteGuard target))
    (n : ℕ) :
    (((stateTransfer (execStmt init)).comp ((loopStepTransfer accVar latch).iterate n)).post
      (denoteGuard ctx ⊓ denoteGuard (hoistLoopGuardIR init ctx inv))) ≤ denoteGuard target := by
  rw [hoistLoopGuardIR_denote]
  exact hoistLoopGuard_iterate_target (stateTransfer (execStmt init))
    (loopStepTransfer accVar latch) (denoteGuard ctx) (denoteGuard inv) (denoteGuard target)
    hInd n

/-! ### Soundness of the loop optimizer -/

private theorem WhileLoop.withFacts_cond (F : GuardIR) (w : WhileLoop) :
    (w.withFacts F).cond = w.cond := rfl

private theorem WhileLoop.withFacts_accVar (F : GuardIR) (w : WhileLoop) :
    (w.withFacts F).accVar = w.accVar := rfl

private theorem WhileLoop.withFacts_latch (F : GuardIR) (w : WhileLoop) :
    (w.withFacts F).latch = w.latch := rfl

/-- `optimizeBlock` on a block without statements is `optimizeExpr` under the entailed facts;
    it preserves the value of the expression wherever the context holds. -/
private theorem evalExpr_optimizeBlock_skip {ctx : GuardIR} {e : Expr} {env : Env}
    (h : evalGuard env ctx = true) :
    evalExpr env (optimizeBlock ctx { body := .skip, ret := e }).ret = evalExpr env e :=
  optimizeBlock_sound ctx { body := .skip, ret := e } env h

/-- If an invariant that implies the facts `F` holds at the loop header and is preserved by
    every iteration, the loop rewritten under `F` runs exactly like the original. -/
private theorem WhileLoop.runWhileSteps_withFacts {w : WhileLoop} {F inv : GuardIR}
    (hF : ∀ env, evalGuard env inv = true → evalGuard env F = true)
    (hstep : ∀ env val, evalGuard env inv = true →
      evalGuard (execStmt w.latch (updateEnv env w.accVar val)) inv = true) :
    ∀ (fuel : Nat) (env : Env), evalGuard env inv = true →
      runWhileSteps fuel env (w.withFacts F) = runWhileSteps fuel env w := by
  intro fuel
  induction fuel with
  | zero => intro env _; rfl
  | succ fuel ih =>
    intro env hinv
    have hFenv := hF env hinv
    cases hc : evalGuard env w.cond with
    | true =>
      have hb : evalExpr env (w.withFacts F).body = evalExpr env w.body :=
        evalExpr_optimizeBlock_skip (GuardIR.evalGuard_conj_intro hFenv hc)
      simp only [runWhileSteps, WhileLoop.withFacts_cond, WhileLoop.withFacts_accVar,
        WhileLoop.withFacts_latch, hc, hb, ↓reduceIte]
      cases evalExpr env w.body with
      | val val => exact ih _ (hstep env val hinv)
      | trap => rfl
      | ub => rfl
    | false =>
      have hr : evalExpr env (w.withFacts F).ret = evalExpr env w.ret :=
        evalExpr_optimizeBlock_skip
          (GuardIR.evalGuard_conj_intro hFenv (evalGuard_imp_bot_of_eq_false hc))
      simp only [runWhileSteps, WhileLoop.withFacts_cond, hc, hr, Bool.false_eq_true,
        ↓reduceIte]

/-- The facts selected from the strengthened candidates are implied by the conjunction of
    their invariants, which every loop iteration preserves. -/
private theorem selectFacts_sound (accept : GuardIR → Bool) (accVar : VarId) (latch : Stmt) :
    ∀ cands : List GuardIR,
      (∀ env, evalGuard env (selectFacts accept (loopInvariants accVar latch cands)).2 = true →
        evalGuard env (selectFacts accept (loopInvariants accVar latch cands)).1 = true) ∧
      ∀ env val, evalGuard env (selectFacts accept (loopInvariants accVar latch cands)).2 = true →
        evalGuard (execStmt latch (updateEnv env accVar val))
          (selectFacts accept (loopInvariants accVar latch cands)).2 = true := by
  intro cands
  induction cands with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  | cons c cs ih =>
    rw [loopInvariants]
    split
    · next inv hs =>
      split
      · exact ih
      · rw [selectFacts]
        split
        · have hsound := strengthenLoopInvariantIR_sound hs
          refine ⟨fun env h => ?_, fun env val h => ?_⟩
          · rw [GuardIR.evalGuard_mkConj, Bool.and_eq_true] at h ⊢
            exact ⟨hsound.1 env h.1, ih.1 env h.2⟩
          · rw [GuardIR.evalGuard_mkConj, Bool.and_eq_true] at h ⊢
            exact ⟨hsound.2 env val h.1, ih.2 env val h.2⟩
        · exact ih
    · exact ih

/-- If every accepted invariant holds in a state, so does their conjunction. -/
private theorem selectFacts_accept {accept : GuardIR → Bool} {env : Env}
    (hacc : ∀ inv, accept inv = true → evalGuard env inv = true) :
    ∀ invs : List (GuardIR × GuardIR), evalGuard env (selectFacts accept invs).2 = true := by
  intro invs
  induction invs with
  | nil => rfl
  | cons p ps ih =>
    rw [selectFacts]
    split
    · next ha =>
      rw [GuardIR.evalGuard_mkConj, hacc p.2 ha, ih]
      rfl
    · exact ih

/-- A trivial hoisted guard means the entry context establishes the invariant across `init`. -/
private theorem hoistLoopGuardIR_top_sound {init : Stmt} {ctx inv : GuardIR} {env : Env}
    (h : hoistLoopGuardIR init ctx inv = .top) (hctx : evalGuard env ctx = true) :
    evalGuard (execStmt init env) inv = true :=
  GuardIR.entailsAfter_sound (s := init) (a := ctx) (b := inv)
    (by rw [GuardIR.entailsAfter_eq]; exact GuardIR.isTop_iff.mpr h) hctx

private theorem WhileLoop.evalLoop_withFacts {w : WhileLoop} {F inv : GuardIR}
    (hF : ∀ env, evalGuard env inv = true → evalGuard env F = true)
    (hstep : ∀ env val, evalGuard env inv = true →
      evalGuard (execStmt w.latch (updateEnv env w.accVar val)) inv = true)
    (fuel : Nat) (env : Env) (hinit : evalGuard (execStmt w.init env) inv = true) :
    evalLoop fuel env (.whileLoop (w.withFacts F)) = evalLoop fuel env (.whileLoop w) :=
  WhileLoop.runWhileSteps_withFacts hF hstep fuel _ hinit

/-- Loop versioning preserves the outcome from every entry state satisfying the context. -/
private theorem WhileLoop.evalLoop_version (ctx : GuardIR) (w : WhileLoop) (fuel : Nat)
    (env : Env) (hctx : evalGuard env ctx = true) :
    evalLoop fuel env (WhileLoop.version ctx w) = evalLoop fuel env (.whileLoop w) := by
  unfold WhileLoop.version WhileLoop.staticVersion
  simp only []
  generalize dedupGuards (Expr.factCandidates w.body ++ Expr.factCandidates w.ret) = cands
  have hdyn := selectFacts_sound (fun _ => true) w.accVar w.latch cands
  have hsta := selectFacts_sound (fun inv => GuardIR.isTop (hoistLoopGuardIR w.init ctx inv))
    w.accVar w.latch cands
  have hsta0 : evalGuard (execStmt w.init env)
      (selectFacts (fun inv => GuardIR.isTop (hoistLoopGuardIR w.init ctx inv))
        (loopInvariants w.accVar w.latch cands)).2 = true :=
    selectFacts_accept (fun inv ha => hoistLoopGuardIR_top_sound (GuardIR.isTop_iff.mp ha) hctx)
      _
  have hpre : evalGuard env (GuardIR.simplifyUnder (GuardIR.norm ctx)
      (GuardIR.norm (pullbackGuardIR w.init
        (selectFacts (fun _ => true) (loopInvariants w.accVar w.latch cands)).2))) = true →
      evalGuard (execStmt w.init env)
        (selectFacts (fun _ => true) (loopInvariants w.accVar w.latch cands)).2 = true := by
    intro h
    have hn : evalGuard env (GuardIR.norm ctx) = true := by
      rw [GuardIR.evalGuard_norm]; exact hctx
    rw [evalGuard_simplifyUnder hn, GuardIR.evalGuard_norm, evalGuard_pullbackGuardIR] at h
    exact h
  split
  · next htop =>
    exact WhileLoop.evalLoop_withFacts hdyn.1 hdyn.2 fuel env (hpre (by rw [htop]; rfl))
  · split
    · exact WhileLoop.evalLoop_withFacts hsta.1 hsta.2 fuel env hsta0
    · split
      · exact WhileLoop.evalLoop_withFacts hsta.1 hsta.2 fuel env hsta0
      · show (if evalGuard env _ then evalLoop fuel env _ else evalLoop fuel env _) = _
        split
        · next h => exact WhileLoop.evalLoop_withFacts hdyn.1 hdyn.2 fuel env (hpre h)
        · exact WhileLoop.evalLoop_withFacts hsta.1 hsta.2 fuel env hsta0

private theorem optimizeLoop_sound_aux (fuel : Nat) (prog : LoopProg) :
    ∀ (ctx : GuardIR) (env : Env), evalGuard env ctx = true →
      evalLoop fuel env (optimizeLoop ctx prog) = evalLoop fuel env prog := by
  induction prog with
  | whileLoop w =>
    intro ctx env hctx
    exact WhileLoop.evalLoop_version ctx w fuel env hctx
  | iteLoop g t e iht ihe =>
    intro ctx env hctx
    rw [optimizeLoop]
    split
    · next hg =>
      have hgt : evalGuard env g = true := GuardIR.entailsAfter_sound (s := .skip) hg hctx
      rw [iht ctx env hctx]
      simp only [evalLoop, hgt, ↓reduceIte]
    · split
      · next hng =>
        have hgf : evalGuard env g = false :=
          evalGuard_eq_false_of_imp_bot (GuardIR.entailsAfter_sound (s := .skip) hng hctx)
        rw [ihe ctx env hctx]
        simp only [evalLoop, hgf, Bool.false_eq_true, ↓reduceIte]
      · simp only [evalLoop]
        cases hg : evalGuard env g with
        | true =>
          simp only [↓reduceIte]
          exact iht _ env (GuardIR.evalGuard_conj_intro hctx hg)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ihe _ env
            (GuardIR.evalGuard_conj_intro hctx (evalGuard_imp_bot_of_eq_false hg))

/-- Fuel-Indexed Stage-Guarded Soundness of `optimizeLoop` via `GuardedEquiv` and `liftEval (evalLoop fuel)`. -/
theorem optimizeLoop_guardedEquiv (fuel : Nat) (ctx : GuardIR) (prog : LoopProg) :
    GuardedEquiv (liftEval (evalLoop fuel)) (denoteGuard ctx) (optimizeLoop ctx prog) prog := by
  exact (liftEval_guardedEquiv_iff (evalLoop fuel) (denoteGuard ctx) (optimizeLoop ctx prog)
    prog).mpr (fun env h => optimizeLoop_sound_aux fuel prog ctx env h)

/-- Fuel-Indexed Concrete Operational Soundness of `optimizeLoop`: For every `fuel` and `env`
    satisfying `ctx`, `optimizeLoop ctx prog` evaluates to the exact same `LoopOutcome` as `prog`. -/
theorem optimizeLoop_sound (fuel : Nat) (ctx : GuardIR) (prog : LoopProg) (env : Env) :
    evalGuard env ctx = true → evalLoop fuel env (optimizeLoop ctx prog) = evalLoop fuel env prog := by
  exact optimizeLoop_sound_aux fuel prog ctx env

/-! ### Symbolic evaluation of the loop optimizer on the parametric shapes -/

private theorem updateEnv_same (env : Env) (v : VarId) (val : Int) :
    updateEnv env v val v = val := by
  simp only [updateEnv, decide_true, ↓reduceIte]

private theorem updateEnv_of_ne (env : Env) {v w : VarId} (h : w ≠ v) (val : Int) :
    updateEnv env v val w = env w := by
  simp only [updateEnv, h, decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem Int.ofNat_succ_ne_zero (k : Nat) : Int.ofNat (k + 1) ≠ 0 := by
  simp only [Int.ofNat_eq_natCast]
  omega

private theorem Int.ofNat_succ_sub_one (k : Nat) : Int.ofNat (k + 1) - 1 = Int.ofNat k := by
  simp only [Int.ofNat_eq_natCast]
  omega

/-- The counter decrement `i := i - 1`, and its preservation by surrounding statements that
    do not write `i`. -/
private theorem execStmt_dec_assign (i : VarId) (env : Env) :
    execStmt (.assign i (.sub (.var i) (.lit 1))) env i = env i - 1 :=
  updateEnv_same env i _

private theorem execStmt_dec_seq_left {i : VarId} {A B : Stmt}
    (hA : stmtWritesVar i A = false) (hB : ∀ env, execStmt B env i = env i - 1) (env : Env) :
    execStmt (.seq A B) env i = env i - 1 := by
  show execStmt B (execStmt A env) i = env i - 1
  rw [hB, execStmt_of_not_writes hA]

private theorem execStmt_dec_seq_right {i : VarId} {A B : Stmt}
    (hA : ∀ env, execStmt A env i = env i - 1) (hB : stmtWritesVar i B = false) (env : Env) :
    execStmt (.seq A B) env i = env i - 1 := by
  show execStmt B (execStmt A env) i = env i - 1
  rw [execStmt_of_not_writes hB, hA]

/-- The counter still decrements when the loop body first writes the accumulator. -/
private theorem execStmt_dec_after_acc {i acc : VarId} {latch : Stmt} (hia : i ≠ acc)
    (h : ∀ env, execStmt latch env i = env i - 1) (env : Env) (val : Int) :
    execStmt latch (updateEnv env acc val) i = env i - 1 := by
  rw [h, updateEnv_of_ne _ hia]

/-! One loop-header visit of the fuel-indexed evaluator and of its cost observer. -/

private theorem runWhileSteps_exit {fuel : Nat} {env : Env} {w : WhileLoop}
    (hc : evalGuard env w.cond = false) :
    runWhileSteps (fuel + 1) env w = .done (evalExpr env w.ret) := by
  simp only [runWhileSteps, hc, Bool.false_eq_true, ↓reduceIte]

private theorem runWhileSteps_step {fuel : Nat} {env : Env} {w : WhileLoop} {val : Int}
    (hc : evalGuard env w.cond = true) (hb : evalExpr env w.body = .val val) :
    runWhileSteps (fuel + 1) env w =
      runWhileSteps fuel (execStmt w.latch (updateEnv env w.accVar val)) w := by
  simp only [runWhileSteps, hc, hb, ↓reduceIte]

private theorem runWhileSteps_trap {fuel : Nat} {env : Env} {w : WhileLoop}
    (hc : evalGuard env w.cond = true) (hb : evalExpr env w.body = .trap) :
    runWhileSteps (fuel + 1) env w = .done .trap := by
  simp only [runWhileSteps, hc, hb, ↓reduceIte]

private theorem runWhileCheckCost_exit {fuel : Nat} {env : Env} {w : WhileLoop}
    (hc : evalGuard env w.cond = false) :
    runWhileCheckCost (fuel + 1) env w = guardEvalCost env w.cond + execCheckCost env w.ret := by
  simp only [runWhileCheckCost, hc, Bool.false_eq_true, ↓reduceIte]

private theorem runWhileCheckCost_step {fuel : Nat} {env : Env} {w : WhileLoop} {val : Int}
    (hc : evalGuard env w.cond = true) (hb : evalExpr env w.body = .val val) :
    runWhileCheckCost (fuel + 1) env w =
      guardEvalCost env w.cond + (execCheckCost env w.body +
        (stmtGuardCost (updateEnv env w.accVar val) w.latch +
          runWhileCheckCost fuel (execStmt w.latch (updateEnv env w.accVar val)) w)) := by
  simp only [runWhileCheckCost, hc, hb, ↓reduceIte]

/-! The loop body `pa + (num / d + (y * d) / d)` before and after the rewrite. -/

private theorem evalExpr_add_dualDiv {env : Env} (pa num y : PureExpr) {d : PureExpr}
    (h : evalPure env d ≠ 0) :
    evalExpr env (.add (.pure pa) (mkDualDivExpr num y d)) =
      .val (evalPure env pa +
        (evalPure env num / evalPure env d + evalPure env y * evalPure env d / evalPure env d)) := by
  simp only [mkDualDivExpr, evalExpr, h, ↓reduceIte]

private theorem execCheckCost_add_dualDiv {env : Env} (pa num y : PureExpr) {d : PureExpr}
    (h : evalPure env d ≠ 0) :
    execCheckCost env (.add (.pure pa) (mkDualDivExpr num y d)) = 2 := by
  simp only [execCheckCost, evalExpr, execCheckCost_mkDualDivExpr num y h, Nat.zero_add]

private theorem Expr.dualDivFast_counts (pa num y pd : PureExpr) :
    checkedDivCount (Expr.mkBin .add .add (.pure pa)
        (Expr.mkBin .add .add (Expr.mkSafeDiv (.pure num) pd) (.pure y))) = 0 ∧
      divOpCount (Expr.mkBin .add .add (.pure pa)
        (Expr.mkBin .add .add (Expr.mkSafeDiv (.pure num) pd) (.pure y))) ≤ 1 ∧
      guardBranchCount (Expr.mkBin .add .add (.pure pa)
        (Expr.mkBin .add .add (Expr.mkSafeDiv (.pure num) pd) (.pure y))) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Expr.count_mkBin (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl),
      Expr.count_mkBin (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl),
      Expr.count_mkSafeDiv (cnt := checkedDivCount) (fun _ => rfl) (fun _ _ => rfl)]
    rfl
  · rw [Expr.count_mkBin (cnt := divOpCount) (fun _ => rfl) (fun _ _ => rfl),
      Expr.count_mkBin (cnt := divOpCount) (fun _ => rfl) (fun _ _ => rfl)]
    have h := Expr.divOpCount_mkSafeDiv_pure_le num pd
    have e₁ : divOpCount (Expr.pure pa) = 0 := rfl
    have e₂ : divOpCount (Expr.pure y) = 0 := rfl
    omega
  · rw [Expr.count_mkBin (cnt := guardBranchCount) (fun _ => rfl) (fun _ _ => rfl),
      Expr.count_mkBin (cnt := guardBranchCount) (fun _ => rfl) (fun _ _ => rfl),
      Expr.count_mkSafeDiv (cnt := guardBranchCount) (fun _ => rfl) (fun _ _ => rfl)]
    rfl

/-- With `nonZero d` entailed by the context, `optimizeBlock` lowers the loop body completely:
    both checks and one division disappear. -/
private theorem optimizeBlock_skip_add_dualDiv {K : GuardIR} (pa num y d : PureExpr)
    (h : GuardIR.entailsAfter .skip K (.nonZero d) = true) :
    (optimizeBlock K { body := .skip, ret := .add (.pure pa) (mkDualDivExpr num y d) }).ret =
      Expr.mkBin .add .add (.pure pa)
        (Expr.mkBin .add .add (Expr.mkSafeDiv (.pure num) d) (.pure y)) := by
  show optimizeExpr
      (GuardIR.collect (GuardIR.entailsAfter .skip K) [.nonZero d, .nonZero d])
      (.add (.pure pa) (mkDualDivExpr num y d)) = _
  simp only [optimizeExpr, Expr.postFacts]
  rw [optimizeExpr_mkDualDivExpr_of_hasHyp num y d
    (by simp only [GuardIR.nf, GuardIR.hasHyp_mkConj, GuardIR.hasHyp_collect_head _ h,
      Bool.true_or])]

private theorem WhileLoop.withFacts_body_dualDiv {w : WhileLoop} {i d : VarId}
    {pa num y : PureExpr} (hcond : w.cond = .nonZero (.var i))
    (hbody : w.body = .add (.pure pa) (mkDualDivExpr num y (.var d))) :
    (w.withFacts (.nonZero (.var d))).body =
      Expr.mkBin .add .add (.pure pa)
        (Expr.mkBin .add .add (Expr.mkSafeDiv (.pure num) (.var d)) (.pure y)) := by
  show (optimizeBlock (.conj (.nonZero (.var d)) w.cond) { body := .skip, ret := w.body }).ret = _
  rw [hcond, hbody]
  refine optimizeBlock_skip_add_dualDiv pa num y (.var d) ?_
  simp [GuardIR.entailsAfter, pullbackGuardIR, GuardIR.entails, GuardIR.simplifyUnder,
    GuardIR.norm, PureExpr.fold, GuardIR.mkNonZero, GuardIR.mkConj, GuardIR.nf,
    GuardIR.residual, GuardIR.hasHyp, GuardIR.isTop]

private theorem WhileLoop.withFacts_ret_pure (F : GuardIR) {w : WhileLoop} {pr : PureExpr}
    (hret : w.ret = .pure pr) : (w.withFacts F).ret = .pure pr := by
  show (optimizeBlock (.conj F (.imp w.cond .bot)) { body := .skip, ret := w.ret }).ret = _
  rw [hret]
  rfl

/-- Check accounting for a counted dual-division loop whose divisor is covered by an
    inductive invariant: each of the `k` iterations of the rewritten loop saves the two
    division checks, and with a branch-free latch only the `k + 1` evaluations of the loop
    condition remain. -/
private theorem WhileLoop.dualDiv_cost {w : WhileLoop} {i d : VarId} {pa num y pr : PureExpr}
    {inv : GuardIR}
    (hcond : w.cond = .nonZero (.var i))
    (hbody : w.body = .add (.pure pa) (mkDualDivExpr num y (.var d)))
    (hret : w.ret = .pure pr)
    (hd : ∀ env, evalGuard env inv = true → env d ≠ 0)
    (hstep : ∀ env val, evalGuard env inv = true →
      evalGuard (execStmt w.latch (updateEnv env w.accVar val)) inv = true)
    (hdec : ∀ env val, execStmt w.latch (updateEnv env w.accVar val) i = env i - 1) :
    ∀ (k : Nat) (env : Env), evalGuard env inv = true → env i = Int.ofNat k →
      runWhileCheckCost (k + 1) env w =
          runWhileCheckCost (k + 1) env (w.withFacts (.nonZero (.var d))) + 2 * k ∧
        ((∀ env', stmtGuardCost env' w.latch = 0) →
          runWhileCheckCost (k + 1) env (w.withFacts (.nonZero (.var d))) = k + 1) := by
  have hret' : (w.withFacts (.nonZero (.var d))).ret = .pure pr :=
    WhileLoop.withFacts_ret_pure _ hret
  have hbody' := WhileLoop.withFacts_body_dualDiv hcond hbody
  have hcost' : ∀ env, execCheckCost env (w.withFacts (.nonZero (.var d))).body = 0 := by
    intro env
    rw [hbody']
    exact execCheckCost_eq_zero (Expr.dualDivFast_counts pa num y (.var d)).1
      (Expr.dualDivFast_counts pa num y (.var d)).2.2
  intro k
  induction k with
  | zero =>
    intro env _ hi
    have hc : evalGuard env w.cond = false := by
      rw [hcond]
      exact decide_eq_false (fun h => h hi)
    have hc' : evalGuard env (w.withFacts (.nonZero (.var d))).cond = false := hc
    rw [runWhileCheckCost_exit hc, runWhileCheckCost_exit hc', hret', hret,
      WhileLoop.withFacts_cond]
    refine ⟨rfl, fun _ => ?_⟩
    rw [hcond]
    rfl
  | succ k ih =>
    intro env hinv hi
    have hne : env i ≠ 0 := by
      rw [hi]
      exact Int.ofNat_succ_ne_zero k
    have hc : evalGuard env w.cond = true := by
      rw [hcond]
      exact decide_eq_true hne
    have hc' : evalGuard env (w.withFacts (.nonZero (.var d))).cond = true := hc
    have hdne : evalPure env (.var d) ≠ 0 := hd env hinv
    have hval : evalExpr env w.body = .val (evalPure env pa +
        (evalPure env num / evalPure env (.var d) +
          evalPure env y * evalPure env (.var d) / evalPure env (.var d))) := by
      rw [hbody]
      exact evalExpr_add_dualDiv pa num y hdne
    have hval' : evalExpr env (w.withFacts (.nonZero (.var d))).body = .val (evalPure env pa +
        (evalPure env num / evalPure env (.var d) +
          evalPure env y * evalPure env (.var d) / evalPure env (.var d))) := by
      rw [← hval]
      exact evalExpr_optimizeBlock_skip
        (GuardIR.evalGuard_conj_intro (decide_eq_true hdne) hc)
    have hcost : execCheckCost env w.body = 2 := by
      rw [hbody]
      exact execCheckCost_add_dualDiv pa num y hdne
    have hi' : execStmt w.latch (updateEnv env w.accVar (evalPure env pa +
        (evalPure env num / evalPure env (.var d) +
          evalPure env y * evalPure env (.var d) / evalPure env (.var d)))) i = Int.ofNat k := by
      rw [hdec, hi]
      exact Int.ofNat_succ_sub_one k
    have ih' := ih _ (hstep env _ hinv) hi'
    rw [runWhileCheckCost_step hc hval, runWhileCheckCost_step hc' hval', hcost, hcost' env]
    simp only [WhileLoop.withFacts_cond, WhileLoop.withFacts_accVar, WhileLoop.withFacts_latch]
    refine ⟨?_, fun hl => ?_⟩
    · rw [ih'.1]
      omega
    · rw [ih'.2 hl, hl, hcond]
      show 1 + (0 + (0 + (k + 1))) = k + 1 + 1
      omega

/-- Static counts and check accounting for the rewritten loop as a whole program. -/
private theorem WhileLoop.dualDiv_fast_facts {w : WhileLoop} {i d : VarId}
    {pa num y pr : PureExpr} {inv : GuardIR}
    (hcond : w.cond = .nonZero (.var i))
    (hbody : w.body = .add (.pure pa) (mkDualDivExpr num y (.var d)))
    (hret : w.ret = .pure pr)
    (hs : strengthenLoopInvariantIR w.accVar w.latch (.nonZero (.var d)) = some inv)
    (hdec : ∀ env val, execStmt w.latch (updateEnv env w.accVar val) i = env i - 1)
    (n : Nat) (env : Env)
    (hinv : evalGuard (execStmt w.init env) inv = true)
    (hi : execStmt w.init env i = Int.ofNat n) :
    loopCheckedDivCount (.whileLoop (w.withFacts (.nonZero (.var d)))) = 0 ∧
      loopDivOpCount (.whileLoop (w.withFacts (.nonZero (.var d)))) ≤ 1 ∧
      loopBranchCount (.whileLoop (w.withFacts (.nonZero (.var d)))) = 0 ∧
      execLoopCheckCost (n + 1) env (.whileLoop w) =
        execLoopCheckCost (n + 1) env (.whileLoop (w.withFacts (.nonZero (.var d)))) + 2 * n ∧
      ((∀ env', stmtGuardCost env' w.latch = 0) → stmtGuardCost env w.init = 0 →
        execLoopCheckCost (n + 1) env (.whileLoop (w.withFacts (.nonZero (.var d)))) = n + 1) := by
  have hsound := strengthenLoopInvariantIR_sound hs
  have hcost := WhileLoop.dualDiv_cost hcond hbody hret
    (fun env h => of_decide_eq_true (hsound.1 env h)) hsound.2 hdec n (execStmt w.init env)
    hinv hi
  have hret' : (w.withFacts (.nonZero (.var d))).ret = .pure pr :=
    WhileLoop.withFacts_ret_pure _ hret
  have hbody' := WhileLoop.withFacts_body_dualDiv hcond hbody
  have hcounts := Expr.dualDivFast_counts pa num y (.var d)
  refine ⟨?_, ?_, rfl, ?_, fun hl h0 => ?_⟩
  · show checkedDivCount (w.withFacts (.nonZero (.var d))).body +
      checkedDivCount (w.withFacts (.nonZero (.var d))).ret = 0
    rw [hbody', hret', hcounts.1]
    rfl
  · show divOpCount (w.withFacts (.nonZero (.var d))).body +
      divOpCount (w.withFacts (.nonZero (.var d))).ret ≤ 1
    rw [hbody', hret']
    exact hcounts.2.1
  · show stmtGuardCost env w.init + runWhileCheckCost (n + 1) (execStmt w.init env) w =
      stmtGuardCost env w.init +
        runWhileCheckCost (n + 1) (execStmt w.init env) (w.withFacts (.nonZero (.var d))) + 2 * n
    rw [hcost.1]
    omega
  · show stmtGuardCost env w.init +
      runWhileCheckCost (n + 1) (execStmt w.init env) (w.withFacts (.nonZero (.var d))) = n + 1
    rw [hcost.2 hl, h0]
    omega

/-- The two identical candidates of the dual-division body yield one fact. -/
private theorem loopInvariants_dup {accVar : VarId} {latch : Stmt} {p : PureExpr}
    {inv : GuardIR}
    (hs : strengthenLoopInvariantIR accVar latch (.nonZero p) = some inv)
    (hnv : GuardIR.isBot (GuardIR.norm inv) = false) :
    loopInvariants accVar latch (dedupGuards [.nonZero p, .nonZero p]) = [(.nonZero p, inv)] := by
  have hd : dedupGuards [GuardIR.nonZero p, GuardIR.nonZero p] = [GuardIR.nonZero p] := by
    simp [dedupGuards]
  rw [hd]
  simp only [loopInvariants, hs, hnv, Bool.false_eq_true, ↓reduceIte]

private theorem GuardIR.isBot_norm_eq_false {g : GuardIR} {env : Env}
    (h : evalGuard env g = true) : GuardIR.isBot (GuardIR.norm g) = false := by
  cases hb : GuardIR.isBot (GuardIR.norm g) with
  | false => rfl
  | true =>
    have hn := GuardIR.evalGuard_norm env g
    rw [GuardIR.isBot_iff.mp hb, h] at hn
    exact absurd hn (by simp [evalGuard])

/-- When the entry context discharges the invariant across `init`, the loop is rewritten in
    place, without a version branch. -/
private theorem WhileLoop.version_of_discharge {ctx : GuardIR} {w : WhileLoop} {p : PureExpr}
    {inv : GuardIR}
    (hc : Expr.factCandidates w.body ++ Expr.factCandidates w.ret = [.nonZero p, .nonZero p])
    (hs : strengthenLoopInvariantIR w.accVar w.latch (.nonZero p) = some inv)
    (hnv : GuardIR.isBot (GuardIR.norm inv) = false)
    (hd : hoistLoopGuardIR w.init ctx inv = .top) :
    WhileLoop.version ctx w = .whileLoop (w.withFacts (.nonZero p)) := by
  have hpre : GuardIR.simplifyUnder (GuardIR.norm ctx)
      (GuardIR.norm (pullbackGuardIR w.init inv)) = .top :=
    GuardIR.isTop_iff.mp ((isTop_synthesizeGuardIR _ _).symm.trans (GuardIR.isTop_iff.mpr hd))
  unfold WhileLoop.version
  simp only []
  rw [hc, loopInvariants_dup hs hnv]
  simp only [selectFacts, ↓reduceIte, GuardIR.mkConj_top_right, hpre]

/-- When the residual preheader guard is a single runtime test that the context does not
    refute, the result is the fast loop, either versioned on that test or (if the second
    loop coincides with it) alone. -/
private theorem WhileLoop.version_of_hoisted {ctx : GuardIR} {w : WhileLoop} {p q : PureExpr}
    {inv : GuardIR}
    (hc : Expr.factCandidates w.body ++ Expr.factCandidates w.ret = [.nonZero p, .nonZero p])
    (hs : strengthenLoopInvariantIR w.accVar w.latch (.nonZero p) = some inv)
    (hnv : GuardIR.isBot (GuardIR.norm inv) = false)
    (hpre : GuardIR.simplifyUnder (GuardIR.norm ctx)
      (GuardIR.norm (pullbackGuardIR w.init inv)) = .nonZero q)
    (hnr : GuardIR.entails (GuardIR.norm ctx)
      (GuardIR.norm (.imp (.nonZero q) .bot)) = false) :
    WhileLoop.version ctx w = .whileLoop (w.withFacts (.nonZero p)) ∨
      ∃ slow, WhileLoop.version ctx w =
        .iteLoop (.nonZero q) (.whileLoop (w.withFacts (.nonZero p))) slow := by
  unfold WhileLoop.version
  simp only []
  rw [hc, loopInvariants_dup hs hnv]
  simp only [selectFacts, ↓reduceIte, GuardIR.mkConj_top_right, hpre, hnr, Bool.false_eq_true]
  split
  · next heq => exact Or.inl (by rw [← heq])
  · exact Or.inr ⟨_, rfl⟩

/-- Check elimination on a counted dual-division loop whose divisor invariant is discharged
    at the preheader. -/
private theorem optimizeLoop_dualDiv_elim {ctx : GuardIR} {w : WhileLoop} {i d : VarId}
    {pa num y pr : PureExpr} {inv : GuardIR}
    (hcond : w.cond = .nonZero (.var i))
    (hbody : w.body = .add (.pure pa) (mkDualDivExpr num y (.var d)))
    (hret : w.ret = .pure pr)
    (hs : strengthenLoopInvariantIR w.accVar w.latch (.nonZero (.var d)) = some inv)
    (hcov : ∃ env, evalGuard env inv = true)
    (hdis : hoistLoopGuardIR w.init ctx inv = .top)
    (hdec : ∀ env val, execStmt w.latch (updateEnv env w.accVar val) i = env i - 1)
    (n : Nat) (env : Env) (hctx : evalGuard env ctx = true)
    (hi : execStmt w.init env i = Int.ofNat n) :
    loopCheckedDivCount (optimizeLoop ctx (.whileLoop w)) = 0 ∧
      loopDivOpCount (optimizeLoop ctx (.whileLoop w)) ≤ 1 ∧
      loopBranchCount (optimizeLoop ctx (.whileLoop w)) = 0 ∧
      execLoopCheckCost (n + 1) env (.whileLoop w) =
        execLoopCheckCost (n + 1) env (optimizeLoop ctx (.whileLoop w)) + 2 * n ∧
      ((∀ env', stmtGuardCost env' w.latch = 0) → stmtGuardCost env w.init = 0 →
        execLoopCheckCost (n + 1) env (optimizeLoop ctx (.whileLoop w)) = n + 1) := by
  obtain ⟨env₀, hcov⟩ := hcov
  have hopt : optimizeLoop ctx (.whileLoop w) = .whileLoop (w.withFacts (.nonZero (.var d))) :=
    WhileLoop.version_of_discharge (by rw [hbody, hret]; rfl) hs
      (GuardIR.isBot_norm_eq_false hcov) hdis
  rw [hopt]
  exact WhileLoop.dualDiv_fast_facts hcond hbody hret hs hdec n env
    (hoistLoopGuardIR_top_sound hdis hctx) hi

/-! ### Milestone 3 target theorems: check elimination, preheader hoisting and trap preservation -/

/-- Parametric Known-Context Loop Check Elimination: Under `.nonZero (.var x)` across `n` counted
    iterations, `optimizeLoop` eliminates all checked divisions and loop-version branches and reduces
    dynamic check cost from `3 * n + 1` to `n + 1` (only the `n + 1` loop condition evaluations). -/
theorem optimizeLoop_known_ctx_elim_param (x d i acc : VarId)
    (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n) (hx : evalGuard env (.nonZero (.var x)) = true) :
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    let opt := optimizeLoop (.nonZero (.var x)) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt = n + 1 ∧
      execLoopCheckCost (n + 1) env src = 3 * n + 1 := by
  dsimp only
  obtain ⟨h1, h2, h3, h4, h5⟩ := optimizeLoop_dualDiv_elim (ctx := .nonZero (.var x))
    (w := mkCountedDivLoop x d i acc num y) (i := i) (d := d) rfl rfl rfl
    (strengthenLoopInvariantIR_frame hda (decide_eq_false hid))
    ⟨fun _ => 1, rfl⟩
    (hoistLoopGuardIR_assign1_of_pos (.var rfl) x)
    (execStmt_dec_after_acc hia (execStmt_dec_assign i))
    n env hx ((updateEnv_of_ne env hid _).trans hi)
  have hopt := h5 (fun _ => rfl) rfl
  exact ⟨h1, h2, h3, hopt, by rw [h4, hopt]; omega⟩

/-- Parametric Unknown-Context Preheader Hoisting: Under `.top` when `env x ≠ 0` across `n` counted
    iterations, `optimizeLoop` hoists the divisor check out of the loop to the preheader, reducing
    dynamic check cost from `3 * n + 1` to `≤ n + 2`. -/
theorem optimizeLoop_unknown_ctx_hoist_param (x d i acc : VarId)
    (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n) (hx : env x ≠ 0) :
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    let opt := optimizeLoop .top src
    execLoopCheckCost (n + 1) env opt ≤ n + 2 ∧
      execLoopCheckCost (n + 1) env src = 3 * n + 1 := by
  dsimp only
  have hs : strengthenLoopInvariantIR (mkCountedDivLoop x d i acc num y).accVar
      (mkCountedDivLoop x d i acc num y).latch (.nonZero (.var d)) = some (.nonZero (.var d)) :=
    strengthenLoopInvariantIR_frame hda (decide_eq_false hid)
  have hpre : GuardIR.simplifyUnder (GuardIR.norm .top)
      (GuardIR.norm (pullbackGuardIR (mkCountedDivLoop x d i acc num y).init
        (.nonZero (.var d)))) = .nonZero (.var x) := by
    simp [mkCountedDivLoop, pullbackGuardIR, GuardIR.subst, PureExpr.subst, GuardIR.norm,
      PureExpr.fold, GuardIR.mkNonZero, GuardIR.simplifyUnder, GuardIR.nf, GuardIR.residual,
      GuardIR.hasHyp]
  have hnr : GuardIR.entails (GuardIR.norm .top)
      (GuardIR.norm (.imp (.nonZero (.var x)) .bot)) = false := by
    simp [GuardIR.entails, GuardIR.simplifyUnder, GuardIR.norm, PureExpr.fold,
      GuardIR.mkNonZero, GuardIR.impN, GuardIR.mkNot, GuardIR.nf, GuardIR.mkImp,
      GuardIR.residual, GuardIR.hasHyp, GuardIR.isTop]
  have hver := WhileLoop.version_of_hoisted (ctx := .top)
    (w := mkCountedDivLoop x d i acc num y) rfl hs
    (GuardIR.isBot_norm_eq_false (env := fun _ => 1) rfl) hpre hnr
  have hinv : evalGuard (execStmt (mkCountedDivLoop x d i acc num y).init env)
      (.nonZero (.var d)) = true := by
    show decide (updateEnv env d (evalPure env (.var x)) d ≠ 0) = true
    rw [updateEnv_same]
    exact decide_eq_true hx
  obtain ⟨_, _, _, h4, h5⟩ := WhileLoop.dualDiv_fast_facts
    (w := mkCountedDivLoop x d i acc num y) (i := i) (d := d) rfl rfl rfl hs
    (execStmt_dec_after_acc hia (execStmt_dec_assign i))
    n env hinv ((updateEnv_of_ne env hid _).trans hi)
  have hfast := h5 (fun _ => rfl) rfl
  refine ⟨?_, by rw [h4, hfast]; omega⟩
  show execLoopCheckCost (n + 1) env (WhileLoop.version .top (mkCountedDivLoop x d i acc num y)) ≤
    n + 2
  rcases hver with hopt | ⟨slow, hopt⟩
  · rw [hopt, hfast]
    omega
  · rw [hopt]
    show guardEvalCost env (.nonZero (.var x)) +
      (if evalGuard env (.nonZero (.var x)) then
        execLoopCheckCost (n + 1) env
          (.whileLoop ((mkCountedDivLoop x d i acc num y).withFacts (.nonZero (.var d))))
      else execLoopCheckCost (n + 1) env slow) ≤ n + 2
    have hgx : evalGuard env (.nonZero (.var x)) = true := decide_eq_true hx
    rw [hgx, hfast]
    show 1 + (n + 1) ≤ n + 2
    omega

/-- Parametric Zero-Divisor Preheader Safety (0 Iterations vs ≥1 Iterations): Under `.top` when `x = 0`,
    `optimizeLoop .top` returns `.done (.val (env₀ acc))` when the loop executes `0` iterations (`i = 0`)
    and safely returns `.done .trap` when the loop executes `n + 1` iterations (`i = n + 1`). -/
theorem optimizeLoop_zero_div_behavior_param (x d i acc : VarId)
    (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (n : Nat) (env₀ env₁ : Env)
    (hx₀ : env₀ x = 0) (hi₀ : env₀ i = 0)
    (hx₁ : env₁ x = 0) (hi₁ : env₁ i = Int.ofNat (n + 1)) :
    let src := LoopProg.whileLoop (mkCountedDivLoop x d i acc num y)
    evalLoop 1 env₀ (optimizeLoop .top src) = .done (.val (env₀ acc)) ∧
      evalLoop (n + 2) env₁ (optimizeLoop .top src) = .done .trap := by
  dsimp only
  have _ := hia
  have _ := hx₀
  rw [optimizeLoop_sound 1 .top _ env₀ rfl, optimizeLoop_sound (n + 2) .top _ env₁ rfl]
  constructor
  · show runWhileSteps (0 + 1) (execStmt (.assign d (.var x)) env₀)
      (mkCountedDivLoop x d i acc num y) = _
    have hc : evalGuard (execStmt (.assign d (.var x)) env₀)
        (mkCountedDivLoop x d i acc num y).cond = false := by
      show decide (updateEnv env₀ d (evalPure env₀ (.var x)) i ≠ 0) = false
      rw [updateEnv_of_ne _ hid]
      exact decide_eq_false (fun h => h hi₀)
    rw [runWhileSteps_exit hc]
    show LoopOutcome.done (.val (updateEnv env₀ d (evalPure env₀ (.var x)) acc)) = _
    rw [updateEnv_of_ne _ (Ne.symm hda)]
  · show runWhileSteps (n + 1 + 1) (execStmt (.assign d (.var x)) env₁)
      (mkCountedDivLoop x d i acc num y) = _
    have hc : evalGuard (execStmt (.assign d (.var x)) env₁)
        (mkCountedDivLoop x d i acc num y).cond = true := by
      show decide (updateEnv env₁ d (evalPure env₁ (.var x)) i ≠ 0) = true
      rw [updateEnv_of_ne _ hid, hi₁]
      exact decide_eq_true (Int.ofNat_succ_ne_zero n)
    have hd0 : evalPure (execStmt (.assign d (.var x)) env₁) (.var d) = 0 :=
      (updateEnv_same env₁ d _).trans hx₁
    have hb : evalExpr (execStmt (.assign d (.var x)) env₁)
        (mkCountedDivLoop x d i acc num y).body = .trap := by
      show evalExpr _ (.add (.pure (.var acc)) (mkDualDivExpr num y (.var d))) = .trap
      simp only [evalExpr, evalExpr_mkDualDivExpr_trap num y hd0]
    exact runWhileSteps_trap hc hb

/-- Parametric Two-Stage Pipeline Inductive Strengthening Elimination: Under `x ≠ 0 ∧ z ≠ 0`,
    `optimizeLoop` strengthens `d ≠ 0` to `d ≠ 0 ∧ nextD ≠ 0` across `d := nextD; i := i - 1`,
    eliminates all checked divisions and loop-version branches, and achieves check cost `n + 1`. -/
theorem optimizeLoop_pipeline_elim_param (x z d nextD i acc : VarId)
    (hda : d ≠ acc) (hna : nextD ≠ acc)
    (hid : i ≠ d) (hin : i ≠ nextD) (hia : i ≠ acc) (hdn : d ≠ nextD)
    (num y : PureExpr) (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n)
    (hctx : evalGuard env (.conj (.nonZero (.var x)) (.nonZero (.var z))) = true) :
    let src := LoopProg.whileLoop (mkPipelineDivLoop x z d nextD i acc num y)
    let opt := optimizeLoop (.conj (.nonZero (.var x)) (.nonZero (.var z))) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt = n + 1 := by
  dsimp only
  obtain ⟨inv, hs, hpos⟩ := strengthenLoopInvariantIR_pipeline_pos acc d nextD i hda hna
    (Ne.symm hid) (Ne.symm hin) hdn (.sub (.var i) (.lit 1))
  have hinit : stmtWritesVar i (mkPipelineDivLoop x z d nextD i acc num y).init = false := by
    simp [mkPipelineDivLoop, stmtWritesVar, Ne.symm hid, Ne.symm hin]
  obtain ⟨h1, h2, h3, _, h5⟩ := optimizeLoop_dualDiv_elim
    (ctx := .conj (.nonZero (.var x)) (.nonZero (.var z)))
    (w := mkPipelineDivLoop x z d nextD i acc num y) (i := i) (d := d) rfl rfl rfl hs
    ⟨fun _ => 1, hpos.eval (fun _ _ => by decide)⟩
    (hoistLoopGuardIR_assign2_of_pos hpos x z)
    (execStmt_dec_after_acc hia
      (execStmt_dec_seq_left (i := i) (A := .assign d (.var nextD))
        (decide_eq_false (Ne.symm hid)) (execStmt_dec_assign i)))
    n env hctx ((execStmt_of_not_writes hinit env).trans hi)
  exact ⟨h1, h2, h3, h5 (fun _ => rfl) rfl⟩

/-- Parametric Non-Invariant Decrementing-Divisor Trap Preservation: Even when `init` sets `d := 1`
    (`x = 1 ≠ 0`), `d := d - 1` violates loop invariance on iteration 2 (`i = 2`), so `optimizeLoop`
    must preserve `.done .trap` (rejecting naive entry-only check elimination). -/
theorem optimizeLoop_decrement_div_trap_param (x d i acc : VarId)
    (hda : d ≠ acc) (hia : i ≠ acc) (hid : i ≠ d)
    (num : PureExpr) (env : Env) (hx : env x = 1) (hi : env i = 2) :
    evalLoop 3 env (optimizeLoop (.nonZero (.var x)) (.whileLoop (mkDecrementDivisorLoop x d i acc num))) =
      .done .trap := by
  have hctx : evalGuard env (.nonZero (.var x)) = true := by
    show decide (env x ≠ 0) = true
    rw [hx]
    rfl
  rw [optimizeLoop_sound 3 _ _ env hctx]
  show runWhileSteps (2 + 1) (execStmt (.assign d (.var x)) env)
    (mkDecrementDivisorLoop x d i acc num) = _
  have hE0d : execStmt (.assign d (.var x)) env d = 1 := (updateEnv_same env d _).trans hx
  have hE0i : execStmt (.assign d (.var x)) env i = 2 := (updateEnv_of_ne env hid _).trans hi
  generalize execStmt (.assign d (.var x)) env = E₀ at hE0d hE0i
  have hc1 : evalGuard E₀ (mkDecrementDivisorLoop x d i acc num).cond = true := by
    show decide (E₀ i ≠ 0) = true
    rw [hE0i]
    rfl
  have hb1 : evalExpr E₀ (mkDecrementDivisorLoop x d i acc num).body =
      .val (evalPure E₀ num / 1) := by
    show evalExpr E₀ (.checkedDiv (.pure num) (.pure (.var d))) = _
    simp [evalExpr, evalPure, hE0d]
  rw [runWhileSteps_step hc1 hb1]
  have hE1d : execStmt (mkDecrementDivisorLoop x d i acc num).latch
      (updateEnv E₀ (mkDecrementDivisorLoop x d i acc num).accVar (evalPure E₀ num / 1)) d = 0 := by
    show updateEnv (updateEnv (updateEnv E₀ acc (evalPure E₀ num / 1)) d
      (updateEnv E₀ acc (evalPure E₀ num / 1) d - 1)) i _ d = 0
    rw [updateEnv_of_ne _ (Ne.symm hid), updateEnv_same, updateEnv_of_ne _ hda, hE0d]
    rfl
  have hE1i : execStmt (mkDecrementDivisorLoop x d i acc num).latch
      (updateEnv E₀ (mkDecrementDivisorLoop x d i acc num).accVar (evalPure E₀ num / 1)) i = 1 := by
    show updateEnv (updateEnv (updateEnv E₀ acc (evalPure E₀ num / 1)) d
        (updateEnv E₀ acc (evalPure E₀ num / 1) d - 1)) i
      (updateEnv (updateEnv E₀ acc (evalPure E₀ num / 1)) d
        (updateEnv E₀ acc (evalPure E₀ num / 1) d - 1) i - 1) i = 1
    rw [updateEnv_same, updateEnv_of_ne _ hid, updateEnv_of_ne _ hia, hE0i]
    rfl
  generalize execStmt (mkDecrementDivisorLoop x d i acc num).latch
    (updateEnv E₀ (mkDecrementDivisorLoop x d i acc num).accVar (evalPure E₀ num / 1)) = E₁
    at hE1d hE1i
  refine runWhileSteps_trap ?_ ?_
  · show decide (E₁ i ≠ 0) = true
    rw [hE1i]
    rfl
  · show evalExpr E₁ (.checkedDiv (.pure num) (.pure (.var d))) = .trap
    simp [evalExpr, evalPure, hE1d]

/-! ### Milestone 3 target theorems: non-vacuous strengthening and elimination across arbitrary latch frames -/

/-- Non-Vacuous Stationary Divisor Strengthening & Preheader Discharge:
    Across `i := stepRhs` for arbitrary `stepRhs : PureExpr`, `strengthenLoopInvariantIR` returns
    `some inv` covering all environments with `env d ≠ 0` and discharging to `.top` across
    `d := x` under `.nonZero (.var x)` (ruling out vacuous `some .bot` and fixture-only latches). -/
theorem strengthenLoopInvariantIR_stationary_safe (accVar d i : VarId)
    (hda : d ≠ accVar) (hdi : d ≠ i) (stepRhs : PureExpr) :
    ∃ inv,
      strengthenLoopInvariantIR accVar (.assign i stepRhs) (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → evalGuard env inv = true) ∧
      (∀ x : VarId, hoistLoopGuardIR (.assign d (.var x)) (.nonZero (.var x)) inv = .top) := by
  exact ⟨_, strengthenLoopInvariantIR_frame hda (decide_eq_false (Ne.symm hdi)),
    fun _ h => decide_eq_true h, fun x => hoistLoopGuardIR_assign1_of_pos (.var rfl) x⟩

/-- Non-Vacuous Pipeline Divisor Strengthening & Preheader Discharge:
    Across `d := nextD; i := stepRhs` for arbitrary `stepRhs : PureExpr`, `strengthenLoopInvariantIR`
    returns `some inv` covering all environments with `env d ≠ 0 ∧ env nextD ≠ 0` and discharging
    to `.top` across `d := x; nextD := z` under `x ≠ 0 ∧ z ≠ 0` (ruling out vacuous `some .bot`
    and fixture-only pipeline latches). -/
theorem strengthenLoopInvariantIR_pipeline_safe (accVar d nextD i : VarId)
    (hda : d ≠ accVar) (hna : nextD ≠ accVar)
    (hdi : d ≠ i) (hni : nextD ≠ i) (hdn : d ≠ nextD) (stepRhs : PureExpr) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq (.assign d (.var nextD)) (.assign i stepRhs))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → env nextD ≠ 0 → evalGuard env inv = true) ∧
      (∀ x z : VarId,
        hoistLoopGuardIR
          (.seq (.assign d (.var x)) (.assign nextD (.var z)))
          (.conj (.nonZero (.var x)) (.nonZero (.var z)))
          inv = .top) := by
  obtain ⟨inv, hs, hpos⟩ :=
    strengthenLoopInvariantIR_pipeline_pos accVar d nextD i hda hna hdi hni hdn stepRhs
  exact ⟨inv, hs,
    fun env h₁ h₂ => hpos.eval (by rintro u (rfl | rfl) <;> assumption),
    fun x z => hoistLoopGuardIR_assign2_of_pos hpos x z⟩

/-- General One-Step Inductive Strengthening Completeness & Non-Vacuity:
    For arbitrary `accVar`, `latch`, and `target`, whenever `cand := GuardIR.conj target g₁`
    (with `g₁ := havocGuardIR accVar (pullbackGuardIR latch target)`) closes in one step under
    `synthesizeGuardIR`, `strengthenLoopInvariantIR` succeeds with `some inv` covering `target ∧ g₁`. -/
theorem strengthenLoopInvariantIR_step_complete (accVar : VarId) (latch : Stmt) (target : GuardIR) :
    let g₁ := havocGuardIR accVar (pullbackGuardIR latch target)
    let cand := GuardIR.conj target g₁
    synthesizeGuardIR cand (havocGuardIR accVar (pullbackGuardIR latch cand)) = .top →
      ∃ inv,
        strengthenLoopInvariantIR accVar latch target = some inv ∧
        (∀ env : Env, evalGuard env target = true → evalGuard env g₁ = true → evalGuard env inv = true) := by
  dsimp only
  intro h
  have hclosed : GuardIR.closedBy (.conj target (GuardIR.loopStep accVar latch target))
      (GuardIR.loopStep accVar latch
        (.conj target (GuardIR.loopStep accVar latch target))) = true := by
    have htop : GuardIR.isTop (synthesizeGuardIR
        (.conj target (GuardIR.loopStep accVar latch target))
        (GuardIR.loopStep accVar latch
          (.conj target (GuardIR.loopStep accVar latch target)))) = true :=
      GuardIR.isTop_iff.mpr h
    unfold GuardIR.closedBy
    rw [GuardIR.entails_eq]
    simp only [htop, Bool.true_or]
  unfold strengthenLoopInvariantIR
  simp only []
  split
  · exact ⟨target, rfl, fun _ ht _ => ht⟩
  · split
    · exact ⟨_, rfl, fun env ht hg => GuardIR.evalGuard_conj_intro ht hg⟩
    · exact ⟨_, rfl, fun env ht hg => GuardIR.evalGuard_conj_intro ht hg⟩

/-- Syntactic Transparency of `havocGuardIR` on Non-Mentioning Guards:
    When `guardMentionsVar v g = false`, `havocGuardIR v g` returns `g` unchanged without
    injecting unnormalized wrapper syntax. -/
theorem havocGuardIR_nonMention_eq (v : VarId) (g : GuardIR)
    (h : guardMentionsVar v g = false) :
    havocGuardIR v g = g := by
  exact havocGuardIR_of_not_mentions h

/-- Unconditional Frame-Preserving `Stmt` Strengthening & Preheader Discharge:
    For ANY `latch : Stmt` built from `skip`/`assign`/`seq`/`ite` that writes neither `d`
    nor `accVar` (`stmtWritesVar d latch = false`, `stmtWritesVar accVar latch = false`),
    `strengthenLoopInvariantIR` returns `some inv` covering all environments with `env d ≠ 0`
    and discharging to `.top` across `d := x` under `.nonZero (.var x)`. -/
theorem strengthenLoopInvariantIR_frame_stmt_safe (accVar d : VarId) (latch : Stmt)
    (hda : d ≠ accVar)
    (hdWrite : stmtWritesVar d latch = false)
    (haWrite : stmtWritesVar accVar latch = false) :
    ∃ inv,
      strengthenLoopInvariantIR accVar latch (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → evalGuard env inv = true) ∧
      (∀ x : VarId, hoistLoopGuardIR (.assign d (.var x)) (.nonZero (.var x)) inv = .top) := by
  have _ := haWrite
  exact ⟨_, strengthenLoopInvariantIR_frame hda hdWrite,
    fun _ h => decide_eq_true h, fun x => hoistLoopGuardIR_assign1_of_pos (.var rfl) x⟩

/-- Unconditional Variable-Swap Latch Strengthening & Preheader Discharge:
    Across `preLatch; tmp := d; d := altD; altD := tmp; postLatch` for arbitrary frame-preserving
    surrounding statements `preLatch` and `postLatch`, `strengthenLoopInvariantIR` returns `some inv`
    covering `env d ≠ 0 ∧ env altD ≠ 0` and discharging to `.top` across `d := x; altD := z`. -/
theorem strengthenLoopInvariantIR_swap_safe (accVar d altD tmp : VarId)
    (preLatch postLatch : Stmt)
    (hda : d ≠ accVar) (hala : altD ≠ accVar) (hta : tmp ≠ accVar)
    (hdal : d ≠ altD) (hdt : d ≠ tmp) (halt : altD ≠ tmp)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreAlt : stmtWritesVar altD preLatch = false)
    (hPreAcc : stmtWritesVar accVar preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostAlt : stmtWritesVar altD postLatch = false)
    (hPostTmp : stmtWritesVar tmp postLatch = false)
    (hPostAcc : stmtWritesVar accVar postLatch = false) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq preLatch
          (.seq (.assign tmp (.var d))
            (.seq (.assign d (.var altD))
              (.seq (.assign altD (.var tmp)) postLatch))))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → env altD ≠ 0 → evalGuard env inv = true) ∧
      (∀ x z : VarId,
        hoistLoopGuardIR
          (.seq (.assign d (.var x)) (.assign altD (.var z)))
          (.conj (.nonZero (.var x)) (.nonZero (.var z)))
          inv = .top) := by
  have _ := hta
  have _ := hPreAcc
  have _ := hPostTmp
  have _ := hPostAcc
  obtain ⟨inv, hs, hpos⟩ := strengthenLoopInvariantIR_swap_pos accVar d altD tmp preLatch
    postLatch hda hala hdal hdt halt hPreD hPreAlt hPostD hPostAlt
  exact ⟨inv, hs,
    fun env h₁ h₂ => hpos.eval (by rintro u (rfl | rfl) <;> assumption),
    fun x z => hoistLoopGuardIR_assign2_of_pos hpos x z⟩

/-- Unconditional Three-Stage Pipeline Strengthening & Preheader Discharge:
    Across `preLatch; d := d₁; d₁ := d₂; postLatch` for arbitrary frame-preserving surrounding
    statements `preLatch` and `postLatch`, `strengthenLoopInvariantIR` strengthens `.nonZero (.var d)`
    across multiple backward steps to `some inv` covering `env d ≠ 0 ∧ env d₁ ≠ 0 ∧ env d₂ ≠ 0`
    and discharging to `.top` across `d := x; d₁ := w; d₂ := z`. -/
theorem strengthenLoopInvariantIR_pipeline3_safe (accVar d d₁ d₂ : VarId)
    (preLatch postLatch : Stmt)
    (hda : d ≠ accVar) (hd₁a : d₁ ≠ accVar) (hd₂a : d₂ ≠ accVar)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (hPreAcc : stmtWritesVar accVar preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : stmtWritesVar d₂ postLatch = false)
    (hPostAcc : stmtWritesVar accVar postLatch = false) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq preLatch
          (.seq (.assign d (.var d₁))
            (.seq (.assign d₁ (.var d₂)) postLatch)))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → env d₁ ≠ 0 → env d₂ ≠ 0 → evalGuard env inv = true) ∧
      (∀ x w z : VarId,
        hoistLoopGuardIR
          (.seq (.assign d (.var x)) (.seq (.assign d₁ (.var w)) (.assign d₂ (.var z))))
          (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z))))
          inv = .top) := by
  have _ := hPreAcc
  have _ := hPostAcc
  obtain ⟨inv, hs, hpos⟩ := strengthenLoopInvariantIR_pipeline3_pos accVar d d₁ d₂ preLatch
    postLatch hda hd₁a hd₂a hdd₁ hdd₂ hd₁d₂ hPreD hPreD₁ hPreD₂ hPostD hPostD₁ hPostD₂
  exact ⟨inv, hs,
    fun env h₀ h₁ h₂ => hpos.eval (by rintro u (rfl | rfl | rfl) <;> assumption),
    fun x w z => hoistLoopGuardIR_assign3_of_pos hpos x w z⟩

/-- Unconditional Branching-`ite` Latch Strengthening & Preheader Discharge:
    Across `preLatch; if branchCond { d := d₁ } else { d := d₂ }; postLatch` for arbitrary
    `branchCond : GuardIR` and arbitrary frame-preserving surrounding statements `preLatch` and
    `postLatch`, `strengthenLoopInvariantIR` returns `some inv` covering
    `env d ≠ 0 ∧ env d₁ ≠ 0 ∧ env d₂ ≠ 0` and discharging to `.top` across `d := x; d₁ := w; d₂ := z`. -/
theorem strengthenLoopInvariantIR_ite_branch_safe (accVar d d₁ d₂ : VarId)
    (branchCond : GuardIR) (preLatch postLatch : Stmt)
    (hda : d ≠ accVar) (hd₁a : d₁ ≠ accVar) (hd₂a : d₂ ≠ accVar)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (hPreAcc : stmtWritesVar accVar preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : stmtWritesVar d₂ postLatch = false)
    (hPostAcc : stmtWritesVar accVar postLatch = false) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq preLatch
          (.seq (.ite branchCond (.assign d (.var d₁)) (.assign d (.var d₂))) postLatch))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : Env, env d ≠ 0 → env d₁ ≠ 0 → env d₂ ≠ 0 → evalGuard env inv = true) ∧
      (∀ x w z : VarId,
        hoistLoopGuardIR
          (.seq (.assign d (.var x)) (.seq (.assign d₁ (.var w)) (.assign d₂ (.var z))))
          (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z))))
          inv = .top) := by
  have _ := hPreAcc
  have _ := hPostAcc
  obtain ⟨inv, hs, hpos⟩ := strengthenLoopInvariantIR_ite_branch_pos accVar d d₁ d₂ branchCond
    preLatch postLatch hda hd₁a hd₂a hdd₁ hdd₂ hd₁d₂ hPreD hPreD₁ hPreD₂ hPostD hPostD₁ hPostD₂
  exact ⟨inv, hs,
    fun env h₀ h₁ h₂ => hpos.eval (by rintro u (rfl | rfl | rfl) <;> assumption),
    fun x w z => hoistLoopGuardIR_assign3_of_pos hpos x w z⟩

/-- Parametric Frame-Preserving Surrounding-`Stmt` Loop Check Elimination:
    Under `.nonZero (.var x)` across `n` counted iterations with arbitrary frame-preserving
    `preLatch` and `postLatch`, `optimizeLoop` eliminates all checked divisions and loop-version
    branches and saves at least `2 * n` runtime checks. -/
theorem optimizeLoop_frame_stmt_elim_param (x d i acc : VarId)
    (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : PureExpr) (preLatch postLatch : Stmt)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreI : stmtWritesVar i preLatch = false)
    (hPreAcc : stmtWritesVar acc preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostI : stmtWritesVar i postLatch = false)
    (hPostAcc : stmtWritesVar acc postLatch = false)
    (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n)
    (hx : evalGuard env (.nonZero (.var x)) = true) :
    let src := LoopProg.whileLoop (mkFrameStmtDivLoop x d i acc num y preLatch postLatch)
    let opt := optimizeLoop (.nonZero (.var x)) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt + 2 * n ≤ execLoopCheckCost (n + 1) env src := by
  dsimp only
  have _ := hPreAcc
  have _ := hPostAcc
  have hw : stmtWritesVar d
      (mkFrameStmtDivLoop x d i acc num y preLatch postLatch).latch = false := by
    simp [mkFrameStmtDivLoop, stmtWritesVar, hPreD, hPostD, hid]
  obtain ⟨h1, h2, h3, h4, _⟩ := optimizeLoop_dualDiv_elim (ctx := .nonZero (.var x))
    (w := mkFrameStmtDivLoop x d i acc num y preLatch postLatch) (i := i) (d := d) rfl rfl rfl
    (strengthenLoopInvariantIR_frame hda hw)
    ⟨fun _ => 1, rfl⟩
    (hoistLoopGuardIR_assign1_of_pos (.var rfl) x)
    (execStmt_dec_after_acc hia
      (execStmt_dec_seq_left (i := i) (A := preLatch) hPreI
        (execStmt_dec_seq_right (i := i) (B := postLatch) (execStmt_dec_assign i) hPostI)))
    n env hx ((updateEnv_of_ne env hid _).trans hi)
  exact ⟨h1, h2, h3, Nat.le_of_eq h4.symm⟩

/-- Parametric Variable-Swap Latch Loop Check Elimination:
    Under `x ≠ 0 ∧ z ≠ 0` across `n` counted iterations of `mkSwapDivLoop` with arbitrary
    frame-preserving `preLatch` and `postLatch`, `optimizeLoop` eliminates all checked divisions
    and loop-version branches and saves at least `2 * n` runtime checks. -/
theorem optimizeLoop_swap_elim_param (x z d altD tmp i acc : VarId)
    (hda : d ≠ acc) (hala : altD ≠ acc) (hta : tmp ≠ acc)
    (hid : i ≠ d) (hial : i ≠ altD) (hit : i ≠ tmp) (hia : i ≠ acc)
    (hdal : d ≠ altD) (hdt : d ≠ tmp) (halt : altD ≠ tmp)
    (num y : PureExpr) (preLatch postLatch : Stmt)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreAlt : stmtWritesVar altD preLatch = false)
    (hPreI : stmtWritesVar i preLatch = false)
    (hPreAcc : stmtWritesVar acc preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostAlt : stmtWritesVar altD postLatch = false)
    (hPostTmp : stmtWritesVar tmp postLatch = false)
    (hPostI : stmtWritesVar i postLatch = false)
    (hPostAcc : stmtWritesVar acc postLatch = false)
    (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n)
    (hctx : evalGuard env (.conj (.nonZero (.var x)) (.nonZero (.var z))) = true) :
    let src := LoopProg.whileLoop (mkSwapDivLoop x z d altD tmp i acc num y preLatch postLatch)
    let opt := optimizeLoop (.conj (.nonZero (.var x)) (.nonZero (.var z))) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt + 2 * n ≤ execLoopCheckCost (n + 1) env src := by
  dsimp only
  have _ := hta
  have _ := hPreAcc
  have _ := hPostTmp
  have _ := hPostAcc
  have hPostD' : stmtWritesVar d (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) = false := by
    simp [stmtWritesVar, hPostD, hid]
  have hPostAlt' : stmtWritesVar altD
      (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) = false := by
    simp [stmtWritesVar, hPostAlt, hial]
  obtain ⟨inv, hs, hpos⟩ := strengthenLoopInvariantIR_swap_pos acc d altD tmp preLatch
    (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) hda hala hdal hdt halt hPreD hPreAlt
    hPostD' hPostAlt'
  have hinit : stmtWritesVar i
      (mkSwapDivLoop x z d altD tmp i acc num y preLatch postLatch).init = false := by
    simp [mkSwapDivLoop, stmtWritesVar, Ne.symm hid, Ne.symm hial]
  obtain ⟨h1, h2, h3, h4, _⟩ := optimizeLoop_dualDiv_elim
    (ctx := .conj (.nonZero (.var x)) (.nonZero (.var z)))
    (w := mkSwapDivLoop x z d altD tmp i acc num y preLatch postLatch) (i := i) (d := d)
    rfl rfl rfl hs
    ⟨fun _ => 1, hpos.eval (fun _ _ => by decide)⟩
    (hoistLoopGuardIR_assign2_of_pos hpos x z)
    (execStmt_dec_after_acc hia
      (execStmt_dec_seq_left (i := i) (A := preLatch) hPreI
        (execStmt_dec_seq_left (i := i) (A := .assign tmp (.var d))
          (decide_eq_false (Ne.symm hit))
          (execStmt_dec_seq_left (i := i) (A := .assign d (.var altD))
            (decide_eq_false (Ne.symm hid))
            (execStmt_dec_seq_left (i := i) (A := .assign altD (.var tmp))
              (decide_eq_false (Ne.symm hial))
              (execStmt_dec_seq_right (i := i) (B := postLatch) (execStmt_dec_assign i)
                hPostI))))))
    n env hctx ((execStmt_of_not_writes hinit env).trans hi)
  exact ⟨h1, h2, h3, Nat.le_of_eq h4.symm⟩

/-- Parametric Three-Stage Pipeline Loop Check Elimination:
    Under `x ≠ 0 ∧ w ≠ 0 ∧ z ≠ 0` across `n` counted iterations of `mkPipeline3DivLoop` with
    arbitrary frame-preserving `preLatch` and `postLatch`, `optimizeLoop` eliminates all checked
    divisions and loop-version branches and saves at least `2 * n` runtime checks. -/
theorem optimizeLoop_pipeline3_elim_param (x w z d d₁ d₂ i acc : VarId)
    (hda : d ≠ acc) (hd₁a : d₁ ≠ acc) (hd₂a : d₂ ≠ acc)
    (hid : i ≠ d) (hid₁ : i ≠ d₁) (hid₂ : i ≠ d₂) (hia : i ≠ acc)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (num y : PureExpr) (preLatch postLatch : Stmt)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (hPreI : stmtWritesVar i preLatch = false)
    (hPreAcc : stmtWritesVar acc preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : stmtWritesVar d₂ postLatch = false)
    (hPostI : stmtWritesVar i postLatch = false)
    (hPostAcc : stmtWritesVar acc postLatch = false)
    (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n)
    (hctx : evalGuard env (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) = true) :
    let src := LoopProg.whileLoop (mkPipeline3DivLoop x w z d d₁ d₂ i acc num y preLatch postLatch)
    let opt := optimizeLoop (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt + 2 * n ≤ execLoopCheckCost (n + 1) env src := by
  dsimp only
  have _ := hPreAcc
  have _ := hPostAcc
  have hPostD' : stmtWritesVar d (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) = false := by
    simp [stmtWritesVar, hPostD, hid]
  have hPostD₁' : stmtWritesVar d₁
      (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) = false := by
    simp [stmtWritesVar, hPostD₁, hid₁]
  have hPostD₂' : stmtWritesVar d₂
      (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) = false := by
    simp [stmtWritesVar, hPostD₂, hid₂]
  obtain ⟨inv, hs, hpos⟩ := strengthenLoopInvariantIR_pipeline3_pos acc d d₁ d₂ preLatch
    (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) hda hd₁a hd₂a hdd₁ hdd₂ hd₁d₂
    hPreD hPreD₁ hPreD₂ hPostD' hPostD₁' hPostD₂'
  have hinit : stmtWritesVar i
      (mkPipeline3DivLoop x w z d d₁ d₂ i acc num y preLatch postLatch).init = false := by
    simp [mkPipeline3DivLoop, stmtWritesVar, Ne.symm hid, Ne.symm hid₁, Ne.symm hid₂]
  obtain ⟨h1, h2, h3, h4, _⟩ := optimizeLoop_dualDiv_elim
    (ctx := .conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z))))
    (w := mkPipeline3DivLoop x w z d d₁ d₂ i acc num y preLatch postLatch) (i := i) (d := d)
    rfl rfl rfl hs
    ⟨fun _ => 1, hpos.eval (fun _ _ => by decide)⟩
    (hoistLoopGuardIR_assign3_of_pos hpos x w z)
    (execStmt_dec_after_acc hia
      (execStmt_dec_seq_left (i := i) (A := preLatch) hPreI
        (execStmt_dec_seq_left (i := i) (A := .assign d (.var d₁))
          (decide_eq_false (Ne.symm hid))
          (execStmt_dec_seq_left (i := i) (A := .assign d₁ (.var d₂))
            (decide_eq_false (Ne.symm hid₁))
            (execStmt_dec_seq_right (i := i) (B := postLatch) (execStmt_dec_assign i)
              hPostI)))))
    n env hctx ((execStmt_of_not_writes hinit env).trans hi)
  exact ⟨h1, h2, h3, Nat.le_of_eq h4.symm⟩

/-- Parametric Branching-`ite` Latch Loop Check Elimination:
    Under `x ≠ 0 ∧ w ≠ 0 ∧ z ≠ 0` across `n` counted iterations of `mkBranchDivLoop` for arbitrary
    `branchCond : GuardIR` and arbitrary frame-preserving `preLatch` and `postLatch`, `optimizeLoop`
    eliminates all checked divisions and loop-version branches and saves at least `2 * n` runtime checks. -/
theorem optimizeLoop_ite_branch_elim_param (x w z d d₁ d₂ i acc : VarId)
    (hda : d ≠ acc) (hd₁a : d₁ ≠ acc) (hd₂a : d₂ ≠ acc)
    (hid : i ≠ d) (hid₁ : i ≠ d₁) (hid₂ : i ≠ d₂) (hia : i ≠ acc)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (branchCond : GuardIR) (num y : PureExpr) (preLatch postLatch : Stmt)
    (hPreD : stmtWritesVar d preLatch = false)
    (hPreD₁ : stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : stmtWritesVar d₂ preLatch = false)
    (hPreI : stmtWritesVar i preLatch = false)
    (hPreAcc : stmtWritesVar acc preLatch = false)
    (hPostD : stmtWritesVar d postLatch = false)
    (hPostD₁ : stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : stmtWritesVar d₂ postLatch = false)
    (hPostI : stmtWritesVar i postLatch = false)
    (hPostAcc : stmtWritesVar acc postLatch = false)
    (n : Nat) (env : Env)
    (hi : env i = Int.ofNat n)
    (hctx : evalGuard env (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) = true) :
    let src := LoopProg.whileLoop (mkBranchDivLoop x w z d d₁ d₂ i acc branchCond num y preLatch postLatch)
    let opt := optimizeLoop (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) src
    loopCheckedDivCount opt = 0 ∧
      loopDivOpCount opt ≤ 1 ∧
      loopBranchCount opt = 0 ∧
      execLoopCheckCost (n + 1) env opt + 2 * n ≤ execLoopCheckCost (n + 1) env src := by
  dsimp only
  have _ := hPreAcc
  have _ := hPostAcc
  have hPostD' : stmtWritesVar d (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) = false := by
    simp [stmtWritesVar, hPostD, hid]
  have hPostD₁' : stmtWritesVar d₁
      (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) = false := by
    simp [stmtWritesVar, hPostD₁, hid₁]
  have hPostD₂' : stmtWritesVar d₂
      (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) = false := by
    simp [stmtWritesVar, hPostD₂, hid₂]
  obtain ⟨inv, hs, hpos⟩ := strengthenLoopInvariantIR_ite_branch_pos acc d d₁ d₂ branchCond
    preLatch (.seq (.assign i (.sub (.var i) (.lit 1))) postLatch) hda hd₁a hd₂a hdd₁ hdd₂
    hd₁d₂ hPreD hPreD₁ hPreD₂ hPostD' hPostD₁' hPostD₂'
  have hinit : stmtWritesVar i
      (mkBranchDivLoop x w z d d₁ d₂ i acc branchCond num y preLatch postLatch).init = false := by
    simp [mkBranchDivLoop, stmtWritesVar, Ne.symm hid, Ne.symm hid₁, Ne.symm hid₂]
  have hbranch : stmtWritesVar i
      (.ite branchCond (.assign d (.var d₁)) (.assign d (.var d₂))) = false := by
    simp [stmtWritesVar, Ne.symm hid]
  obtain ⟨h1, h2, h3, h4, _⟩ := optimizeLoop_dualDiv_elim
    (ctx := .conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z))))
    (w := mkBranchDivLoop x w z d d₁ d₂ i acc branchCond num y preLatch postLatch) (i := i)
    (d := d) rfl rfl rfl hs
    ⟨fun _ => 1, hpos.eval (fun _ _ => by decide)⟩
    (hoistLoopGuardIR_assign3_of_pos hpos x w z)
    (execStmt_dec_after_acc hia
      (execStmt_dec_seq_left (i := i) (A := preLatch) hPreI
        (execStmt_dec_seq_left (i := i)
          (A := .ite branchCond (.assign d (.var d₁)) (.assign d (.var d₂))) hbranch
          (execStmt_dec_seq_right (i := i) (B := postLatch) (execStmt_dec_assign i) hPostI))))
    n env hctx ((execStmt_of_not_writes hinit env).trans hi)
  exact ⟨h1, h2, h3, Nat.le_of_eq h4.symm⟩

end CatSem
