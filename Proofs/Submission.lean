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

end CatSem
