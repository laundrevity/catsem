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

end CatSem
