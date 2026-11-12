import Specs.Defs

namespace CatSem

variable {α β β₁ β₂ γ Term Val S S₀ S₁ S₂ : Type*} [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra β₁] [HeytingAlgebra β₂] [HeytingAlgebra γ]

/-- Soundness: Conjoining state `a` with `synthesizeGuard a b` establishes `b`. -/
theorem synthesizeGuard_sound (a b : α) :
    a ⊓ synthesizeGuard a b ≤ b := by
  sorry

/-- Optimality (Weakest Precondition): Any valid guard `g` implies `synthesizeGuard a b`. -/
theorem synthesizeGuard_weakest (a b g : α) (h : a ⊓ g ≤ b) :
    g ≤ synthesizeGuard a b := by
  sorry

/-- Heyting Adjunction: Conjoining `a` with `g` establishes `b` if and only if `g` implies `synthesizeGuard a b`. -/
theorem synthesizeGuard_adjunction (a b g : α) :
    a ⊓ g ≤ b ↔ g ≤ synthesizeGuard a b := by
  sorry

/-- Edge Soundness: Conjoining state `a` at block `u` with `synthesizeEdgeGuard T a b`
    guarantees `b` holds after the forward transfer `T.post` at block `v`. -/
theorem synthesizeEdgeGuard_sound (T : CFGTransfer α β) (a : α) (b : β) :
    T.post (a ⊓ synthesizeEdgeGuard T a b) ≤ b := by
  sorry

/-- Edge Optimality (Weakest Precondition): Any local guard `g` at block `u` whose
    forward transfer satisfies `T.post (a ⊓ g) ≤ b` implies `g ≤ synthesizeEdgeGuard T a b`. -/
theorem synthesizeEdgeGuard_weakest (T : CFGTransfer α β) (a : α) (b : β) (g : α)
    (h : T.post (a ⊓ g) ≤ b) :
    g ≤ synthesizeEdgeGuard T a b := by
  sorry

/-- Branch Split Adjunction: Across two branch transitions `T₁ : CFGTransfer α β₁` and
    `T₂ : CFGTransfer α β₂`, the meet of the synthesized branch guards is the exact weakest
    guard establishing both `b₁` and `b₂` along their respective branches. -/
theorem synthesizeBranchGuard_iff (T₁ : CFGTransfer α β₁) (T₂ : CFGTransfer α β₂)
    (a : α) (b₁ : β₁) (b₂ : β₂) (g : α) :
    T₁.post (a ⊓ g) ≤ b₁ ∧ T₂.post (a ⊓ g) ≤ b₂ ↔
      g ≤ synthesizeEdgeGuard T₁ a b₁ ⊓ synthesizeEdgeGuard T₂ a b₂ := by
  sorry

/-- Meet Preservation: Every `T : CFGTransfer α β` preserves binary meets on pullbacks. -/
theorem pullback_map_inf (T : CFGTransfer α β) (b₁ b₂ : β) :
    T.pullback (b₁ ⊓ b₂) = T.pullback b₁ ⊓ T.pullback b₂ := by
  sorry

/-- Path Composition: Guard synthesis across a composed path `T₁.comp T₂` equals
    nested stage-by-stage guard synthesis. -/
theorem synthesizeEdgeGuard_comp (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ)
    (a : α) (c : γ) :
    synthesizeEdgeGuard (T₁.comp T₂) a c = synthesizeEdgeGuard T₁ a (T₂.pullback c) := by
  sorry

/-- Conjunctive Target Decomposition: Synthesizing a guard for a conjunction `b₁ ⊓ b₂`
    at the target block equals the meet of the synthesized guards. -/
theorem synthesizeEdgeGuard_map_inf (T : CFGTransfer α β) (a : α) (b₁ b₂ : β) :
    synthesizeEdgeGuard T a (b₁ ⊓ b₂) =
      synthesizeEdgeGuard T a b₁ ⊓ synthesizeEdgeGuard T a b₂ := by
  sorry

/-- Diamond Join Adjunction: Given two converging CFG paths `P₁ P₂ : CFGTransfer α γ`
    from entry `α` to join block `γ`, a guard `g : α` guarantees that the joined post-state
    at `γ` satisfies `c` if and only if `g` implies the meet of the path guards. -/
theorem synthesizeDiamondGuard_iff (P₁ P₂ : CFGTransfer α γ) (a : α) (c : γ) (g : α) :
    P₁.post (a ⊓ g) ⊔ P₂.post (a ⊓ g) ≤ c ↔
      g ≤ synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c := by
  sorry

/-- Kripke-Joyal Loop Stability: A predicate `inv` is a forward loop invariant
    if and only if it is Kripke-Joyal stable under back-edge pullback (`inv ≤ L.pullback inv`). -/
theorem isLoopInvariant_iff_le_pullback (L : CFGTransfer α α) (inv : α) :
    IsLoopInvariant L inv ↔ inv ≤ L.pullback inv := by
  sorry

/-- Trivial Abductive Guard Characterization: `IsLoopInvariant L inv` holds if and only if
    the abductive loop-step guard is trivial (`synthesizeLoopStepGuard L inv = ⊤`). -/
theorem isLoopInvariant_iff_guard_eq_top (L : CFGTransfer α α) (inv : α) :
    IsLoopInvariant L inv ↔ synthesizeLoopStepGuard L inv = ⊤ := by
  sorry

/-- Loop-Step Guard Soundness: Conjoining any candidate invariant `inv` with its abductive
    loop-step guard guarantees the invariant holds after executing the loop body. -/
theorem synthesizeLoopStepGuard_sound (L : CFGTransfer α α) (inv : α) :
    L.post (inv ⊓ synthesizeLoopStepGuard L inv) ≤ inv := by
  sorry

/-- Conjunctive Loop Invariance: If `inv₁` and `inv₂` are both loop invariants for `L`,
    their conjunction `inv₁ ⊓ inv₂` is also a loop invariant. -/
theorem isLoopInvariant_inf (L : CFGTransfer α α) (inv₁ inv₂ : α) :
    IsLoopInvariant L inv₁ → IsLoopInvariant L inv₂ → IsLoopInvariant L (inv₁ ⊓ inv₂) := by
  sorry

/-- Two-Step Loop Invariance: If `IsLoopInvariant L inv`, then `inv` is preserved
    across two back-to-back iterations `(L.comp L).post inv ≤ inv`. -/
theorem isLoopInvariant_iterate_two (L : CFGTransfer α α) (inv : α)
    (h : IsLoopInvariant L inv) :
    (L.comp L).post inv ≤ inv := by
  sorry

/-- Hoisted Guard Entry Target Soundness: If `IsInductiveFor L inv target`, conjoining
    preheader state `a₀` with `hoistLoopGuard E a₀ inv` establishes `target` on loop entry. -/
theorem hoistLoopGuard_entry_target (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    E.post (a₀ ⊓ hoistLoopGuard E a₀ inv) ≤ target := by
  sorry

/-- Hoisted Guard One-Step Invariance: If `IsLoopInvariant L inv`, conjoining `a₀` with
    `hoistLoopGuard E a₀ inv` preserves `inv` after executing the preheader followed by the loop body. -/
theorem hoistLoopGuard_step_invariant (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv : β) (h : IsLoopInvariant L inv) :
    L.post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ inv := by
  sorry

/-- Hoisted Guard One-Step Target Soundness: If `IsInductiveFor L inv target`, the hoisted
    preheader guard guarantees `target` still holds after executing the preheader followed by the loop body. -/
theorem hoistLoopGuard_step_target (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    L.post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ target := by
  sorry

/-- Arbitrary-Iteration Loop Invariance: If `IsLoopInvariant L inv`, then `inv` is preserved
    across any number of loop iterations (`∀ n : ℕ, (L.iterate n).post inv ≤ inv`). -/
theorem isLoopInvariant_iterate (L : CFGTransfer α α) (inv : α)
    (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post inv ≤ inv := by
  sorry

/-- Arbitrary-Iteration Kripke-Joyal Pullback Stability: If `IsLoopInvariant L inv`, then `inv`
    is Kripke-Joyal stable under pullback along any `n`-fold loop path (`∀ n : ℕ, inv ≤ (L.iterate n).pullback inv`). -/
theorem isLoopInvariant_iterate_pullback (L : CFGTransfer α α) (inv : α)
    (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, inv ≤ (L.iterate n).pullback inv := by
  sorry

/-- Hoisted Guard Arbitrary-Iteration Invariance: If `IsLoopInvariant L inv`, the single
    preheader guard `hoistLoopGuard E a₀ inv` preserves `inv` after entering the loop and running `n` iterations. -/
theorem hoistLoopGuard_iterate_invariant (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv : β) (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ inv := by
  sorry

/-- Hoisted Guard Arbitrary-Iteration Target Soundness: If `IsInductiveFor L inv target`,
    the hoisted preheader guard guarantees `target` holds after entering the loop and running `n` iterations. -/
theorem hoistLoopGuard_iterate_target (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ target := by
  sorry

/-- Kripke-Joyal Forcing Adjunction: Across any `T : CFGTransfer α β`,
    `a` forces `q` after `T` if and only if `a` locally forces the pullback `T.pullback q`. -/
theorem forcesAfter_iff_pullback (T : CFGTransfer α β) (a : α) (q : β) :
    ForcesAfter T a q ↔ Forces a (T.pullback q) := by
  sorry

/-- Kripke-Joyal Implication Forcing: At stage `a`, a guarded stage `a ⊓ g` forces `p`
    if and only if `g` forces the synthesized guard `synthesizeGuard a p`. -/
theorem forces_guard_iff (a p g : α) :
    Forces (a ⊓ g) p ↔ Forces g (synthesizeGuard a p) := by
  sorry

/-- Kripke-Joyal Rewrite-Chain Forcing: For two conditional rewrite preconditions `p₁ p₂ : α`,
    a guarded stage `a ⊓ g` forces `p₁ ⊓ p₂` if and only if `g` forces the meet of their synthesized guards. -/
theorem forces_rewrite_chain_iff (a p₁ p₂ g : α) :
    Forces (a ⊓ g) (p₁ ⊓ p₂) ↔ Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) := by
  sorry

/-- Kripke-Joyal Hoisted Loop Forcing: If `IsInductiveFor L inv target`, then for every
    iteration count `n : ℕ`, the guarded preheader stage forces `target` along the composed
    morphism `E.comp (L.iterate n)`. -/
theorem forcesAfter_hoistLoopGuard_iterate (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    ∀ n : ℕ, ForcesAfter (E.comp (L.iterate n)) (a₀ ⊓ hoistLoopGuard E a₀ inv) target := by
  sorry

/-- Reflexivity of Guarded Equivalence: Any term `t` is guardedly equivalent to itself under `⊤`. -/
theorem guardedEquiv_refl (eval : α → Term → Val) (t : Term) :
    GuardedEquiv eval ⊤ t t := by
  sorry

/-- Symmetry of Guarded Equivalence: Guarded equivalence is symmetric. -/
theorem guardedEquiv_symm (eval : α → Term → Val) (p : α) (t₁ t₂ : Term) :
    GuardedEquiv eval p t₁ t₂ → GuardedEquiv eval p t₂ t₁ := by
  sorry

/-- Conjunctive Transitivity of Guarded Equivalence: Chaining two conditional rewrites
    `GuardedEquiv eval p₁ t₁ t₂` and `GuardedEquiv eval p₂ t₂ t₃` yields a sound equivalence
    under the conjoined guard `p₁ ⊓ p₂`. -/
theorem guardedEquiv_trans_inf (eval : α → Term → Val) (p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : GuardedEquiv eval p₁ t₁ t₂) (h₂ : GuardedEquiv eval p₂ t₂ t₃) :
    GuardedEquiv eval (p₁ ⊓ p₂) t₁ t₃ := by
  sorry

/-- Abductive Rewrite-Chain Soundness: Given `GuardedEquiv eval p₁ t₁ t₂` and
    `GuardedEquiv eval p₂ t₂ t₃`, at any stage `a : α`, conjoining `a` with the synthesized
    residual guard `synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂` guarantees `t₁` and `t₃`
    evaluate identically at the guarded stage. -/
theorem guardedEquiv_synthesize_chain (eval : α → Term → Val) (a p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : GuardedEquiv eval p₁ t₁ t₂) (h₂ : GuardedEquiv eval p₂ t₂ t₃) :
    eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) t₁ =
      eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) t₃ := by
  sorry

/-- Guarded Equivalence Monotonicity (Weakening): If `Forces p q` and
    `GuardedEquiv eval q t₁ t₂`, then `GuardedEquiv eval p t₁ t₂`. -/
theorem guardedEquiv_weaken (eval : α → Term → Val) (p q : α) (t₁ t₂ : Term)
    (hpq : Forces p q) (h : GuardedEquiv eval q t₁ t₂) :
    GuardedEquiv eval p t₁ t₂ := by
  sorry

/-- Kripke-Joyal Pullback of Guarded Equivalence: If `GuardedEquiv evalβ q t₁ t₂`,
    then `GuardedEquiv (pullbackEval T evalβ) (T.pullback q) t₁ t₂`. -/
theorem guardedEquiv_pullback (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (q : β) (t₁ t₂ : Term) (h : GuardedEquiv evalβ q t₁ t₂) :
    GuardedEquiv (pullbackEval T evalβ) (T.pullback q) t₁ t₂ := by
  sorry

/-- Inter-Block Abductive Guarded Rewrite Soundness: If `GuardedEquiv evalβ q t₁ t₂`,
    then at any upstream stage `a : α`, conjoining `a` with `synthesizeEdgeGuard T a q`
    guarantees `t₁` and `t₂` evaluate identically after transferring across `T`. -/
theorem guardedEquiv_edge_synthesize (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (a : α) (q : β) (t₁ t₂ : Term) (h : GuardedEquiv evalβ q t₁ t₂) :
    evalβ (T.post (a ⊓ synthesizeEdgeGuard T a q)) t₁ =
      evalβ (T.post (a ⊓ synthesizeEdgeGuard T a q)) t₂ := by
  sorry

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
  sorry

/-- Binary Congruence of Guarded Equivalence: Under `CompatibleOp2 eval op semOp`,
    guarded equivalences on subterms compose under the meet of their guards. -/
theorem guardedEquiv_congr2 (eval : α → Term → Val)
    (op : Term → Term → Term) (semOp : α → Val → Val → Val)
    (p₁ p₂ : α) (t₁ u₁ t₂ u₂ : Term)
    (hcompat : CompatibleOp2 eval op semOp)
    (h₁ : GuardedEquiv eval p₁ t₁ u₁) (h₂ : GuardedEquiv eval p₂ t₂ u₂) :
    GuardedEquiv eval (p₁ ⊓ p₂) (op t₁ t₂) (op u₁ u₂) := by
  sorry

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
  sorry

/-- Pullback Meet Commutativity for Guarded Equivalence: Across any `T : CFGTransfer α β`,
    guarded equivalence under `T.pullback (q₁ ⊓ q₂)` is equivalent to guarded equivalence
    under `T.pullback q₁ ⊓ T.pullback q₂`. -/
theorem guardedEquiv_pullback_inf_commute (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (q₁ q₂ : β) (t₁ t₂ : Term) :
    GuardedEquiv (pullbackEval T evalβ) (T.pullback (q₁ ⊓ q₂)) t₁ t₂ ↔
      GuardedEquiv (pullbackEval T evalβ) (T.pullback q₁ ⊓ T.pullback q₂) t₁ t₂ := by
  sorry

/-- Diamond Join Guarded Rewrite Soundness: Given two converging CFG paths
    `P₁ P₂ : CFGTransfer α γ` and a downstream rewrite `GuardedEquiv evalγ c t₁ t₂`,
    conjoining `a` with `g := synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c`
    guarantees `t₁` and `t₂` evaluate identically along both paths at the join block. -/
theorem guardedEquiv_diamond (P₁ P₂ : CFGTransfer α γ) (evalγ : γ → Term → Val)
    (a : α) (c : γ) (t₁ t₂ : Term) (h : GuardedEquiv evalγ c t₁ t₂) :
    let g := synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c
    evalγ (P₁.post (a ⊓ g)) t₁ = evalγ (P₁.post (a ⊓ g)) t₂ ∧
      evalγ (P₂.post (a ⊓ g)) t₁ = evalγ (P₂.post (a ⊓ g)) t₂ := by
  sorry

/-- Concrete Pullback Application: Applying `(stateTransfer step).pullback Q` at `s₁`
    computes the weakest precondition `Q (step s₁)`. -/
theorem stateTransfer_pullback_apply (step : S₁ → S₂) (Q : S₂ → Prop) (s₁ : S₁) :
    (stateTransfer step).pullback Q s₁ ↔ Q (step s₁) := by
  sorry

/-- Concrete Edge Guard Synthesis: Pointwise evaluation of `synthesizeEdgeGuard (stateTransfer step) P Q`
    at state `s₁` is the logical implication `P s₁ → Q (step s₁)`. -/
theorem stateTransfer_synthesizeEdgeGuard_apply (step : S₁ → S₂)
    (P : S₁ → Prop) (Q : S₂ → Prop) (s₁ : S₁) :
    synthesizeEdgeGuard (stateTransfer step) P Q s₁ ↔ (P s₁ → Q (step s₁)) := by
  sorry

/-- Concrete Hoare Loop Invariance: `IsLoopInvariant (stateTransfer step) inv` holds if and only if
    `inv` is preserved pointwise by `step` (`∀ s, inv s → inv (step s)`). -/
theorem stateTransfer_isLoopInvariant_iff (step : S → S) (inv : S → Prop) :
    IsLoopInvariant (stateTransfer step) inv ↔ ∀ s, inv s → inv (step s) := by
  sorry

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
  sorry

/-! ## Milestone 1: Executable Guarded Expression Optimizer & Concrete State Bridge -/

/-- Computable Heyting guard synthesis on `GuardIR` syntax. -/
def synthesizeGuardIR (a b : GuardIR) : GuardIR :=
  sorry

/-- Computable context-sensitive guarded expression optimizer on `Expr`. -/
def optimizeExpr (ctx : GuardIR) (e : Expr) : Expr :=
  sorry

/-- Stage-to-Machine-State Bridge Equivalence: `GuardedEquiv (liftEval run) P t₁ t₂` holds
    if and only if `t₁` and `t₂` produce identical concrete outcomes on every state satisfying `P`. -/
theorem liftEval_guardedEquiv_iff {Out : Type*} (run : S → Term → Out)
    (P : S → Prop) (t₁ t₂ : Term) :
    GuardedEquiv (liftEval run) P t₁ t₂ ↔ ∀ s, P s → run s t₁ = run s t₂ := by
  sorry

/-- Denotational Compatibility of `Expr.add` with `liftEval evalExpr`. -/
theorem exprAdd_compatibleOp2 :
    CompatibleOp2 (liftEval evalExpr) Expr.add (liftBinarySem (fun x y => .val (x + y))) := by
  sorry

/-- Denotational Compatibility of `Expr.checkedDiv` with `liftEval evalExpr`. -/
theorem exprCheckedDiv_compatibleOp2 :
    CompatibleOp2 (liftEval evalExpr) Expr.checkedDiv
      (liftBinarySem (fun x y => if y = 0 then .trap else .val (x / y))) := by
  sorry

/-- Categorical Realization of `synthesizeGuardIR`: Denotation commutes with abstract `synthesizeGuard`. -/
theorem synthesizeGuardIR_denote (a b : GuardIR) :
    denoteGuard (synthesizeGuardIR a b) = synthesizeGuard (denoteGuard a) (denoteGuard b) := by
  sorry

/-- Universal Property (Heyting Adjunction) of `synthesizeGuardIR` in `Env → Prop`. -/
theorem synthesizeGuardIR_universal (a b : GuardIR) (g : Env → Prop) :
    denoteGuard a ⊓ g ≤ denoteGuard b ↔ g ≤ denoteGuard (synthesizeGuardIR a b) := by
  sorry

/-- Syntactic Self-Discharge: Synthesizing a non-zero guard already present in context yields `.top`. -/
theorem synthesizeGuardIR_discharge_self (p : PureExpr) :
    synthesizeGuardIR (.nonZero p) (.nonZero p) = .top := by
  sorry

/-- Stage-Guarded Soundness of `optimizeExpr` via `GuardedEquiv` and `liftEval`. -/
theorem optimizeExpr_guardedEquiv (ctx : GuardIR) (e : Expr) :
    GuardedEquiv (liftEval evalExpr) (denoteGuard ctx) (optimizeExpr ctx e) e := by
  sorry

/-- Concrete Operational Soundness of `optimizeExpr`: Whenever `evalGuard env ctx = true`,
    the optimized expression evaluates to the exact same `Outcome` as the original expression. -/
theorem optimizeExpr_sound (ctx : GuardIR) (e : Expr) (env : Env) :
    evalGuard env ctx = true → evalExpr env (optimizeExpr ctx e) = evalExpr env e := by
  sorry

/-- Known-Context Check Elimination: Under context `v₀ ≠ 0`, `optimizeExpr` eliminates all
    checked divisions, introduces zero runtime guard branches, and incurs zero runtime check cost. -/
theorem optimizeExpr_known_ctx_elim (env : Env) :
    checkedDivCount (optimizeExpr (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
      guardBranchCount (optimizeExpr (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
      execCheckCost env (optimizeExpr (.nonZero (.var 0)) m1BenchExpr) = 0 := by
  sorry

/-- Guarded Algebraic Cancellation: Under context `v₀ ≠ 0`, `(v₁ * v₀) / v₀` eliminates division completely. -/
theorem optimizeExpr_cancel_div :
    divOpCount (optimizeExpr (.nonZero (.var 0)) m1CancelExpr) = 0 := by
  sorry

/-- Unknown-Context Guard Deduplication: Under trivial context `.top`, `optimizeExpr` reduces
    runtime check cost on `m1BenchExpr` from `2` down to at most `1` whenever `v₀ ≠ 0`. -/
theorem optimizeExpr_unknown_ctx_dedup (env : Env) (h : env 0 ≠ 0) :
    execCheckCost env (optimizeExpr .top m1BenchExpr) ≤ 1 ∧
      execCheckCost env m1BenchExpr = 2 := by
  sorry

/-- Trap Preservation (Negative Safety Test): Under trivial context `.top`, when `v₀ = 0`,
    `optimizeExpr .top m1BenchExpr` still safely traps rather than triggering `.ub` or fabricating a value. -/
theorem optimizeExpr_zero_div_trap (env : Env) (h : env 0 = 0) :
    evalExpr env (optimizeExpr .top m1BenchExpr) = .trap := by
  sorry

/-- Right-Top Residual Normalization: Synthesizing `.top` from any context `a` yields `.top`. -/
theorem synthesizeGuardIR_top_right (a : GuardIR) :
    synthesizeGuardIR a .top = .top := by
  sorry

/-- Left-Bottom Residual Normalization: Synthesizing any target `b` from inconsistent context `.bot` yields `.top`. -/
theorem synthesizeGuardIR_bot_left (b : GuardIR) :
    synthesizeGuardIR .bot b = .top := by
  sorry

/-- Top-Antecedent Atomic Normalization: Synthesizing `.nonZero p` from trivial context `.top`
    returns `.nonZero p` directly rather than an unsimplified `.imp .top (.nonZero p)` wrapper. -/
theorem synthesizeGuardIR_top_left_nonZero (p : PureExpr) :
    synthesizeGuardIR .top (.nonZero p) = .nonZero p := by
  sorry

/-- Left Conjunctive Context Discharge: Synthesizing `.nonZero p` when `.nonZero p` appears on the
    left of a conjunctive context yields `.top`. -/
theorem synthesizeGuardIR_discharge_conj_left (p : PureExpr) (rest : GuardIR) :
    synthesizeGuardIR (.conj (.nonZero p) rest) (.nonZero p) = .top := by
  sorry

/-- Right Conjunctive Context Discharge: Synthesizing `.nonZero p` when `.nonZero p` appears on the
    right of a conjunctive context yields `.top`. -/
theorem synthesizeGuardIR_discharge_conj_right (rest : GuardIR) (p : PureExpr) :
    synthesizeGuardIR (.conj rest (.nonZero p)) (.nonZero p) = .top := by
  sorry

/-- Duplicate Conjunctive Target Normalization: Synthesizing `.conj (.nonZero p) (.nonZero p)` from
    `.top` deduplicates the residual guard to `.nonZero p`. -/
theorem synthesizeGuardIR_dedup_conj (p : PureExpr) :
    synthesizeGuardIR .top (.conj (.nonZero p) (.nonZero p)) = .nonZero p := by
  sorry

/-- Parametric Checked-Division Elimination: For arbitrary pure operands `num, d` and extra context `extra`,
    `optimizeExpr` eliminates `.checkedDiv (.pure num) (.pure d)` under `.nonZero d` and conjunctive
    contexts containing `.nonZero d` with zero guard branches and zero runtime check cost. -/
theorem optimizeExpr_elim_checkedDiv_param (num d : PureExpr) (extra : GuardIR) (env : Env) :
    checkedDivCount (optimizeExpr (.nonZero d) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      checkedDivCount (optimizeExpr (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      checkedDivCount (optimizeExpr (.conj extra (.nonZero d)) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      guardBranchCount (optimizeExpr (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      execCheckCost env (optimizeExpr (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 := by
  sorry

/-- Parametric Guarded Algebraic Cancellation: Under `.nonZero d`, both `(x * d) / d` and `(d * x) / d`
    eliminate division completely for arbitrary `PureExpr` operands `x, d`. -/
theorem optimizeExpr_cancel_div_param (x d : PureExpr) :
    divOpCount (optimizeExpr (.nonZero d) (mkCancelExpr x d)) = 0 ∧
      divOpCount (optimizeExpr (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d))) = 0 := by
  sorry

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
  sorry

/-- Parametric Known-Context Elimination: Under `.nonZero d`, `optimizeExpr` on `mkDualDivExpr x y d`
    eliminates all checked divisions, introduces zero guard branches, and incurs zero runtime check cost. -/
theorem optimizeExpr_known_ctx_elim_param (x y d : PureExpr) (env : Env) :
    checkedDivCount (optimizeExpr (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
      guardBranchCount (optimizeExpr (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
      execCheckCost env (optimizeExpr (.nonZero d) (mkDualDivExpr x y d)) = 0 := by
  sorry

/-- Parametric Unknown-Context Guard Deduplication: Under `.top`, for any `x, y, d` and `env` with
    `evalPure env d ≠ 0`, `optimizeExpr` reduces runtime check cost on `mkDualDivExpr x y d` from `2` to `≤ 1`. -/
theorem optimizeExpr_unknown_ctx_dedup_param (x y d : PureExpr) (env : Env)
    (h : evalPure env d ≠ 0) :
    execCheckCost env (optimizeExpr .top (mkDualDivExpr x y d)) ≤ 1 ∧
      execCheckCost env (mkDualDivExpr x y d) = 2 := by
  sorry

/-- Parametric Trap Preservation: Under `.top`, for any `x, y, d` and `env` with `evalPure env d = 0`,
    `optimizeExpr .top (mkDualDivExpr x y d)` safely traps. -/
theorem optimizeExpr_zero_div_trap_param (x y d : PureExpr) (env : Env)
    (h : evalPure env d = 0) :
    evalExpr env (optimizeExpr .top (mkDualDivExpr x y d)) = .trap := by
  sorry

/-! ## Milestone 2: Imperative CFG Statements, Syntactic Pullbacks & Diamond Block Optimization -/

/-- Computable syntactic weakest-precondition pullback of a `GuardIR` across an imperative `Stmt`. -/
def pullbackGuardIR (s : Stmt) (g : GuardIR) : GuardIR :=
  sorry

/-- Computable edge guard synthesis across an imperative `Stmt` from pre-context `a` to post-guard `b`. -/
def synthesizeStmtGuardIR (s : Stmt) (a b : GuardIR) : GuardIR :=
  sorry

/-- Computable context-sensitive block optimizer across `BlockProg` statement prefixes and return expressions. -/
def optimizeBlock (ctx : GuardIR) (prog : BlockProg) : BlockProg :=
  sorry

/-- Pulled-Back State-Transfer Lifting Equivalence: `GuardedEquiv` along
    `pullbackEval (stateTransfer step) (liftEval run)` at predicate `P` holds if and only if
    `t₁` and `t₂` produce identical concrete outcomes in `step s` whenever `P s` holds. -/
theorem pullbackEval_stateTransfer_liftEval_iff {Out : Type*}
    (step : S₁ → S₂) (run : S₂ → Term → Out) (P : S₁ → Prop) (t₁ t₂ : Term) :
    GuardedEquiv (pullbackEval (stateTransfer step) (liftEval run)) P t₁ t₂ ↔
      ∀ s, P s → run (step s) t₁ = run (step s) t₂ := by
  sorry

/-- Categorical Realization of `pullbackGuardIR`: Denotation commutes with `(stateTransfer (execStmt s)).pullback`. -/
theorem pullbackGuardIR_denote (s : Stmt) (g : GuardIR) :
    denoteGuard (pullbackGuardIR s g) =
      (stateTransfer (execStmt s)).pullback (denoteGuard g) := by
  sorry

/-- Contravariant Compositionality of `pullbackGuardIR` on Sequential Statements:
    Denotation on `.seq s₁ s₂` equals the composed `CFGTransfer` pullback. -/
theorem pullbackGuardIR_seq (s₁ s₂ : Stmt) (g : GuardIR) :
    denoteGuard (pullbackGuardIR (.seq s₁ s₂) g) =
      ((stateTransfer (execStmt s₁)).comp (stateTransfer (execStmt s₂))).pullback (denoteGuard g) := by
  sorry

/-- Categorical Realization of `synthesizeStmtGuardIR`: Denotation commutes with abstract `synthesizeEdgeGuard`
    along `stateTransfer (execStmt s)`. -/
theorem synthesizeStmtGuardIR_denote (s : Stmt) (a b : GuardIR) :
    denoteGuard (synthesizeStmtGuardIR s a b) =
      synthesizeEdgeGuard (stateTransfer (execStmt s)) (denoteGuard a) (denoteGuard b) := by
  sorry

/-- Universal Property (Kripke-Joyal / Galois Adjunction) of `synthesizeStmtGuardIR`:
    `ForcesAfter` across `execStmt s` under `denoteGuard a ⊓ g` holds iff `g` implies the synthesized guard. -/
theorem synthesizeStmtGuardIR_universal (s : Stmt) (a b : GuardIR) (g : Env → Prop) :
    ForcesAfter (stateTransfer (execStmt s)) (denoteGuard a ⊓ g) (denoteGuard b) ↔
      g ≤ denoteGuard (synthesizeStmtGuardIR s a b) := by
  sorry

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
  sorry

/-- Non-Zero Literal Discharge: Synthesizing `.nonZero (.lit n)` across `.skip` from `.top`
    normalizes to `.top` whenever `n ≠ 0`. -/
theorem synthesizeStmtGuardIR_lit_nonZero (n : Int) (hn : n ≠ 0) :
    synthesizeStmtGuardIR .skip .top (.nonZero (.lit n)) = .top := by
  sorry

/-- Assignment Pullback Self-Discharge: Across `v := rhs`, pre-context `.nonZero rhs`
    discharges post-requirement `.nonZero (.var v)` to `.top`. -/
theorem synthesizeStmtGuardIR_assign_self (v : VarId) (rhs : PureExpr) :
    synthesizeStmtGuardIR (.assign v rhs) (.nonZero rhs) (.nonZero (.var v)) = .top := by
  sorry

/-- Diamond Safe-Divisor Discharge: Across `if x == 0 then d := n else d := x` with `n ≠ 0`,
    post-requirement `.nonZero (.var d)` discharges unconditionally from `.top` to `.top`. -/
theorem synthesizeStmtGuardIR_diamond_safe (x d : VarId) (n : Int) (hn : n ≠ 0) :
    synthesizeStmtGuardIR
      (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)))
      .top (.nonZero (.var d)) = .top := by
  sorry

/-- Stage-Guarded Soundness of `optimizeBlock` via `GuardedEquiv` and `liftEval evalBlock`. -/
theorem optimizeBlock_guardedEquiv (ctx : GuardIR) (prog : BlockProg) :
    GuardedEquiv (liftEval evalBlock) (denoteGuard ctx) (optimizeBlock ctx prog) prog := by
  sorry

/-- Concrete Operational Soundness of `optimizeBlock`: Whenever `evalGuard env ctx = true`,
    `optimizeBlock ctx prog` produces the exact same `Outcome` as `prog`. -/
theorem optimizeBlock_sound (ctx : GuardIR) (prog : BlockProg) (env : Env) :
    evalGuard env ctx = true → evalBlock env (optimizeBlock ctx prog) = evalBlock env prog := by
  sorry

/-- Parametric Non-Zero Literal Divisor Elimination: On `{ body := .skip, ret := mkDualDivExpr num y (.lit n) }`
    with `n ≠ 0` under `.top`, `optimizeBlock` eliminates all checked divisions, cancels the algebraic
    factor, introduces zero guard branches, and reduces block runtime check cost to `0`. -/
theorem optimizeBlock_literal_div_elim_param (num y : PureExpr) (n : Int) (hn : n ≠ 0) (env : Env) :
    let prog : BlockProg := { body := .skip, ret := mkDualDivExpr num y (.lit n) }
    checkedDivCount (optimizeBlock .top prog).ret = 0 ∧
      divOpCount (optimizeBlock .top prog).ret ≤ 1 ∧
      guardBranchCount (optimizeBlock .top prog).ret = 0 ∧
      execBlockCheckCost env (optimizeBlock .top prog) = 0 := by
  sorry

/-- Parametric Sequential Aliasing & Clobber Elimination: Under `.nonZero (.var x)` with `d ≠ x`,
    across `d := x; x := 0`, `optimizeBlock` preserves `d ≠ 0` despite clobbering `x` and eliminates
    all checked divisions on divisor `d` with zero runtime check cost. -/
theorem optimizeBlock_seq_clobber_elim_param (x d : VarId) (hxd : d ≠ x)
    (num y : PureExpr) (env : Env) :
    checkedDivCount (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret = 0 ∧
      divOpCount (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret ≤ 1 ∧
      guardBranchCount (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y d)).ret = 0 ∧
      execBlockCheckCost env (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y d)) = 0 := by
  sorry

/-- Parametric Clobbered Divisor Trap Preservation: Under `.nonZero (.var x)`, across `d := x; x := 0`,
    dividing by the clobbered variable `x` must still safely return `.trap` (never `.ub`). -/
theorem optimizeBlock_clobber_trap_param (x d : VarId) (num y : PureExpr)
    (env : Env) (hx : evalGuard env (.nonZero (.var x)) = true) :
    evalBlock env (optimizeBlock (.nonZero (.var x)) (mkClobberBlock x d num y x)) = .trap := by
  sorry

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
  sorry

/-- Parametric Dead-Branch Pruning & Guarded Cancellation: Under `.nonZero p` with `n ≠ 0`,
    `optimizeBlock` prunes the unreachable zero-assignment branch in `mkDeadBranchBlock p d n y`,
    propagates `d ≠ 0`, cancels `(y * d) / d`, and achieves `0` total block check cost. -/
theorem optimizeBlock_dead_branch_elim_param (p : PureExpr) (d : VarId)
    (n : Int) (hn : n ≠ 0) (y : PureExpr) (env : Env) :
    checkedDivCount (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)).ret = 0 ∧
      divOpCount (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)).ret = 0 ∧
      execBlockCheckCost env (optimizeBlock (.nonZero p) (mkDeadBranchBlock p d n y)) = 0 := by
  sorry

/-! ## Milestone 3: Fuel-Indexed Imperative Loops, Inductive Strengthening & Preheader Guard Hoisting -/

/-- Computable conservative universal-quantification pullback of a `GuardIR` across a write to `v`. -/
def havocGuardIR (v : VarId) (g : GuardIR) : GuardIR :=
  sorry

/-- Computable bounded backward inductive-invariant strengthening across `(accVar, latch)` for `target`. -/
def strengthenLoopInvariantIR (accVar : VarId) (latch : Stmt) (target : GuardIR) : Option GuardIR :=
  sorry

/-- Computable preheader loop-hoisted guard synthesis across `init` from `ctx` to `inv`. -/
def hoistLoopGuardIR (init : Stmt) (ctx inv : GuardIR) : GuardIR :=
  sorry

/-- Computable context-sensitive loop optimizer performing inductive invariant strengthening,
    preheader guard hoisting / loop versioning, and loop-body check elimination. -/
def optimizeLoop (ctx : GuardIR) (prog : LoopProg) : LoopProg :=
  sorry

/-- Iterated State-Transfer Pullback Characterization: The `n`-fold `CFGTransfer.iterate` pullback
    of `stateTransfer step` at `Q` and `s` holds if and only if `Q (step^[n] s)` holds. -/
theorem stateTransfer_iterate_pullback_iff (step : S → S) (Q : S → Prop) (n : ℕ) (s : S) :
    ((stateTransfer step).iterate n).pullback Q s ↔ Q (step^[n] s) := by
  sorry

/-- Soundness of `havocGuardIR`: Denotation implies the semantic universal pullback `(havocTransfer v).pullback`. -/
theorem havocGuardIR_sound (v : VarId) (g : GuardIR) :
    denoteGuard (havocGuardIR v g) ≤ (havocTransfer v).pullback (denoteGuard g) := by
  sorry

/-- Exactness of `havocGuardIR` on Non-Mentioning Guards: When `guardMentionsVar v g = false`,
    `havocGuardIR v g` denotes the exact semantic pullback `(havocTransfer v).pullback (denoteGuard g)`. -/
theorem havocGuardIR_exact_of_nonMention (v : VarId) (g : GuardIR)
    (h : guardMentionsVar v g = false) :
    denoteGuard (havocGuardIR v g) = (havocTransfer v).pullback (denoteGuard g) := by
  sorry

/-- Categorical Inductive Soundness of `strengthenLoopInvariantIR`: Any synthesized `some inv`
    satisfies `IsInductiveFor (loopStepTransfer accVar latch) (denoteGuard inv) (denoteGuard target)`. -/
theorem strengthenLoopInvariantIR_inductive (accVar : VarId) (latch : Stmt)
    (target inv : GuardIR) (h : strengthenLoopInvariantIR accVar latch target = some inv) :
    IsInductiveFor (loopStepTransfer accVar latch) (denoteGuard inv) (denoteGuard target) := by
  sorry

/-- Stationary Divisor Strengthening Completeness: When `d` is distinct from `accVar` and `i`,
    `strengthenLoopInvariantIR` succeeds on `i := i - 1` for `.nonZero (.var d)`. -/
theorem strengthenLoopInvariantIR_stationary (accVar d i : VarId)
    (hda : d ≠ accVar) (hdi : d ≠ i) :
    ∃ inv, strengthenLoopInvariantIR accVar (.assign i (.sub (.var i) (.lit 1))) (.nonZero (.var d)) = some inv := by
  sorry

/-- Two-Stage Pipeline Divisor Strengthening Completeness: Across `d := nextD; i := i - 1`,
    `strengthenLoopInvariantIR` strengthens `.nonZero (.var d)` to a genuine inductive invariant `some inv`. -/
theorem strengthenLoopInvariantIR_pipeline (accVar d nextD i : VarId)
    (hda : d ≠ accVar) (hna : nextD ≠ accVar)
    (hdi : d ≠ i) (hni : nextD ≠ i) (hdn : d ≠ nextD) :
    ∃ inv,
      strengthenLoopInvariantIR accVar
        (.seq (.assign d (.var nextD)) (.assign i (.sub (.var i) (.lit 1))))
        (.nonZero (.var d)) = some inv := by
  sorry

/-- Categorical Realization of `hoistLoopGuardIR`: Denotation commutes with abstract `hoistLoopGuard`
    along `stateTransfer (execStmt init)`. -/
theorem hoistLoopGuardIR_denote (init : Stmt) (ctx inv : GuardIR) :
    denoteGuard (hoistLoopGuardIR init ctx inv) =
      hoistLoopGuard (stateTransfer (execStmt init)) (denoteGuard ctx) (denoteGuard inv) := by
  sorry

/-- Arbitrary-Iteration Target Soundness of `hoistLoopGuardIR`: Given an inductive invariant `inv`
    for `target` under `loopStepTransfer accVar latch`, conjoining `ctx` with `hoistLoopGuardIR init ctx inv`
    establishes `target` after `init` and `n` abstract loop iterations for every `n : ℕ`. -/
theorem hoistLoopGuardIR_iterate_target (init : Stmt) (accVar : VarId) (latch : Stmt)
    (ctx target inv : GuardIR)
    (hInd : IsInductiveFor (loopStepTransfer accVar latch) (denoteGuard inv) (denoteGuard target))
    (n : ℕ) :
    (((stateTransfer (execStmt init)).comp ((loopStepTransfer accVar latch).iterate n)).post
      (denoteGuard ctx ⊓ denoteGuard (hoistLoopGuardIR init ctx inv))) ≤ denoteGuard target := by
  sorry

/-- Fuel-Indexed Stage-Guarded Soundness of `optimizeLoop` via `GuardedEquiv` and `liftEval (evalLoop fuel)`. -/
theorem optimizeLoop_guardedEquiv (fuel : Nat) (ctx : GuardIR) (prog : LoopProg) :
    GuardedEquiv (liftEval (evalLoop fuel)) (denoteGuard ctx) (optimizeLoop ctx prog) prog := by
  sorry

/-- Fuel-Indexed Concrete Operational Soundness of `optimizeLoop`: For every `fuel` and `env`
    satisfying `ctx`, `optimizeLoop ctx prog` evaluates to the exact same `LoopOutcome` as `prog`. -/
theorem optimizeLoop_sound (fuel : Nat) (ctx : GuardIR) (prog : LoopProg) (env : Env) :
    evalGuard env ctx = true → evalLoop fuel env (optimizeLoop ctx prog) = evalLoop fuel env prog := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- Parametric Non-Invariant Decrementing-Divisor Trap Preservation: Even when `init` sets `d := 1`
    (`x = 1 ≠ 0`), `d := d - 1` violates loop invariance on iteration 2 (`i = 2`), so `optimizeLoop`
    must preserve `.done .trap` (rejecting naive entry-only check elimination). -/
theorem optimizeLoop_decrement_div_trap_param (x d i acc : VarId)
    (hda : d ≠ acc) (hia : i ≠ acc) (hid : i ≠ d)
    (num : PureExpr) (env : Env) (hx : env x = 1) (hi : env i = 2) :
    evalLoop 3 env (optimizeLoop (.nonZero (.var x)) (.whileLoop (mkDecrementDivisorLoop x d i acc num))) =
      .done .trap := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- Syntactic Transparency of `havocGuardIR` on Non-Mentioning Guards:
    When `guardMentionsVar v g = false`, `havocGuardIR v g` returns `g` unchanged without
    injecting unnormalized wrapper syntax. -/
theorem havocGuardIR_nonMention_eq (v : VarId) (g : GuardIR)
    (h : guardMentionsVar v g = false) :
    havocGuardIR v g = g := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end CatSem
