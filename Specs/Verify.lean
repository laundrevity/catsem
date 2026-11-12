import Specs.Defs
import Proofs.Submission
import Lean.Elab.Command
import Lean.Util.CollectAxioms

namespace CatSem.Verify

open Lean Elab Command in
/-- Fail-closed kernel axiom allowlist check: inspects the transitive kernel axioms of `id`
    via `Lean.collectAxioms` and throws an elaboration error if any axiom outside
    `{propext, Quot.sound}` is present (rejecting `sorryAx`, `Classical.choice`,
    `Lean.ofReduceBool`, `Lean.trustCompiler`, and user-declared axioms). -/
elab "#verify_allowed_axioms " id:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  unless env.contains declName do
    throwError m!"❌ Axiom audit failed: unknown constant '{declName}'"
  let axioms ← liftCoreM <| Lean.collectAxioms declName
  let disallowed := axioms.filter fun ax =>
    ax != ``propext && ax != ``Quot.sound
  if !disallowed.isEmpty then
    throwError m!"❌ Axiom audit failed for '{declName}': disallowed axioms {disallowed.toList} (permitted: [propext, Quot.sound])"

-- In-kernel transitive axiom audit on all Trusted Computing Base definitions (Specs/Defs.lean)
#verify_allowed_axioms CatSem.synthesizeGuard
#verify_allowed_axioms CatSem.synthesizeEdgeGuard
#verify_allowed_axioms CatSem.CFGTransfer.id
#verify_allowed_axioms CatSem.CFGTransfer.comp
#verify_allowed_axioms CatSem.IsLoopInvariant
#verify_allowed_axioms CatSem.synthesizeLoopStepGuard
#verify_allowed_axioms CatSem.IsInductiveFor
#verify_allowed_axioms CatSem.hoistLoopGuard
#verify_allowed_axioms CatSem.CFGTransfer.iterate
#verify_allowed_axioms CatSem.Forces
#verify_allowed_axioms CatSem.ForcesAfter
#verify_allowed_axioms CatSem.GuardedEquiv
#verify_allowed_axioms CatSem.pullbackEval
#verify_allowed_axioms CatSem.CompatibleOp2
#verify_allowed_axioms CatSem.stateTransfer
#verify_allowed_axioms CatSem.evalPure
#verify_allowed_axioms CatSem.evalGuard
#verify_allowed_axioms CatSem.denoteGuard
#verify_allowed_axioms CatSem.bindOutcome2
#verify_allowed_axioms CatSem.evalExpr
#verify_allowed_axioms CatSem.liftEval
#verify_allowed_axioms CatSem.liftBinarySem
#verify_allowed_axioms CatSem.checkedDivCount
#verify_allowed_axioms CatSem.divOpCount
#verify_allowed_axioms CatSem.guardBranchCount
#verify_allowed_axioms CatSem.guardEvalCost
#verify_allowed_axioms CatSem.execCheckCost
#verify_allowed_axioms CatSem.mkCancelExpr
#verify_allowed_axioms CatSem.mkDualDivExpr
#verify_allowed_axioms CatSem.m1CancelExpr
#verify_allowed_axioms CatSem.m1BenchExpr
#verify_allowed_axioms CatSem.updateEnv
#verify_allowed_axioms CatSem.execStmt
#verify_allowed_axioms CatSem.evalBlock
#verify_allowed_axioms CatSem.stmtGuardCost
#verify_allowed_axioms CatSem.execBlockCheckCost
#verify_allowed_axioms CatSem.mkClobberBlock
#verify_allowed_axioms CatSem.mkDiamondSafeBlock
#verify_allowed_axioms CatSem.mkDeadBranchBlock
#verify_allowed_axioms CatSem.pureMentionsVar
#verify_allowed_axioms CatSem.guardMentionsVar
#verify_allowed_axioms CatSem.havocTransfer
#verify_allowed_axioms CatSem.loopStepTransfer
#verify_allowed_axioms CatSem.runWhileSteps
#verify_allowed_axioms CatSem.evalLoop
#verify_allowed_axioms CatSem.loopCheckedDivCount
#verify_allowed_axioms CatSem.loopDivOpCount
#verify_allowed_axioms CatSem.loopBranchCount
#verify_allowed_axioms CatSem.runWhileCheckCost
#verify_allowed_axioms CatSem.execLoopCheckCost
#verify_allowed_axioms CatSem.mkCountedDivLoop
#verify_allowed_axioms CatSem.mkPipelineDivLoop
#verify_allowed_axioms CatSem.mkDecrementDivisorLoop
#verify_allowed_axioms CatSem.stmtWritesVar
#verify_allowed_axioms CatSem.mkFrameStmtDivLoop
#verify_allowed_axioms CatSem.mkSwapDivLoop
#verify_allowed_axioms CatSem.mkPipeline3DivLoop
#verify_allowed_axioms CatSem.mkBranchDivLoop

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

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CatSem.CFGTransfer α β) (a : α) (q : β) :
    CatSem.ForcesAfter T a q ↔ CatSem.Forces a (T.pullback q) :=
  CatSem.forcesAfter_iff_pullback T a q

example {α : Type*} [HeytingAlgebra α] (a p g : α) :
    CatSem.Forces (a ⊓ g) p ↔ CatSem.Forces g (CatSem.synthesizeGuard a p) :=
  CatSem.forces_guard_iff a p g

example {α : Type*} [HeytingAlgebra α] (a p₁ p₂ g : α) :
    CatSem.Forces (a ⊓ g) (p₁ ⊓ p₂) ↔
      CatSem.Forces g (CatSem.synthesizeGuard a p₁ ⊓ CatSem.synthesizeGuard a p₂) :=
  CatSem.forces_rewrite_chain_iff a p₁ p₂ g

example {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CatSem.CFGTransfer α β) (L : CatSem.CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : CatSem.IsInductiveFor L inv target) :
    ∀ n : ℕ, CatSem.ForcesAfter (E.comp (L.iterate n)) (a₀ ⊓ CatSem.hoistLoopGuard E a₀ inv) target :=
  CatSem.forcesAfter_hoistLoopGuard_iterate E L a₀ inv target h

example {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (t : Term) :
    CatSem.GuardedEquiv eval ⊤ t t :=
  CatSem.guardedEquiv_refl eval t

example {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p : α) (t₁ t₂ : Term) :
    CatSem.GuardedEquiv eval p t₁ t₂ → CatSem.GuardedEquiv eval p t₂ t₁ :=
  CatSem.guardedEquiv_symm eval p t₁ t₂

example {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : CatSem.GuardedEquiv eval p₁ t₁ t₂) (h₂ : CatSem.GuardedEquiv eval p₂ t₂ t₃) :
    CatSem.GuardedEquiv eval (p₁ ⊓ p₂) t₁ t₃ :=
  CatSem.guardedEquiv_trans_inf eval p₁ p₂ t₁ t₂ t₃ h₁ h₂

example {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (a p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : CatSem.GuardedEquiv eval p₁ t₁ t₂) (h₂ : CatSem.GuardedEquiv eval p₂ t₂ t₃) :
    eval (a ⊓ (CatSem.synthesizeGuard a p₁ ⊓ CatSem.synthesizeGuard a p₂)) t₁ =
      eval (a ⊓ (CatSem.synthesizeGuard a p₁ ⊓ CatSem.synthesizeGuard a p₂)) t₃ :=
  CatSem.guardedEquiv_synthesize_chain eval a p₁ p₂ t₁ t₂ t₃ h₁ h₂

example {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p q : α) (t₁ t₂ : Term)
    (hpq : CatSem.Forces p q) (h : CatSem.GuardedEquiv eval q t₁ t₂) :
    CatSem.GuardedEquiv eval p t₁ t₂ :=
  CatSem.guardedEquiv_weaken eval p q t₁ t₂ hpq h

example {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CatSem.CFGTransfer α β) (evalβ : β → Term → Val)
    (q : β) (t₁ t₂ : Term) (h : CatSem.GuardedEquiv evalβ q t₁ t₂) :
    CatSem.GuardedEquiv (CatSem.pullbackEval T evalβ) (T.pullback q) t₁ t₂ :=
  CatSem.guardedEquiv_pullback T evalβ q t₁ t₂ h

example {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CatSem.CFGTransfer α β) (evalβ : β → Term → Val)
    (a : α) (q : β) (t₁ t₂ : Term) (h : CatSem.GuardedEquiv evalβ q t₁ t₂) :
    evalβ (T.post (a ⊓ CatSem.synthesizeEdgeGuard T a q)) t₁ =
      evalβ (T.post (a ⊓ CatSem.synthesizeEdgeGuard T a q)) t₂ :=
  CatSem.guardedEquiv_edge_synthesize T evalβ a q t₁ t₂ h

example {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CatSem.CFGTransfer α β) (L : CatSem.CFGTransfer β β)
    (evalβ : β → Term → Val) (a₀ : α) (inv q : β) (t₁ t₂ : Term)
    (hind : CatSem.IsInductiveFor L inv q) (heq : CatSem.GuardedEquiv evalβ q t₁ t₂) :
    ∀ n : ℕ,
      evalβ ((E.comp (L.iterate n)).post (a₀ ⊓ CatSem.hoistLoopGuard E a₀ inv)) t₁ =
        evalβ ((E.comp (L.iterate n)).post (a₀ ⊓ CatSem.hoistLoopGuard E a₀ inv)) t₂ :=
  CatSem.guardedEquiv_hoistLoopGuard_iterate E L evalβ a₀ inv q t₁ t₂ hind heq

example {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (op : Term → Term → Term) (semOp : α → Val → Val → Val)
    (p₁ p₂ : α) (t₁ u₁ t₂ u₂ : Term)
    (hcompat : CatSem.CompatibleOp2 eval op semOp)
    (h₁ : CatSem.GuardedEquiv eval p₁ t₁ u₁) (h₂ : CatSem.GuardedEquiv eval p₂ t₂ u₂) :
    CatSem.GuardedEquiv eval (p₁ ⊓ p₂) (op t₁ t₂) (op u₁ u₂) :=
  CatSem.guardedEquiv_congr2 eval op semOp p₁ p₂ t₁ u₁ t₂ u₂ hcompat h₁ h₂

example {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (op : Term → Term → Term) (semOp : α → Val → Val → Val)
    (a p₁ p₂ : α) (t₁ u₁ t₂ u₂ : Term)
    (hcompat : CatSem.CompatibleOp2 eval op semOp)
    (h₁ : CatSem.GuardedEquiv eval p₁ t₁ u₁) (h₂ : CatSem.GuardedEquiv eval p₂ t₂ u₂) :
    eval (a ⊓ (CatSem.synthesizeGuard a p₁ ⊓ CatSem.synthesizeGuard a p₂)) (op t₁ t₂) =
      eval (a ⊓ (CatSem.synthesizeGuard a p₁ ⊓ CatSem.synthesizeGuard a p₂)) (op u₁ u₂) :=
  CatSem.guardedEquiv_congr2_synthesize eval op semOp a p₁ p₂ t₁ u₁ t₂ u₂ hcompat h₁ h₂

example {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CatSem.CFGTransfer α β) (evalβ : β → Term → Val)
    (q₁ q₂ : β) (t₁ t₂ : Term) :
    CatSem.GuardedEquiv (CatSem.pullbackEval T evalβ) (T.pullback (q₁ ⊓ q₂)) t₁ t₂ ↔
      CatSem.GuardedEquiv (CatSem.pullbackEval T evalβ) (T.pullback q₁ ⊓ T.pullback q₂) t₁ t₂ :=
  CatSem.guardedEquiv_pullback_inf_commute T evalβ q₁ q₂ t₁ t₂

example {α γ Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra γ]
    (P₁ P₂ : CatSem.CFGTransfer α γ) (evalγ : γ → Term → Val)
    (a : α) (c : γ) (t₁ t₂ : Term) (h : CatSem.GuardedEquiv evalγ c t₁ t₂) :
    let g := CatSem.synthesizeEdgeGuard P₁ a c ⊓ CatSem.synthesizeEdgeGuard P₂ a c
    evalγ (P₁.post (a ⊓ g)) t₁ = evalγ (P₁.post (a ⊓ g)) t₂ ∧
      evalγ (P₂.post (a ⊓ g)) t₁ = evalγ (P₂.post (a ⊓ g)) t₂ :=
  CatSem.guardedEquiv_diamond P₁ P₂ evalγ a c t₁ t₂ h

example {S₁ S₂ : Type*} (step : S₁ → S₂) (Q : S₂ → Prop) (s₁ : S₁) :
    (CatSem.stateTransfer step).pullback Q s₁ ↔ Q (step s₁) :=
  CatSem.stateTransfer_pullback_apply step Q s₁

example {S₁ S₂ : Type*} (step : S₁ → S₂) (P : S₁ → Prop) (Q : S₂ → Prop) (s₁ : S₁) :
    CatSem.synthesizeEdgeGuard (CatSem.stateTransfer step) P Q s₁ ↔ (P s₁ → Q (step s₁)) :=
  CatSem.stateTransfer_synthesizeEdgeGuard_apply step P Q s₁

example {S : Type*} (step : S → S) (inv : S → Prop) :
    CatSem.IsLoopInvariant (CatSem.stateTransfer step) inv ↔ ∀ s, inv s → inv (step s) :=
  CatSem.stateTransfer_isLoopInvariant_iff step inv

example {S₀ S Term Val : Type*} (init : S₀ → S) (step : S → S)
    (eval : (S → Prop) → Term → Val) (a₀ : S₀ → Prop) (inv q : S → Prop) (t₁ t₂ : Term)
    (hind : CatSem.IsInductiveFor (CatSem.stateTransfer step) inv q)
    (heq : CatSem.GuardedEquiv eval q t₁ t₂) :
    ∀ n : ℕ,
      eval (((CatSem.stateTransfer init).comp ((CatSem.stateTransfer step).iterate n)).post
        (a₀ ⊓ CatSem.hoistLoopGuard (CatSem.stateTransfer init) a₀ inv)) t₁ =
      eval (((CatSem.stateTransfer init).comp ((CatSem.stateTransfer step).iterate n)).post
        (a₀ ⊓ CatSem.hoistLoopGuard (CatSem.stateTransfer init) a₀ inv)) t₂ :=
  CatSem.stateTransfer_hoistLoopGuard_iterate_equiv init step eval a₀ inv q t₁ t₂ hind heq

-- Milestone 1 computability & signature checks (rejects `noncomputable` implementations)
def _computable_synthesizeGuardIR : GuardIR → GuardIR → GuardIR :=
  CatSem.synthesizeGuardIR

def _computable_optimizeExpr : GuardIR → Expr → Expr :=
  CatSem.optimizeExpr

example {S Term Out : Type*} (run : S → Term → Out) (P : S → Prop) (t₁ t₂ : Term) :
    CatSem.GuardedEquiv (CatSem.liftEval run) P t₁ t₂ ↔ ∀ s, P s → run s t₁ = run s t₂ :=
  CatSem.liftEval_guardedEquiv_iff run P t₁ t₂

example :
    CatSem.CompatibleOp2 (CatSem.liftEval CatSem.evalExpr) CatSem.Expr.add
      (CatSem.liftBinarySem (fun x y => .val (x + y))) :=
  CatSem.exprAdd_compatibleOp2

example :
    CatSem.CompatibleOp2 (CatSem.liftEval CatSem.evalExpr) CatSem.Expr.checkedDiv
      (CatSem.liftBinarySem (fun x y => if y = 0 then .trap else .val (x / y))) :=
  CatSem.exprCheckedDiv_compatibleOp2

example (a b : CatSem.GuardIR) :
    CatSem.denoteGuard (CatSem.synthesizeGuardIR a b) =
      CatSem.synthesizeGuard (CatSem.denoteGuard a) (CatSem.denoteGuard b) :=
  CatSem.synthesizeGuardIR_denote a b

example (a b : CatSem.GuardIR) (g : CatSem.Env → Prop) :
    CatSem.denoteGuard a ⊓ g ≤ CatSem.denoteGuard b ↔
      g ≤ CatSem.denoteGuard (CatSem.synthesizeGuardIR a b) :=
  CatSem.synthesizeGuardIR_universal a b g

example (p : CatSem.PureExpr) :
    CatSem.synthesizeGuardIR (.nonZero p) (.nonZero p) = .top :=
  CatSem.synthesizeGuardIR_discharge_self p

example (ctx : CatSem.GuardIR) (e : CatSem.Expr) :
    CatSem.GuardedEquiv (CatSem.liftEval CatSem.evalExpr) (CatSem.denoteGuard ctx)
      (CatSem.optimizeExpr ctx e) e :=
  CatSem.optimizeExpr_guardedEquiv ctx e

example (ctx : CatSem.GuardIR) (e : CatSem.Expr) (env : CatSem.Env) :
    CatSem.evalGuard env ctx = true →
      CatSem.evalExpr env (CatSem.optimizeExpr ctx e) = CatSem.evalExpr env e :=
  CatSem.optimizeExpr_sound ctx e env

example (env : CatSem.Env) :
    CatSem.checkedDivCount (CatSem.optimizeExpr (.nonZero (.var 0)) CatSem.m1BenchExpr) = 0 ∧
      CatSem.guardBranchCount (CatSem.optimizeExpr (.nonZero (.var 0)) CatSem.m1BenchExpr) = 0 ∧
      CatSem.execCheckCost env (CatSem.optimizeExpr (.nonZero (.var 0)) CatSem.m1BenchExpr) = 0 :=
  CatSem.optimizeExpr_known_ctx_elim env

example :
    CatSem.divOpCount (CatSem.optimizeExpr (.nonZero (.var 0)) CatSem.m1CancelExpr) = 0 :=
  CatSem.optimizeExpr_cancel_div

example (env : CatSem.Env) (h : env 0 ≠ 0) :
    CatSem.execCheckCost env (CatSem.optimizeExpr .top CatSem.m1BenchExpr) ≤ 1 ∧
      CatSem.execCheckCost env CatSem.m1BenchExpr = 2 :=
  CatSem.optimizeExpr_unknown_ctx_dedup env h

example (env : CatSem.Env) (h : env 0 = 0) :
    CatSem.evalExpr env (CatSem.optimizeExpr .top CatSem.m1BenchExpr) = .trap :=
  CatSem.optimizeExpr_zero_div_trap env h

example (a : CatSem.GuardIR) :
    CatSem.synthesizeGuardIR a .top = .top :=
  CatSem.synthesizeGuardIR_top_right a

example (b : CatSem.GuardIR) :
    CatSem.synthesizeGuardIR .bot b = .top :=
  CatSem.synthesizeGuardIR_bot_left b

example (p : CatSem.PureExpr) :
    CatSem.synthesizeGuardIR .top (.nonZero p) = .nonZero p :=
  CatSem.synthesizeGuardIR_top_left_nonZero p

example (p : CatSem.PureExpr) (rest : CatSem.GuardIR) :
    CatSem.synthesizeGuardIR (.conj (.nonZero p) rest) (.nonZero p) = .top :=
  CatSem.synthesizeGuardIR_discharge_conj_left p rest

example (rest : CatSem.GuardIR) (p : CatSem.PureExpr) :
    CatSem.synthesizeGuardIR (.conj rest (.nonZero p)) (.nonZero p) = .top :=
  CatSem.synthesizeGuardIR_discharge_conj_right rest p

example (p : CatSem.PureExpr) :
    CatSem.synthesizeGuardIR .top (.conj (.nonZero p) (.nonZero p)) = .nonZero p :=
  CatSem.synthesizeGuardIR_dedup_conj p

example (num d : CatSem.PureExpr) (extra : CatSem.GuardIR) (env : CatSem.Env) :
    CatSem.checkedDivCount (CatSem.optimizeExpr (.nonZero d) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      CatSem.checkedDivCount (CatSem.optimizeExpr (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      CatSem.checkedDivCount (CatSem.optimizeExpr (.conj extra (.nonZero d)) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      CatSem.guardBranchCount (CatSem.optimizeExpr (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
      CatSem.execCheckCost env (CatSem.optimizeExpr (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 :=
  CatSem.optimizeExpr_elim_checkedDiv_param num d extra env

example (x d : CatSem.PureExpr) :
    CatSem.divOpCount (CatSem.optimizeExpr (.nonZero d) (CatSem.mkCancelExpr x d)) = 0 ∧
      CatSem.divOpCount (CatSem.optimizeExpr (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d))) = 0 :=
  CatSem.optimizeExpr_cancel_div_param x d

example (d : CatSem.PureExpr) (e₁ e₂ : CatSem.Expr)
    (h₁ : CatSem.checkedDivCount (CatSem.optimizeExpr (.nonZero d) e₁) = 0 ∧
          CatSem.guardBranchCount (CatSem.optimizeExpr (.nonZero d) e₁) = 0)
    (h₂ : CatSem.checkedDivCount (CatSem.optimizeExpr (.nonZero d) e₂) = 0 ∧
          CatSem.guardBranchCount (CatSem.optimizeExpr (.nonZero d) e₂) = 0) :
    CatSem.checkedDivCount (CatSem.optimizeExpr (.nonZero d) (.add e₁ e₂)) = 0 ∧
      CatSem.checkedDivCount (CatSem.optimizeExpr (.nonZero d) (.sub e₁ e₂)) = 0 ∧
      CatSem.checkedDivCount (CatSem.optimizeExpr (.nonZero d) (.mul e₁ e₂)) = 0 :=
  CatSem.optimizeExpr_compositional_binary d e₁ e₂ h₁ h₂

example (x y d : CatSem.PureExpr) (env : CatSem.Env) :
    CatSem.checkedDivCount (CatSem.optimizeExpr (.nonZero d) (CatSem.mkDualDivExpr x y d)) = 0 ∧
      CatSem.guardBranchCount (CatSem.optimizeExpr (.nonZero d) (CatSem.mkDualDivExpr x y d)) = 0 ∧
      CatSem.execCheckCost env (CatSem.optimizeExpr (.nonZero d) (CatSem.mkDualDivExpr x y d)) = 0 :=
  CatSem.optimizeExpr_known_ctx_elim_param x y d env

example (x y d : CatSem.PureExpr) (env : CatSem.Env) (h : CatSem.evalPure env d ≠ 0) :
    CatSem.execCheckCost env (CatSem.optimizeExpr .top (CatSem.mkDualDivExpr x y d)) ≤ 1 ∧
      CatSem.execCheckCost env (CatSem.mkDualDivExpr x y d) = 2 :=
  CatSem.optimizeExpr_unknown_ctx_dedup_param x y d env h

example (x y d : CatSem.PureExpr) (env : CatSem.Env) (h : CatSem.evalPure env d = 0) :
    CatSem.evalExpr env (CatSem.optimizeExpr .top (CatSem.mkDualDivExpr x y d)) = .trap :=
  CatSem.optimizeExpr_zero_div_trap_param x y d env h

-- Milestone 2 computability & signature checks (rejects `noncomputable` implementations)
def _computable_pullbackGuardIR : Stmt → GuardIR → GuardIR :=
  CatSem.pullbackGuardIR

def _computable_synthesizeStmtGuardIR : Stmt → GuardIR → GuardIR → GuardIR :=
  CatSem.synthesizeStmtGuardIR

def _computable_optimizeBlock : GuardIR → BlockProg → BlockProg :=
  CatSem.optimizeBlock

example {S₁ S₂ Term Out : Type*}
    (step : S₁ → S₂) (run : S₂ → Term → Out) (P : S₁ → Prop) (t₁ t₂ : Term) :
    CatSem.GuardedEquiv (CatSem.pullbackEval (CatSem.stateTransfer step) (CatSem.liftEval run)) P t₁ t₂ ↔
      ∀ s, P s → run (step s) t₁ = run (step s) t₂ :=
  CatSem.pullbackEval_stateTransfer_liftEval_iff step run P t₁ t₂

example (s : CatSem.Stmt) (g : CatSem.GuardIR) :
    CatSem.denoteGuard (CatSem.pullbackGuardIR s g) =
      (CatSem.stateTransfer (CatSem.execStmt s)).pullback (CatSem.denoteGuard g) :=
  CatSem.pullbackGuardIR_denote s g

example (s₁ s₂ : CatSem.Stmt) (g : CatSem.GuardIR) :
    CatSem.denoteGuard (CatSem.pullbackGuardIR (.seq s₁ s₂) g) =
      ((CatSem.stateTransfer (CatSem.execStmt s₁)).comp
        (CatSem.stateTransfer (CatSem.execStmt s₂))).pullback (CatSem.denoteGuard g) :=
  CatSem.pullbackGuardIR_seq s₁ s₂ g

example (s : CatSem.Stmt) (a b : CatSem.GuardIR) :
    CatSem.denoteGuard (CatSem.synthesizeStmtGuardIR s a b) =
      CatSem.synthesizeEdgeGuard (CatSem.stateTransfer (CatSem.execStmt s))
        (CatSem.denoteGuard a) (CatSem.denoteGuard b) :=
  CatSem.synthesizeStmtGuardIR_denote s a b

example (s : CatSem.Stmt) (a b : CatSem.GuardIR) (g : CatSem.Env → Prop) :
    CatSem.ForcesAfter (CatSem.stateTransfer (CatSem.execStmt s))
      (CatSem.denoteGuard a ⊓ g) (CatSem.denoteGuard b) ↔
      g ≤ CatSem.denoteGuard (CatSem.synthesizeStmtGuardIR s a b) :=
  CatSem.synthesizeStmtGuardIR_universal s a b g

example (s₁ s₂ : CatSem.Stmt) (ctx req : CatSem.GuardIR)
    (e₁ e₂ : CatSem.Expr)
    (h : CatSem.GuardedEquiv (CatSem.liftEval CatSem.evalExpr) (CatSem.denoteGuard req) e₁ e₂) :
    let g := CatSem.GuardIR.conj
      (CatSem.synthesizeStmtGuardIR s₁ ctx req)
      (CatSem.synthesizeStmtGuardIR s₂ ctx req)
    ∀ env : CatSem.Env, CatSem.evalGuard env ctx = true → CatSem.evalGuard env g = true →
      CatSem.evalExpr (CatSem.execStmt s₁ env) e₁ = CatSem.evalExpr (CatSem.execStmt s₁ env) e₂ ∧
        CatSem.evalExpr (CatSem.execStmt s₂ env) e₁ = CatSem.evalExpr (CatSem.execStmt s₂ env) e₂ :=
  CatSem.synthesizeStmtGuardIR_diamond_sound s₁ s₂ ctx req e₁ e₂ h

example (n : Int) (hn : n ≠ 0) :
    CatSem.synthesizeStmtGuardIR .skip .top (.nonZero (.lit n)) = .top :=
  CatSem.synthesizeStmtGuardIR_lit_nonZero n hn

example (v : CatSem.VarId) (rhs : CatSem.PureExpr) :
    CatSem.synthesizeStmtGuardIR (.assign v rhs) (.nonZero rhs) (.nonZero (.var v)) = .top :=
  CatSem.synthesizeStmtGuardIR_assign_self v rhs

example (x d : CatSem.VarId) (n : Int) (hn : n ≠ 0) :
    CatSem.synthesizeStmtGuardIR
      (.ite (.eq (.var x) (.lit 0)) (.assign d (.lit n)) (.assign d (.var x)))
      .top (.nonZero (.var d)) = .top :=
  CatSem.synthesizeStmtGuardIR_diamond_safe x d n hn

example (ctx : CatSem.GuardIR) (prog : CatSem.BlockProg) :
    CatSem.GuardedEquiv (CatSem.liftEval CatSem.evalBlock) (CatSem.denoteGuard ctx)
      (CatSem.optimizeBlock ctx prog) prog :=
  CatSem.optimizeBlock_guardedEquiv ctx prog

example (ctx : CatSem.GuardIR) (prog : CatSem.BlockProg) (env : CatSem.Env) :
    CatSem.evalGuard env ctx = true →
      CatSem.evalBlock env (CatSem.optimizeBlock ctx prog) = CatSem.evalBlock env prog :=
  CatSem.optimizeBlock_sound ctx prog env

example (num y : CatSem.PureExpr) (n : Int) (hn : n ≠ 0) (env : CatSem.Env) :
    let prog : CatSem.BlockProg := { body := .skip, ret := CatSem.mkDualDivExpr num y (.lit n) }
    CatSem.checkedDivCount (CatSem.optimizeBlock .top prog).ret = 0 ∧
      CatSem.divOpCount (CatSem.optimizeBlock .top prog).ret ≤ 1 ∧
      CatSem.guardBranchCount (CatSem.optimizeBlock .top prog).ret = 0 ∧
      CatSem.execBlockCheckCost env (CatSem.optimizeBlock .top prog) = 0 :=
  CatSem.optimizeBlock_literal_div_elim_param num y n hn env

example (x d : CatSem.VarId) (hxd : d ≠ x) (num y : CatSem.PureExpr) (env : CatSem.Env) :
    CatSem.checkedDivCount (CatSem.optimizeBlock (.nonZero (.var x)) (CatSem.mkClobberBlock x d num y d)).ret = 0 ∧
      CatSem.divOpCount (CatSem.optimizeBlock (.nonZero (.var x)) (CatSem.mkClobberBlock x d num y d)).ret ≤ 1 ∧
      CatSem.guardBranchCount (CatSem.optimizeBlock (.nonZero (.var x)) (CatSem.mkClobberBlock x d num y d)).ret = 0 ∧
      CatSem.execBlockCheckCost env (CatSem.optimizeBlock (.nonZero (.var x)) (CatSem.mkClobberBlock x d num y d)) = 0 :=
  CatSem.optimizeBlock_seq_clobber_elim_param x d hxd num y env

example (x d : CatSem.VarId) (num y : CatSem.PureExpr) (env : CatSem.Env)
    (hx : CatSem.evalGuard env (.nonZero (.var x)) = true) :
    CatSem.evalBlock env (CatSem.optimizeBlock (.nonZero (.var x)) (CatSem.mkClobberBlock x d num y x)) = .trap :=
  CatSem.optimizeBlock_clobber_trap_param x d num y env hx

example (x d : CatSem.VarId) (n : Int) (hn : n ≠ 0) (num y : CatSem.PureExpr) (env : CatSem.Env) :
    CatSem.checkedDivCount (CatSem.optimizeBlock .top (CatSem.mkDiamondSafeBlock x d n num y)).ret = 0 ∧
      CatSem.divOpCount (CatSem.optimizeBlock .top (CatSem.mkDiamondSafeBlock x d n num y)).ret ≤ 1 ∧
      CatSem.guardBranchCount (CatSem.optimizeBlock .top (CatSem.mkDiamondSafeBlock x d n num y)).ret = 0 ∧
      CatSem.execBlockCheckCost env (CatSem.optimizeBlock .top (CatSem.mkDiamondSafeBlock x d n num y)) ≤ 1 ∧
      CatSem.execBlockCheckCost env (CatSem.mkDiamondSafeBlock x d n num y) = 3 :=
  CatSem.optimizeBlock_diamond_elim_param x d n hn num y env

example (p : CatSem.PureExpr) (d : CatSem.VarId) (n : Int) (hn : n ≠ 0)
    (y : CatSem.PureExpr) (env : CatSem.Env) :
    CatSem.checkedDivCount (CatSem.optimizeBlock (.nonZero p) (CatSem.mkDeadBranchBlock p d n y)).ret = 0 ∧
      CatSem.divOpCount (CatSem.optimizeBlock (.nonZero p) (CatSem.mkDeadBranchBlock p d n y)).ret = 0 ∧
      CatSem.execBlockCheckCost env (CatSem.optimizeBlock (.nonZero p) (CatSem.mkDeadBranchBlock p d n y)) = 0 :=
  CatSem.optimizeBlock_dead_branch_elim_param p d n hn y env

-- Milestone 3 computability & signature checks (rejects `noncomputable` implementations)
def _computable_havocGuardIR : VarId → GuardIR → GuardIR :=
  CatSem.havocGuardIR

def _computable_strengthenLoopInvariantIR : VarId → Stmt → GuardIR → Option GuardIR :=
  CatSem.strengthenLoopInvariantIR

def _computable_hoistLoopGuardIR : Stmt → GuardIR → GuardIR → GuardIR :=
  CatSem.hoistLoopGuardIR

def _computable_optimizeLoop : GuardIR → LoopProg → LoopProg :=
  CatSem.optimizeLoop

example {S : Type*} (step : S → S) (Q : S → Prop) (n : ℕ) (s : S) :
    ((CatSem.stateTransfer step).iterate n).pullback Q s ↔ Q (step^[n] s) :=
  CatSem.stateTransfer_iterate_pullback_iff step Q n s

example (v : CatSem.VarId) (g : CatSem.GuardIR) :
    CatSem.denoteGuard (CatSem.havocGuardIR v g) ≤
      (CatSem.havocTransfer v).pullback (CatSem.denoteGuard g) :=
  CatSem.havocGuardIR_sound v g

example (v : CatSem.VarId) (g : CatSem.GuardIR)
    (h : CatSem.guardMentionsVar v g = false) :
    CatSem.denoteGuard (CatSem.havocGuardIR v g) =
      (CatSem.havocTransfer v).pullback (CatSem.denoteGuard g) :=
  CatSem.havocGuardIR_exact_of_nonMention v g h

example (accVar : CatSem.VarId) (latch : CatSem.Stmt)
    (target inv : CatSem.GuardIR)
    (h : CatSem.strengthenLoopInvariantIR accVar latch target = some inv) :
    CatSem.IsInductiveFor (CatSem.loopStepTransfer accVar latch)
      (CatSem.denoteGuard inv) (CatSem.denoteGuard target) :=
  CatSem.strengthenLoopInvariantIR_inductive accVar latch target inv h

example (accVar d i : CatSem.VarId) (hda : d ≠ accVar) (hdi : d ≠ i) :
    ∃ inv,
      CatSem.strengthenLoopInvariantIR accVar
        (.assign i (.sub (.var i) (.lit 1))) (.nonZero (.var d)) = some inv :=
  CatSem.strengthenLoopInvariantIR_stationary accVar d i hda hdi

example (accVar d nextD i : CatSem.VarId)
    (hda : d ≠ accVar) (hna : nextD ≠ accVar)
    (hdi : d ≠ i) (hni : nextD ≠ i) (hdn : d ≠ nextD) :
    ∃ inv,
      CatSem.strengthenLoopInvariantIR accVar
        (.seq (.assign d (.var nextD)) (.assign i (.sub (.var i) (.lit 1))))
        (.nonZero (.var d)) = some inv :=
  CatSem.strengthenLoopInvariantIR_pipeline accVar d nextD i hda hna hdi hni hdn

example (init : CatSem.Stmt) (ctx inv : CatSem.GuardIR) :
    CatSem.denoteGuard (CatSem.hoistLoopGuardIR init ctx inv) =
      CatSem.hoistLoopGuard (CatSem.stateTransfer (CatSem.execStmt init))
        (CatSem.denoteGuard ctx) (CatSem.denoteGuard inv) :=
  CatSem.hoistLoopGuardIR_denote init ctx inv

example (init : CatSem.Stmt) (accVar : CatSem.VarId) (latch : CatSem.Stmt)
    (ctx target inv : CatSem.GuardIR)
    (hInd : CatSem.IsInductiveFor (CatSem.loopStepTransfer accVar latch)
      (CatSem.denoteGuard inv) (CatSem.denoteGuard target))
    (n : ℕ) :
    (((CatSem.stateTransfer (CatSem.execStmt init)).comp
      ((CatSem.loopStepTransfer accVar latch).iterate n)).post
      (CatSem.denoteGuard ctx ⊓ CatSem.denoteGuard (CatSem.hoistLoopGuardIR init ctx inv))) ≤
      CatSem.denoteGuard target :=
  CatSem.hoistLoopGuardIR_iterate_target init accVar latch ctx target inv hInd n

example (fuel : Nat) (ctx : CatSem.GuardIR) (prog : CatSem.LoopProg) :
    CatSem.GuardedEquiv (CatSem.liftEval (CatSem.evalLoop fuel)) (CatSem.denoteGuard ctx)
      (CatSem.optimizeLoop ctx prog) prog :=
  CatSem.optimizeLoop_guardedEquiv fuel ctx prog

example (fuel : Nat) (ctx : CatSem.GuardIR) (prog : CatSem.LoopProg) (env : CatSem.Env) :
    CatSem.evalGuard env ctx = true →
      CatSem.evalLoop fuel env (CatSem.optimizeLoop ctx prog) = CatSem.evalLoop fuel env prog :=
  CatSem.optimizeLoop_sound fuel ctx prog env

example (x d i acc : CatSem.VarId)
    (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : CatSem.PureExpr) (n : Nat) (env : CatSem.Env)
    (hi : env i = Int.ofNat n) (hx : CatSem.evalGuard env (.nonZero (.var x)) = true) :
    let src := CatSem.LoopProg.whileLoop (CatSem.mkCountedDivLoop x d i acc num y)
    let opt := CatSem.optimizeLoop (.nonZero (.var x)) src
    CatSem.loopCheckedDivCount opt = 0 ∧
      CatSem.loopDivOpCount opt ≤ 1 ∧
      CatSem.loopBranchCount opt = 0 ∧
      CatSem.execLoopCheckCost (n + 1) env opt = n + 1 ∧
      CatSem.execLoopCheckCost (n + 1) env src = 3 * n + 1 :=
  CatSem.optimizeLoop_known_ctx_elim_param x d i acc hid hia hda num y n env hi hx

example (x d i acc : CatSem.VarId)
    (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : CatSem.PureExpr) (n : Nat) (env : CatSem.Env)
    (hi : env i = Int.ofNat n) (hx : env x ≠ 0) :
    let src := CatSem.LoopProg.whileLoop (CatSem.mkCountedDivLoop x d i acc num y)
    let opt := CatSem.optimizeLoop .top src
    CatSem.execLoopCheckCost (n + 1) env opt ≤ n + 2 ∧
      CatSem.execLoopCheckCost (n + 1) env src = 3 * n + 1 :=
  CatSem.optimizeLoop_unknown_ctx_hoist_param x d i acc hid hia hda num y n env hi hx

example (x d i acc : CatSem.VarId)
    (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : CatSem.PureExpr) (n : Nat) (env₀ env₁ : CatSem.Env)
    (hx₀ : env₀ x = 0) (hi₀ : env₀ i = 0)
    (hx₁ : env₁ x = 0) (hi₁ : env₁ i = Int.ofNat (n + 1)) :
    let src := CatSem.LoopProg.whileLoop (CatSem.mkCountedDivLoop x d i acc num y)
    CatSem.evalLoop 1 env₀ (CatSem.optimizeLoop .top src) = .done (.val (env₀ acc)) ∧
      CatSem.evalLoop (n + 2) env₁ (CatSem.optimizeLoop .top src) = .done .trap :=
  CatSem.optimizeLoop_zero_div_behavior_param x d i acc hid hia hda num y n env₀ env₁ hx₀ hi₀ hx₁ hi₁

example (x z d nextD i acc : CatSem.VarId)
    (hda : d ≠ acc) (hna : nextD ≠ acc)
    (hid : i ≠ d) (hin : i ≠ nextD) (hia : i ≠ acc) (hdn : d ≠ nextD)
    (num y : CatSem.PureExpr) (n : Nat) (env : CatSem.Env)
    (hi : env i = Int.ofNat n)
    (hctx : CatSem.evalGuard env (.conj (.nonZero (.var x)) (.nonZero (.var z))) = true) :
    let src := CatSem.LoopProg.whileLoop (CatSem.mkPipelineDivLoop x z d nextD i acc num y)
    let opt := CatSem.optimizeLoop (.conj (.nonZero (.var x)) (.nonZero (.var z))) src
    CatSem.loopCheckedDivCount opt = 0 ∧
      CatSem.loopDivOpCount opt ≤ 1 ∧
      CatSem.loopBranchCount opt = 0 ∧
      CatSem.execLoopCheckCost (n + 1) env opt = n + 1 :=
  CatSem.optimizeLoop_pipeline_elim_param x z d nextD i acc hda hna hid hin hia hdn num y n env hi hctx

example (x d i acc : CatSem.VarId)
    (hda : d ≠ acc) (hia : i ≠ acc) (hid : i ≠ d)
    (num : CatSem.PureExpr) (env : CatSem.Env) (hx : env x = 1) (hi : env i = 2) :
    CatSem.evalLoop 3 env
      (CatSem.optimizeLoop (.nonZero (.var x))
        (.whileLoop (CatSem.mkDecrementDivisorLoop x d i acc num))) = .done .trap :=
  CatSem.optimizeLoop_decrement_div_trap_param x d i acc hda hia hid num env hx hi

example (accVar d i : CatSem.VarId)
    (hda : d ≠ accVar) (hdi : d ≠ i) (stepRhs : CatSem.PureExpr) :
    ∃ inv,
      CatSem.strengthenLoopInvariantIR accVar (.assign i stepRhs) (.nonZero (.var d)) = some inv ∧
      (∀ env : CatSem.Env, env d ≠ 0 → CatSem.evalGuard env inv = true) ∧
      (∀ x : CatSem.VarId,
        CatSem.hoistLoopGuardIR (.assign d (.var x)) (.nonZero (.var x)) inv = .top) :=
  CatSem.strengthenLoopInvariantIR_stationary_safe accVar d i hda hdi stepRhs

example (accVar d nextD i : CatSem.VarId)
    (hda : d ≠ accVar) (hna : nextD ≠ accVar)
    (hdi : d ≠ i) (hni : nextD ≠ i) (hdn : d ≠ nextD) (stepRhs : CatSem.PureExpr) :
    ∃ inv,
      CatSem.strengthenLoopInvariantIR accVar
        (.seq (.assign d (.var nextD)) (.assign i stepRhs))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : CatSem.Env, env d ≠ 0 → env nextD ≠ 0 → CatSem.evalGuard env inv = true) ∧
      (∀ x z : CatSem.VarId,
        CatSem.hoistLoopGuardIR
          (.seq (.assign d (.var x)) (.assign nextD (.var z)))
          (.conj (.nonZero (.var x)) (.nonZero (.var z)))
          inv = .top) :=
  CatSem.strengthenLoopInvariantIR_pipeline_safe accVar d nextD i hda hna hdi hni hdn stepRhs

example (accVar : CatSem.VarId) (latch : CatSem.Stmt) (target : CatSem.GuardIR) :
    let g₁ := CatSem.havocGuardIR accVar (CatSem.pullbackGuardIR latch target)
    let cand := CatSem.GuardIR.conj target g₁
    CatSem.synthesizeGuardIR cand (CatSem.havocGuardIR accVar (CatSem.pullbackGuardIR latch cand)) = .top →
      ∃ inv,
        CatSem.strengthenLoopInvariantIR accVar latch target = some inv ∧
        (∀ env : CatSem.Env,
          CatSem.evalGuard env target = true →
          CatSem.evalGuard env g₁ = true →
          CatSem.evalGuard env inv = true) :=
  CatSem.strengthenLoopInvariantIR_step_complete accVar latch target

example (v : CatSem.VarId) (g : CatSem.GuardIR)
    (h : CatSem.guardMentionsVar v g = false) :
    CatSem.havocGuardIR v g = g :=
  CatSem.havocGuardIR_nonMention_eq v g h

example (accVar d : CatSem.VarId) (latch : CatSem.Stmt)
    (hda : d ≠ accVar)
    (hdWrite : CatSem.stmtWritesVar d latch = false)
    (haWrite : CatSem.stmtWritesVar accVar latch = false) :
    ∃ inv,
      CatSem.strengthenLoopInvariantIR accVar latch (.nonZero (.var d)) = some inv ∧
      (∀ env : CatSem.Env, env d ≠ 0 → CatSem.evalGuard env inv = true) ∧
      (∀ x : CatSem.VarId,
        CatSem.hoistLoopGuardIR (.assign d (.var x)) (.nonZero (.var x)) inv = .top) :=
  CatSem.strengthenLoopInvariantIR_frame_stmt_safe accVar d latch hda hdWrite haWrite

example (accVar d altD tmp : CatSem.VarId)
    (preLatch postLatch : CatSem.Stmt)
    (hda : d ≠ accVar) (hala : altD ≠ accVar) (hta : tmp ≠ accVar)
    (hdal : d ≠ altD) (hdt : d ≠ tmp) (halt : altD ≠ tmp)
    (hPreD : CatSem.stmtWritesVar d preLatch = false)
    (hPreAlt : CatSem.stmtWritesVar altD preLatch = false)
    (hPreAcc : CatSem.stmtWritesVar accVar preLatch = false)
    (hPostD : CatSem.stmtWritesVar d postLatch = false)
    (hPostAlt : CatSem.stmtWritesVar altD postLatch = false)
    (hPostTmp : CatSem.stmtWritesVar tmp postLatch = false)
    (hPostAcc : CatSem.stmtWritesVar accVar postLatch = false) :
    ∃ inv,
      CatSem.strengthenLoopInvariantIR accVar
        (.seq preLatch
          (.seq (.assign tmp (.var d))
            (.seq (.assign d (.var altD))
              (.seq (.assign altD (.var tmp)) postLatch))))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : CatSem.Env, env d ≠ 0 → env altD ≠ 0 → CatSem.evalGuard env inv = true) ∧
      (∀ x z : CatSem.VarId,
        CatSem.hoistLoopGuardIR
          (.seq (.assign d (.var x)) (.assign altD (.var z)))
          (.conj (.nonZero (.var x)) (.nonZero (.var z)))
          inv = .top) :=
  CatSem.strengthenLoopInvariantIR_swap_safe accVar d altD tmp preLatch postLatch
    hda hala hta hdal hdt halt hPreD hPreAlt hPreAcc hPostD hPostAlt hPostTmp hPostAcc

example (accVar d d₁ d₂ : CatSem.VarId)
    (preLatch postLatch : CatSem.Stmt)
    (hda : d ≠ accVar) (hd₁a : d₁ ≠ accVar) (hd₂a : d₂ ≠ accVar)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (hPreD : CatSem.stmtWritesVar d preLatch = false)
    (hPreD₁ : CatSem.stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : CatSem.stmtWritesVar d₂ preLatch = false)
    (hPreAcc : CatSem.stmtWritesVar accVar preLatch = false)
    (hPostD : CatSem.stmtWritesVar d postLatch = false)
    (hPostD₁ : CatSem.stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : CatSem.stmtWritesVar d₂ postLatch = false)
    (hPostAcc : CatSem.stmtWritesVar accVar postLatch = false) :
    ∃ inv,
      CatSem.strengthenLoopInvariantIR accVar
        (.seq preLatch
          (.seq (.assign d (.var d₁))
            (.seq (.assign d₁ (.var d₂)) postLatch)))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : CatSem.Env, env d ≠ 0 → env d₁ ≠ 0 → env d₂ ≠ 0 → CatSem.evalGuard env inv = true) ∧
      (∀ x w z : CatSem.VarId,
        CatSem.hoistLoopGuardIR
          (.seq (.assign d (.var x)) (.seq (.assign d₁ (.var w)) (.assign d₂ (.var z))))
          (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z))))
          inv = .top) :=
  CatSem.strengthenLoopInvariantIR_pipeline3_safe accVar d d₁ d₂ preLatch postLatch
    hda hd₁a hd₂a hdd₁ hdd₂ hd₁d₂ hPreD hPreD₁ hPreD₂ hPreAcc hPostD hPostD₁ hPostD₂ hPostAcc

example (accVar d d₁ d₂ : CatSem.VarId)
    (branchCond : CatSem.GuardIR) (preLatch postLatch : CatSem.Stmt)
    (hda : d ≠ accVar) (hd₁a : d₁ ≠ accVar) (hd₂a : d₂ ≠ accVar)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (hPreD : CatSem.stmtWritesVar d preLatch = false)
    (hPreD₁ : CatSem.stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : CatSem.stmtWritesVar d₂ preLatch = false)
    (hPreAcc : CatSem.stmtWritesVar accVar preLatch = false)
    (hPostD : CatSem.stmtWritesVar d postLatch = false)
    (hPostD₁ : CatSem.stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : CatSem.stmtWritesVar d₂ postLatch = false)
    (hPostAcc : CatSem.stmtWritesVar accVar postLatch = false) :
    ∃ inv,
      CatSem.strengthenLoopInvariantIR accVar
        (.seq preLatch
          (.seq (.ite branchCond (.assign d (.var d₁)) (.assign d (.var d₂))) postLatch))
        (.nonZero (.var d)) = some inv ∧
      (∀ env : CatSem.Env, env d ≠ 0 → env d₁ ≠ 0 → env d₂ ≠ 0 → CatSem.evalGuard env inv = true) ∧
      (∀ x w z : CatSem.VarId,
        CatSem.hoistLoopGuardIR
          (.seq (.assign d (.var x)) (.seq (.assign d₁ (.var w)) (.assign d₂ (.var z))))
          (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z))))
          inv = .top) :=
  CatSem.strengthenLoopInvariantIR_ite_branch_safe accVar d d₁ d₂ branchCond preLatch postLatch
    hda hd₁a hd₂a hdd₁ hdd₂ hd₁d₂ hPreD hPreD₁ hPreD₂ hPreAcc hPostD hPostD₁ hPostD₂ hPostAcc

example (x d i acc : CatSem.VarId)
    (hid : i ≠ d) (hia : i ≠ acc) (hda : d ≠ acc)
    (num y : CatSem.PureExpr) (preLatch postLatch : CatSem.Stmt)
    (hPreD : CatSem.stmtWritesVar d preLatch = false)
    (hPreI : CatSem.stmtWritesVar i preLatch = false)
    (hPreAcc : CatSem.stmtWritesVar acc preLatch = false)
    (hPostD : CatSem.stmtWritesVar d postLatch = false)
    (hPostI : CatSem.stmtWritesVar i postLatch = false)
    (hPostAcc : CatSem.stmtWritesVar acc postLatch = false)
    (n : Nat) (env : CatSem.Env)
    (hi : env i = Int.ofNat n)
    (hx : CatSem.evalGuard env (.nonZero (.var x)) = true) :
    let src := CatSem.LoopProg.whileLoop (CatSem.mkFrameStmtDivLoop x d i acc num y preLatch postLatch)
    let opt := CatSem.optimizeLoop (.nonZero (.var x)) src
    CatSem.loopCheckedDivCount opt = 0 ∧
      CatSem.loopDivOpCount opt ≤ 1 ∧
      CatSem.loopBranchCount opt = 0 ∧
      CatSem.execLoopCheckCost (n + 1) env opt + 2 * n ≤ CatSem.execLoopCheckCost (n + 1) env src :=
  CatSem.optimizeLoop_frame_stmt_elim_param x d i acc hid hia hda num y preLatch postLatch
    hPreD hPreI hPreAcc hPostD hPostI hPostAcc n env hi hx

example (x z d altD tmp i acc : CatSem.VarId)
    (hda : d ≠ acc) (hala : altD ≠ acc) (hta : tmp ≠ acc)
    (hid : i ≠ d) (hial : i ≠ altD) (hit : i ≠ tmp) (hia : i ≠ acc)
    (hdal : d ≠ altD) (hdt : d ≠ tmp) (halt : altD ≠ tmp)
    (num y : CatSem.PureExpr) (preLatch postLatch : CatSem.Stmt)
    (hPreD : CatSem.stmtWritesVar d preLatch = false)
    (hPreAlt : CatSem.stmtWritesVar altD preLatch = false)
    (hPreI : CatSem.stmtWritesVar i preLatch = false)
    (hPreAcc : CatSem.stmtWritesVar acc preLatch = false)
    (hPostD : CatSem.stmtWritesVar d postLatch = false)
    (hPostAlt : CatSem.stmtWritesVar altD postLatch = false)
    (hPostTmp : CatSem.stmtWritesVar tmp postLatch = false)
    (hPostI : CatSem.stmtWritesVar i postLatch = false)
    (hPostAcc : CatSem.stmtWritesVar acc postLatch = false)
    (n : Nat) (env : CatSem.Env)
    (hi : env i = Int.ofNat n)
    (hctx : CatSem.evalGuard env (.conj (.nonZero (.var x)) (.nonZero (.var z))) = true) :
    let src := CatSem.LoopProg.whileLoop (CatSem.mkSwapDivLoop x z d altD tmp i acc num y preLatch postLatch)
    let opt := CatSem.optimizeLoop (.conj (.nonZero (.var x)) (.nonZero (.var z))) src
    CatSem.loopCheckedDivCount opt = 0 ∧
      CatSem.loopDivOpCount opt ≤ 1 ∧
      CatSem.loopBranchCount opt = 0 ∧
      CatSem.execLoopCheckCost (n + 1) env opt + 2 * n ≤ CatSem.execLoopCheckCost (n + 1) env src :=
  CatSem.optimizeLoop_swap_elim_param x z d altD tmp i acc hda hala hta hid hial hit hia hdal hdt halt
    num y preLatch postLatch hPreD hPreAlt hPreI hPreAcc hPostD hPostAlt hPostTmp hPostI hPostAcc n env hi hctx

example (x w z d d₁ d₂ i acc : CatSem.VarId)
    (hda : d ≠ acc) (hd₁a : d₁ ≠ acc) (hd₂a : d₂ ≠ acc)
    (hid : i ≠ d) (hid₁ : i ≠ d₁) (hid₂ : i ≠ d₂) (hia : i ≠ acc)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (num y : CatSem.PureExpr) (preLatch postLatch : CatSem.Stmt)
    (hPreD : CatSem.stmtWritesVar d preLatch = false)
    (hPreD₁ : CatSem.stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : CatSem.stmtWritesVar d₂ preLatch = false)
    (hPreI : CatSem.stmtWritesVar i preLatch = false)
    (hPreAcc : CatSem.stmtWritesVar acc preLatch = false)
    (hPostD : CatSem.stmtWritesVar d postLatch = false)
    (hPostD₁ : CatSem.stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : CatSem.stmtWritesVar d₂ postLatch = false)
    (hPostI : CatSem.stmtWritesVar i postLatch = false)
    (hPostAcc : CatSem.stmtWritesVar acc postLatch = false)
    (n : Nat) (env : CatSem.Env)
    (hi : env i = Int.ofNat n)
    (hctx : CatSem.evalGuard env (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) = true) :
    let src := CatSem.LoopProg.whileLoop (CatSem.mkPipeline3DivLoop x w z d d₁ d₂ i acc num y preLatch postLatch)
    let opt := CatSem.optimizeLoop (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) src
    CatSem.loopCheckedDivCount opt = 0 ∧
      CatSem.loopDivOpCount opt ≤ 1 ∧
      CatSem.loopBranchCount opt = 0 ∧
      CatSem.execLoopCheckCost (n + 1) env opt + 2 * n ≤ CatSem.execLoopCheckCost (n + 1) env src :=
  CatSem.optimizeLoop_pipeline3_elim_param x w z d d₁ d₂ i acc hda hd₁a hd₂a hid hid₁ hid₂ hia hdd₁ hdd₂ hd₁d₂
    num y preLatch postLatch hPreD hPreD₁ hPreD₂ hPreI hPreAcc hPostD hPostD₁ hPostD₂ hPostI hPostAcc n env hi hctx

example (x w z d d₁ d₂ i acc : CatSem.VarId)
    (hda : d ≠ acc) (hd₁a : d₁ ≠ acc) (hd₂a : d₂ ≠ acc)
    (hid : i ≠ d) (hid₁ : i ≠ d₁) (hid₂ : i ≠ d₂) (hia : i ≠ acc)
    (hdd₁ : d ≠ d₁) (hdd₂ : d ≠ d₂) (hd₁d₂ : d₁ ≠ d₂)
    (branchCond : CatSem.GuardIR) (num y : CatSem.PureExpr) (preLatch postLatch : CatSem.Stmt)
    (hPreD : CatSem.stmtWritesVar d preLatch = false)
    (hPreD₁ : CatSem.stmtWritesVar d₁ preLatch = false)
    (hPreD₂ : CatSem.stmtWritesVar d₂ preLatch = false)
    (hPreI : CatSem.stmtWritesVar i preLatch = false)
    (hPreAcc : CatSem.stmtWritesVar acc preLatch = false)
    (hPostD : CatSem.stmtWritesVar d postLatch = false)
    (hPostD₁ : CatSem.stmtWritesVar d₁ postLatch = false)
    (hPostD₂ : CatSem.stmtWritesVar d₂ postLatch = false)
    (hPostI : CatSem.stmtWritesVar i postLatch = false)
    (hPostAcc : CatSem.stmtWritesVar acc postLatch = false)
    (n : Nat) (env : CatSem.Env)
    (hi : env i = Int.ofNat n)
    (hctx : CatSem.evalGuard env (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) = true) :
    let src := CatSem.LoopProg.whileLoop (CatSem.mkBranchDivLoop x w z d d₁ d₂ i acc branchCond num y preLatch postLatch)
    let opt := CatSem.optimizeLoop (.conj (.nonZero (.var x)) (.conj (.nonZero (.var w)) (.nonZero (.var z)))) src
    CatSem.loopCheckedDivCount opt = 0 ∧
      CatSem.loopDivOpCount opt ≤ 1 ∧
      CatSem.loopBranchCount opt = 0 ∧
      CatSem.execLoopCheckCost (n + 1) env opt + 2 * n ≤ CatSem.execLoopCheckCost (n + 1) env src :=
  CatSem.optimizeLoop_ite_branch_elim_param x w z d d₁ d₂ i acc hda hd₁a hd₂a hid hid₁ hid₂ hia hdd₁ hdd₂ hd₁d₂
    branchCond num y preLatch postLatch hPreD hPreD₁ hPreD₂ hPreI hPreAcc hPostD hPostD₁ hPostD₂ hPostI hPostAcc n env hi hctx

#print axioms CatSem.synthesizeGuard
#print axioms CatSem.synthesizeEdgeGuard
#print axioms CatSem.CFGTransfer.id
#print axioms CatSem.CFGTransfer.comp
#print axioms CatSem.IsLoopInvariant
#print axioms CatSem.synthesizeLoopStepGuard
#print axioms CatSem.IsInductiveFor
#print axioms CatSem.hoistLoopGuard
#print axioms CatSem.CFGTransfer.iterate
#print axioms CatSem.Forces
#print axioms CatSem.ForcesAfter
#print axioms CatSem.GuardedEquiv
#print axioms CatSem.pullbackEval
#print axioms CatSem.CompatibleOp2
#print axioms CatSem.stateTransfer
#print axioms CatSem.evalPure
#print axioms CatSem.evalGuard
#print axioms CatSem.denoteGuard
#print axioms CatSem.bindOutcome2
#print axioms CatSem.evalExpr
#print axioms CatSem.liftEval
#print axioms CatSem.liftBinarySem
#print axioms CatSem.checkedDivCount
#print axioms CatSem.divOpCount
#print axioms CatSem.guardBranchCount
#print axioms CatSem.guardEvalCost
#print axioms CatSem.execCheckCost
#print axioms CatSem.mkCancelExpr
#print axioms CatSem.mkDualDivExpr
#print axioms CatSem.m1CancelExpr
#print axioms CatSem.m1BenchExpr
#print axioms CatSem.updateEnv
#print axioms CatSem.execStmt
#print axioms CatSem.evalBlock
#print axioms CatSem.stmtGuardCost
#print axioms CatSem.execBlockCheckCost
#print axioms CatSem.mkClobberBlock
#print axioms CatSem.mkDiamondSafeBlock
#print axioms CatSem.mkDeadBranchBlock
#print axioms CatSem.pureMentionsVar
#print axioms CatSem.guardMentionsVar
#print axioms CatSem.havocTransfer
#print axioms CatSem.loopStepTransfer
#print axioms CatSem.runWhileSteps
#print axioms CatSem.evalLoop
#print axioms CatSem.loopCheckedDivCount
#print axioms CatSem.loopDivOpCount
#print axioms CatSem.loopBranchCount
#print axioms CatSem.runWhileCheckCost
#print axioms CatSem.execLoopCheckCost
#print axioms CatSem.mkCountedDivLoop
#print axioms CatSem.mkPipelineDivLoop
#print axioms CatSem.mkDecrementDivisorLoop
#print axioms CatSem.stmtWritesVar
#print axioms CatSem.mkFrameStmtDivLoop
#print axioms CatSem.mkSwapDivLoop
#print axioms CatSem.mkPipeline3DivLoop
#print axioms CatSem.mkBranchDivLoop
#print axioms CatSem.synthesizeGuardIR
#print axioms CatSem.optimizeExpr
#print axioms CatSem.pullbackGuardIR
#print axioms CatSem.synthesizeStmtGuardIR
#print axioms CatSem.optimizeBlock
#print axioms CatSem.havocGuardIR
#print axioms CatSem.strengthenLoopInvariantIR
#print axioms CatSem.hoistLoopGuardIR
#print axioms CatSem.optimizeLoop
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
#print axioms CatSem.forcesAfter_iff_pullback
#print axioms CatSem.forces_guard_iff
#print axioms CatSem.forces_rewrite_chain_iff
#print axioms CatSem.forcesAfter_hoistLoopGuard_iterate
#print axioms CatSem.guardedEquiv_refl
#print axioms CatSem.guardedEquiv_symm
#print axioms CatSem.guardedEquiv_trans_inf
#print axioms CatSem.guardedEquiv_synthesize_chain
#print axioms CatSem.guardedEquiv_weaken
#print axioms CatSem.guardedEquiv_pullback
#print axioms CatSem.guardedEquiv_edge_synthesize
#print axioms CatSem.guardedEquiv_hoistLoopGuard_iterate
#print axioms CatSem.guardedEquiv_congr2
#print axioms CatSem.guardedEquiv_congr2_synthesize
#print axioms CatSem.guardedEquiv_pullback_inf_commute
#print axioms CatSem.guardedEquiv_diamond
#print axioms CatSem.stateTransfer_pullback_apply
#print axioms CatSem.stateTransfer_synthesizeEdgeGuard_apply
#print axioms CatSem.stateTransfer_isLoopInvariant_iff
#print axioms CatSem.stateTransfer_hoistLoopGuard_iterate_equiv
#print axioms CatSem.liftEval_guardedEquiv_iff
#print axioms CatSem.exprAdd_compatibleOp2
#print axioms CatSem.exprCheckedDiv_compatibleOp2
#print axioms CatSem.synthesizeGuardIR_denote
#print axioms CatSem.synthesizeGuardIR_universal
#print axioms CatSem.synthesizeGuardIR_discharge_self
#print axioms CatSem.optimizeExpr_guardedEquiv
#print axioms CatSem.optimizeExpr_sound
#print axioms CatSem.optimizeExpr_known_ctx_elim
#print axioms CatSem.optimizeExpr_cancel_div
#print axioms CatSem.optimizeExpr_unknown_ctx_dedup
#print axioms CatSem.optimizeExpr_zero_div_trap
#print axioms CatSem.synthesizeGuardIR_top_right
#print axioms CatSem.synthesizeGuardIR_bot_left
#print axioms CatSem.synthesizeGuardIR_top_left_nonZero
#print axioms CatSem.synthesizeGuardIR_discharge_conj_left
#print axioms CatSem.synthesizeGuardIR_discharge_conj_right
#print axioms CatSem.synthesizeGuardIR_dedup_conj
#print axioms CatSem.optimizeExpr_elim_checkedDiv_param
#print axioms CatSem.optimizeExpr_cancel_div_param
#print axioms CatSem.optimizeExpr_compositional_binary
#print axioms CatSem.optimizeExpr_known_ctx_elim_param
#print axioms CatSem.optimizeExpr_unknown_ctx_dedup_param
#print axioms CatSem.optimizeExpr_zero_div_trap_param
#print axioms CatSem.pullbackEval_stateTransfer_liftEval_iff
#print axioms CatSem.pullbackGuardIR_denote
#print axioms CatSem.pullbackGuardIR_seq
#print axioms CatSem.synthesizeStmtGuardIR_denote
#print axioms CatSem.synthesizeStmtGuardIR_universal
#print axioms CatSem.synthesizeStmtGuardIR_diamond_sound
#print axioms CatSem.synthesizeStmtGuardIR_lit_nonZero
#print axioms CatSem.synthesizeStmtGuardIR_assign_self
#print axioms CatSem.synthesizeStmtGuardIR_diamond_safe
#print axioms CatSem.optimizeBlock_guardedEquiv
#print axioms CatSem.optimizeBlock_sound
#print axioms CatSem.optimizeBlock_literal_div_elim_param
#print axioms CatSem.optimizeBlock_seq_clobber_elim_param
#print axioms CatSem.optimizeBlock_clobber_trap_param
#print axioms CatSem.optimizeBlock_diamond_elim_param
#print axioms CatSem.optimizeBlock_dead_branch_elim_param
#print axioms CatSem.stateTransfer_iterate_pullback_iff
#print axioms CatSem.havocGuardIR_sound
#print axioms CatSem.havocGuardIR_exact_of_nonMention
#print axioms CatSem.strengthenLoopInvariantIR_inductive
#print axioms CatSem.strengthenLoopInvariantIR_stationary
#print axioms CatSem.strengthenLoopInvariantIR_pipeline
#print axioms CatSem.hoistLoopGuardIR_denote
#print axioms CatSem.hoistLoopGuardIR_iterate_target
#print axioms CatSem.optimizeLoop_guardedEquiv
#print axioms CatSem.optimizeLoop_sound
#print axioms CatSem.optimizeLoop_known_ctx_elim_param
#print axioms CatSem.optimizeLoop_unknown_ctx_hoist_param
#print axioms CatSem.optimizeLoop_zero_div_behavior_param
#print axioms CatSem.optimizeLoop_pipeline_elim_param
#print axioms CatSem.optimizeLoop_decrement_div_trap_param
#print axioms CatSem.strengthenLoopInvariantIR_stationary_safe
#print axioms CatSem.strengthenLoopInvariantIR_pipeline_safe
#print axioms CatSem.strengthenLoopInvariantIR_step_complete
#print axioms CatSem.havocGuardIR_nonMention_eq
#print axioms CatSem.strengthenLoopInvariantIR_frame_stmt_safe
#print axioms CatSem.strengthenLoopInvariantIR_swap_safe
#print axioms CatSem.strengthenLoopInvariantIR_pipeline3_safe
#print axioms CatSem.strengthenLoopInvariantIR_ite_branch_safe
#print axioms CatSem.optimizeLoop_frame_stmt_elim_param
#print axioms CatSem.optimizeLoop_swap_elim_param
#print axioms CatSem.optimizeLoop_pipeline3_elim_param
#print axioms CatSem.optimizeLoop_ite_branch_elim_param

-- In-kernel transitive axiom allowlist audit on compiler passes and all Rounds 1–11 + Milestones 1–3 theorems
#verify_allowed_axioms CatSem.synthesizeGuardIR
#verify_allowed_axioms CatSem.optimizeExpr
#verify_allowed_axioms CatSem.pullbackGuardIR
#verify_allowed_axioms CatSem.synthesizeStmtGuardIR
#verify_allowed_axioms CatSem.optimizeBlock
#verify_allowed_axioms CatSem.havocGuardIR
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR
#verify_allowed_axioms CatSem.hoistLoopGuardIR
#verify_allowed_axioms CatSem.optimizeLoop
#verify_allowed_axioms CatSem.synthesizeGuard_sound
#verify_allowed_axioms CatSem.synthesizeGuard_weakest
#verify_allowed_axioms CatSem.synthesizeGuard_adjunction
#verify_allowed_axioms CatSem.synthesizeEdgeGuard_sound
#verify_allowed_axioms CatSem.synthesizeEdgeGuard_weakest
#verify_allowed_axioms CatSem.synthesizeBranchGuard_iff
#verify_allowed_axioms CatSem.pullback_map_inf
#verify_allowed_axioms CatSem.synthesizeEdgeGuard_comp
#verify_allowed_axioms CatSem.synthesizeEdgeGuard_map_inf
#verify_allowed_axioms CatSem.synthesizeDiamondGuard_iff
#verify_allowed_axioms CatSem.isLoopInvariant_iff_le_pullback
#verify_allowed_axioms CatSem.isLoopInvariant_iff_guard_eq_top
#verify_allowed_axioms CatSem.synthesizeLoopStepGuard_sound
#verify_allowed_axioms CatSem.isLoopInvariant_inf
#verify_allowed_axioms CatSem.isLoopInvariant_iterate_two
#verify_allowed_axioms CatSem.hoistLoopGuard_entry_target
#verify_allowed_axioms CatSem.hoistLoopGuard_step_invariant
#verify_allowed_axioms CatSem.hoistLoopGuard_step_target
#verify_allowed_axioms CatSem.isLoopInvariant_iterate
#verify_allowed_axioms CatSem.isLoopInvariant_iterate_pullback
#verify_allowed_axioms CatSem.hoistLoopGuard_iterate_invariant
#verify_allowed_axioms CatSem.hoistLoopGuard_iterate_target
#verify_allowed_axioms CatSem.forcesAfter_iff_pullback
#verify_allowed_axioms CatSem.forces_guard_iff
#verify_allowed_axioms CatSem.forces_rewrite_chain_iff
#verify_allowed_axioms CatSem.forcesAfter_hoistLoopGuard_iterate
#verify_allowed_axioms CatSem.guardedEquiv_refl
#verify_allowed_axioms CatSem.guardedEquiv_symm
#verify_allowed_axioms CatSem.guardedEquiv_trans_inf
#verify_allowed_axioms CatSem.guardedEquiv_synthesize_chain
#verify_allowed_axioms CatSem.guardedEquiv_weaken
#verify_allowed_axioms CatSem.guardedEquiv_pullback
#verify_allowed_axioms CatSem.guardedEquiv_edge_synthesize
#verify_allowed_axioms CatSem.guardedEquiv_hoistLoopGuard_iterate
#verify_allowed_axioms CatSem.guardedEquiv_congr2
#verify_allowed_axioms CatSem.guardedEquiv_congr2_synthesize
#verify_allowed_axioms CatSem.guardedEquiv_pullback_inf_commute
#verify_allowed_axioms CatSem.guardedEquiv_diamond
#verify_allowed_axioms CatSem.stateTransfer_pullback_apply
#verify_allowed_axioms CatSem.stateTransfer_synthesizeEdgeGuard_apply
#verify_allowed_axioms CatSem.stateTransfer_isLoopInvariant_iff
#verify_allowed_axioms CatSem.stateTransfer_hoistLoopGuard_iterate_equiv
#verify_allowed_axioms CatSem.liftEval_guardedEquiv_iff
#verify_allowed_axioms CatSem.exprAdd_compatibleOp2
#verify_allowed_axioms CatSem.exprCheckedDiv_compatibleOp2
#verify_allowed_axioms CatSem.synthesizeGuardIR_denote
#verify_allowed_axioms CatSem.synthesizeGuardIR_universal
#verify_allowed_axioms CatSem.synthesizeGuardIR_discharge_self
#verify_allowed_axioms CatSem.optimizeExpr_guardedEquiv
#verify_allowed_axioms CatSem.optimizeExpr_sound
#verify_allowed_axioms CatSem.optimizeExpr_known_ctx_elim
#verify_allowed_axioms CatSem.optimizeExpr_cancel_div
#verify_allowed_axioms CatSem.optimizeExpr_unknown_ctx_dedup
#verify_allowed_axioms CatSem.optimizeExpr_zero_div_trap
#verify_allowed_axioms CatSem.synthesizeGuardIR_top_right
#verify_allowed_axioms CatSem.synthesizeGuardIR_bot_left
#verify_allowed_axioms CatSem.synthesizeGuardIR_top_left_nonZero
#verify_allowed_axioms CatSem.synthesizeGuardIR_discharge_conj_left
#verify_allowed_axioms CatSem.synthesizeGuardIR_discharge_conj_right
#verify_allowed_axioms CatSem.synthesizeGuardIR_dedup_conj
#verify_allowed_axioms CatSem.optimizeExpr_elim_checkedDiv_param
#verify_allowed_axioms CatSem.optimizeExpr_cancel_div_param
#verify_allowed_axioms CatSem.optimizeExpr_compositional_binary
#verify_allowed_axioms CatSem.optimizeExpr_known_ctx_elim_param
#verify_allowed_axioms CatSem.optimizeExpr_unknown_ctx_dedup_param
#verify_allowed_axioms CatSem.optimizeExpr_zero_div_trap_param
#verify_allowed_axioms CatSem.pullbackEval_stateTransfer_liftEval_iff
#verify_allowed_axioms CatSem.pullbackGuardIR_denote
#verify_allowed_axioms CatSem.pullbackGuardIR_seq
#verify_allowed_axioms CatSem.synthesizeStmtGuardIR_denote
#verify_allowed_axioms CatSem.synthesizeStmtGuardIR_universal
#verify_allowed_axioms CatSem.synthesizeStmtGuardIR_diamond_sound
#verify_allowed_axioms CatSem.synthesizeStmtGuardIR_lit_nonZero
#verify_allowed_axioms CatSem.synthesizeStmtGuardIR_assign_self
#verify_allowed_axioms CatSem.synthesizeStmtGuardIR_diamond_safe
#verify_allowed_axioms CatSem.optimizeBlock_guardedEquiv
#verify_allowed_axioms CatSem.optimizeBlock_sound
#verify_allowed_axioms CatSem.optimizeBlock_literal_div_elim_param
#verify_allowed_axioms CatSem.optimizeBlock_seq_clobber_elim_param
#verify_allowed_axioms CatSem.optimizeBlock_clobber_trap_param
#verify_allowed_axioms CatSem.optimizeBlock_diamond_elim_param
#verify_allowed_axioms CatSem.optimizeBlock_dead_branch_elim_param
#verify_allowed_axioms CatSem.stateTransfer_iterate_pullback_iff
#verify_allowed_axioms CatSem.havocGuardIR_sound
#verify_allowed_axioms CatSem.havocGuardIR_exact_of_nonMention
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_inductive
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_stationary
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_pipeline
#verify_allowed_axioms CatSem.hoistLoopGuardIR_denote
#verify_allowed_axioms CatSem.hoistLoopGuardIR_iterate_target
#verify_allowed_axioms CatSem.optimizeLoop_guardedEquiv
#verify_allowed_axioms CatSem.optimizeLoop_sound
#verify_allowed_axioms CatSem.optimizeLoop_known_ctx_elim_param
#verify_allowed_axioms CatSem.optimizeLoop_unknown_ctx_hoist_param
#verify_allowed_axioms CatSem.optimizeLoop_zero_div_behavior_param
#verify_allowed_axioms CatSem.optimizeLoop_pipeline_elim_param
#verify_allowed_axioms CatSem.optimizeLoop_decrement_div_trap_param
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_stationary_safe
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_pipeline_safe
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_step_complete
#verify_allowed_axioms CatSem.havocGuardIR_nonMention_eq
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_frame_stmt_safe
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_swap_safe
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_pipeline3_safe
#verify_allowed_axioms CatSem.strengthenLoopInvariantIR_ite_branch_safe
#verify_allowed_axioms CatSem.optimizeLoop_frame_stmt_elim_param
#verify_allowed_axioms CatSem.optimizeLoop_swap_elim_param
#verify_allowed_axioms CatSem.optimizeLoop_pipeline3_elim_param
#verify_allowed_axioms CatSem.optimizeLoop_ite_branch_elim_param

end CatSem.Verify
