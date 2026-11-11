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
#print axioms CatSem.synthesizeGuardIR
#print axioms CatSem.optimizeExpr
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

-- In-kernel transitive axiom allowlist audit on compiler passes and all Rounds 1–11 + Milestone 1 theorems
#verify_allowed_axioms CatSem.synthesizeGuardIR
#verify_allowed_axioms CatSem.optimizeExpr
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

end CatSem.Verify
