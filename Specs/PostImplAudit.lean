import Proofs.Submission

/-!
Gate 2 implementation audit for submission
2a9ebbdc5f0593bb0dd230ca09cf3f096693dd340f291f155de5db6f2abb0a93.

These are named, kernel-checked computations against the actual compiler and
the independent concrete evaluator. No target stubs or custom elaborators are
imported. Context assumptions are explicitly checked in the positive tests.
Expected outcomes distinguish values, checked traps, and existing unchecked UB.
-/

namespace CatSem.PostImplAudit

/-- Variables 0..3 are controlled independently; higher identifiers are also exercised. -/
def env (d x y q : Int) : Env :=
  fun i => if i = 0 then d else if i = 1 then x else if i = 2 then y else if i = 3 then q else 4

def lit (n : Int) : Expr := .pure (.lit n)
def v (i : Nat) : Expr := .pure (.var i)
def nz : GuardIR := .nonZero (.var 0)
def trapExpr : Expr := .checkedDiv (lit 1) (lit 0)
def ubExpr : Expr := .uncheckedDiv (lit 1) (lit 0)

def nestedNum : Expr := .checkedDiv (.checkedDiv (v 1) (v 0)) (v 0)
def nestedDen : Expr := .checkedDiv (v 1) (.checkedDiv (v 2) (v 0))
def differentDivisors : Expr := .add (.checkedDiv (v 1) (v 0)) (.checkedDiv (v 2) (v 3))
def numeratorTrap : Expr := .checkedDiv (.mul (.checkedDiv (lit 9) (lit 0)) (v 0)) (v 0)
def reuseUnchecked : Expr := .add (.uncheckedDiv (v 1) (v 0)) (.checkedDiv (v 2) (v 0))
def arithmeticDenominator : Expr := .checkedDiv (v 1) (.sub (v 0) (lit 1))

def compoundD : PureExpr := .add (.var 7) (.lit 1)
def compoundX : PureExpr := .sub (.mul (.var 9) (.lit 3)) (.lit 2)
def compoundY : PureExpr := .add (.var 11) (.var 12)
def compound : Expr :=
  .sub (.add (.checkedDiv (.pure compoundX) (.pure compoundD))
      (.mul (lit 2) (mkCancelExpr compoundY compoundD))) (lit 3)
def compoundCtx : GuardIR :=
  .conj (.eq (.var 3) (.lit 6)) (.conj .top (.nonZero compoundD))

def guardedCancellation : Expr :=
  .iteGuard nz (mkCancelExpr (.var 1) (.var 0)) trapExpr
def branchFactsMustNotLeak : Expr :=
  .add (.iteGuard (.nonZero (.var 3)) (.checkedDiv (v 1) (v 0)) (lit 0))
    (.checkedDiv (v 2) (v 0))
def bothBranchesCheck : Expr :=
  .add (.iteGuard (.nonZero (.var 3)) (.checkedDiv (v 1) (v 0))
      (.checkedDiv (v 2) (v 0)))
    (.checkedDiv (v 1) (v 0))
def reverseCancel : Expr :=
  .checkedDiv (.mul (v 0) (.pure (.sub (.var 1) (.lit 3)))) (v 0)

/-- Normalization is structural and works on compound operands and nested contexts. -/
theorem guard_normalization :
    synthesizeGuardIR .top (.nonZero (.var 7)) = .nonZero (.var 7) ∧
    synthesizeGuardIR
      (.conj (.eq (.var 3) (.lit 6)) (.conj (.nonZero compoundD) (.nonZero (.var 7))))
      (.conj (.nonZero compoundD) (.conj (.nonZero (.var 7)) (.nonZero compoundD))) = .top ∧
    synthesizeGuardIR .top
      (.conj (.nonZero (.var 7)) (.conj (.nonZero (.var 9)) (.nonZero (.var 7)))) =
      .conj (.nonZero (.var 7)) (.nonZero (.var 9)) := by
  decide

/-- Residual implication is neither a constant-false fallback nor unconditionally true. -/
theorem residual_truth_cases :
    evalGuard (env 0 7 8 0) (synthesizeGuardIR nz (.nonZero (.var 3))) = true ∧
    evalGuard (env 2 7 8 0) (synthesizeGuardIR nz (.nonZero (.var 3))) = false ∧
    evalGuard (env 2 7 8 3) (synthesizeGuardIR nz (.nonZero (.var 3))) = true := by
  decide

/-- The implementation deliberately treats arithmetic atoms syntactically. -/
theorem conservative_atomic_reasoning :
    synthesizeGuardIR .top (.nonZero (.lit 2)) = .nonZero (.lit 2) ∧
    checkedDivCount (optimizeExpr .top (.checkedDiv (lit 7) (lit 2))) = 1 := by
  decide

/-- An inner successful check justifies removing the outer check of the same divisor. -/
theorem nested_numerator_positive :
    evalExpr (env 2 20 8 3) nestedNum = .val 5 ∧
    evalExpr (env 2 20 8 3) (optimizeExpr .top nestedNum) = .val 5 ∧
    checkedDivCount nestedNum = 2 ∧ checkedDivCount (optimizeExpr .top nestedNum) = 1 ∧
    execCheckCost (env 2 20 8 3) nestedNum = 2 ∧
    execCheckCost (env 2 20 8 3) (optimizeExpr .top nestedNum) = 1 := by
  decide

theorem nested_numerator_zero_traps :
    evalExpr (env 0 20 8 3) nestedNum = .trap ∧
    evalExpr (env 0 20 8 3) (optimizeExpr .top nestedNum) = .trap := by
  decide

theorem nested_numerator_negative :
    evalExpr (env (-3) (-8) 9 2) nestedNum = .val (-1) ∧
    evalExpr (env (-3) (-8) 9 2) (optimizeExpr .top nestedNum) = .val (-1) := by
  decide

/-- A nonzero inner divisor does not establish that the inner quotient is nonzero. -/
theorem nested_denominator_positive :
    evalExpr (env 2 20 8 3) nestedDen = .val 5 ∧
    evalExpr (env 2 20 8 3) (optimizeExpr .top nestedDen) = .val 5 ∧
    evalGuard (env 2 20 8 3) nz = true ∧
    evalExpr (env 2 20 8 3) (optimizeExpr nz nestedDen) = .val 5 ∧
    checkedDivCount (optimizeExpr nz nestedDen) = 1 := by
  decide

theorem zero_quotient_retains_outer_trap :
    evalGuard (env 2 20 1 3) nz = true ∧
    evalExpr (env 2 20 1 3) nestedDen = .trap ∧
    evalExpr (env 2 20 1 3) (optimizeExpr nz nestedDen) = .trap ∧
    execCheckCost (env 2 20 1 3) (optimizeExpr nz nestedDen) = 1 := by
  decide

theorem nested_denominator_zero_traps :
    evalExpr (env 0 20 8 3) nestedDen = .trap ∧
    evalExpr (env 0 20 8 3) (optimizeExpr .top nestedDen) = .trap := by
  decide

/-- Evidence about variable 0 must not discharge a check of variable 3. -/
theorem distinct_divisors_stay_independent :
    checkedDivCount (optimizeExpr .top differentDivisors) = 2 ∧
    evalExpr (env 2 7 8 3) differentDivisors = .val 5 ∧
    evalExpr (env 2 7 8 3) (optimizeExpr .top differentDivisors) = .val 5 ∧
    evalExpr (env 2 7 8 0) differentDivisors = .trap ∧
    evalExpr (env 2 7 8 0) (optimizeExpr .top differentDivisors) = .trap := by
  decide

/-- Cancellation must not discard a trapping expression hidden in its numerator. -/
theorem nonpure_numerator_is_not_cancelled :
    evalGuard (env 2 20 8 3) nz = true ∧
    evalExpr (env 2 20 8 3) numeratorTrap = .trap ∧
    evalExpr (env 2 20 8 3) (optimizeExpr nz numeratorTrap) = .trap ∧
    checkedDivCount (optimizeExpr nz numeratorTrap) = 1 := by
  decide

/-- Euclidean division is tested with negative dividends and either divisor sign. -/
theorem negative_division_cases :
    evalExpr (env 0 0 0 0) (.checkedDiv (lit (-7)) (lit 3)) = .val (-3) ∧
    evalExpr (env 0 0 0 0) (optimizeExpr .top (.checkedDiv (lit (-7)) (lit 3))) = .val (-3) ∧
    evalExpr (env 0 0 0 0) (.checkedDiv (lit 7) (lit (-3))) = .val (-2) ∧
    evalExpr (env 0 0 0 0) (optimizeExpr .top (.checkedDiv (lit 7) (lit (-3)))) = .val (-2) ∧
    evalExpr (env 0 0 0 0) (.checkedDiv (lit (-7)) (lit (-3))) = .val 3 ∧
    evalExpr (env 0 0 0 0)
      (optimizeExpr (.nonZero (.lit (-3))) (.checkedDiv (lit (-7)) (lit (-3)))) = .val 3 := by
  decide

theorem signed_cancellation_both_orders :
    evalGuard (env (-3) (-4) 0 0) nz = true ∧
    evalExpr (env (-3) (-4) 0 0) (mkCancelExpr (.sub (.var 1) (.lit 3)) (.var 0)) = .val (-7) ∧
    evalExpr (env (-3) (-4) 0 0)
      (optimizeExpr nz (mkCancelExpr (.sub (.var 1) (.lit 3)) (.var 0))) = .val (-7) ∧
    evalExpr (env (-3) (-4) 0 0) (optimizeExpr nz reverseCancel) = .val (-7) ∧
    divOpCount (optimizeExpr nz reverseCancel) = 0 := by
  decide

/-- Pure arithmetic recovered from expression nodes can serve as a known denominator. -/
theorem arithmetic_denominator_recovery :
    evalGuard (env 4 20 0 0) (.nonZero (.sub (.var 0) (.lit 1))) = true ∧
    evalExpr (env 4 20 0 0) arithmeticDenominator = .val 6 ∧
    evalExpr (env 4 20 0 0)
      (optimizeExpr (.nonZero (.sub (.var 0) (.lit 1))) arithmeticDenominator) = .val 6 ∧
    checkedDivCount (optimizeExpr (.nonZero (.sub (.var 0) (.lit 1))) arithmeticDenominator) = 0 ∧
    evalExpr (env 1 20 0 0) (optimizeExpr .top arithmeticDenominator) = .trap := by
  decide

/-- Nested subtraction/multiplication, compound pure operands, and unrelated variable identifiers. -/
theorem nonbenchmark_compound_reduction :
    evalGuard (env 2 20 8 6) compoundCtx = true ∧
    evalExpr (env 2 20 8 6) compound = .val 15 ∧
    evalExpr (env 2 20 8 6) (optimizeExpr .top compound) = .val 15 ∧
    checkedDivCount compound = 2 ∧ checkedDivCount (optimizeExpr .top compound) = 1 ∧
    execCheckCost (env 2 20 8 6) (optimizeExpr .top compound) = 1 ∧
    evalExpr (env 2 20 8 6) (optimizeExpr compoundCtx compound) = .val 15 ∧
    checkedDivCount (optimizeExpr compoundCtx compound) = 0 ∧
    guardBranchCount (optimizeExpr compoundCtx compound) = 0 ∧
    execCheckCost (env 2 20 8 6) (optimizeExpr compoundCtx compound) = 0 := by
  decide

/-- A successful unchecked operation may justify a later check removal; existing UB remains UB. -/
theorem unchecked_left_success_and_failure :
    evalExpr (env 2 7 8 3) reuseUnchecked = .val 7 ∧
    evalExpr (env 2 7 8 3) (optimizeExpr .top reuseUnchecked) = .val 7 ∧
    checkedDivCount (optimizeExpr .top reuseUnchecked) = 0 ∧
    evalExpr (env 0 7 8 3) reuseUnchecked = .ub ∧
    evalExpr (env 0 7 8 3) (optimizeExpr .top reuseUnchecked) = .ub := by
  decide

theorem zero_times_failure_is_strict :
    evalExpr (env 0 0 0 0) (optimizeExpr .top (.mul (lit 0) trapExpr)) = .trap ∧
    evalExpr (env 0 0 0 0) (optimizeExpr .top (.mul (lit 0) ubExpr)) = .ub := by
  decide

theorem failure_order_is_preserved :
    evalExpr (env 0 0 0 0) (optimizeExpr .top (.add trapExpr ubExpr)) = .trap ∧
    evalExpr (env 0 0 0 0) (optimizeExpr .top (.add ubExpr trapExpr)) = .ub ∧
    evalExpr (env 0 0 0 0) (optimizeExpr .top (.checkedDiv trapExpr (lit 0))) = .trap ∧
    evalExpr (env 0 0 0 0) (optimizeExpr .top (.checkedDiv (lit 1) trapExpr)) = .trap := by
  decide

/-- Cancellation is enabled inside the true branch while its zero-divisor fallback still traps. -/
theorem guard_branch_contexts :
    evalExpr (env 2 7 0 0) guardedCancellation = .val 7 ∧
    evalExpr (env 2 7 0 0) (optimizeExpr .top guardedCancellation) = .val 7 ∧
    execCheckCost (env 2 7 0 0) guardedCancellation = 2 ∧
    execCheckCost (env 2 7 0 0) (optimizeExpr .top guardedCancellation) = 1 ∧
    evalExpr (env 0 7 0 0) (optimizeExpr .top guardedCancellation) = .trap ∧
    evalExpr (env 0 0 0 0) (optimizeExpr .top (.iteGuard .bot ubExpr (lit 7))) = .val 7 := by
  decide

/-- A fact from a potentially unexecuted branch must not be used for the following division. -/
theorem conditional_facts_do_not_leak :
    evalExpr (env 0 7 8 0) branchFactsMustNotLeak = .trap ∧
    evalExpr (env 0 7 8 0) (optimizeExpr .top branchFactsMustNotLeak) = .trap ∧
    checkedDivCount (optimizeExpr .top branchFactsMustNotLeak) = 2 := by
  decide

/-- Conservative precision: common successful facts of both branches are not joined. -/
theorem branch_join_precision_limit :
    evalExpr (env 2 8 4 1) (optimizeExpr .top bothBranchesCheck) = .val 8 ∧
    execCheckCost (env 2 8 4 1) (optimizeExpr .top bothBranchesCheck) = 3 := by
  decide

/-- A bounded semantic sweep complements the exact-value and reduction witnesses above. -/
def testEnvs : List Env :=
  [env 2 20 8 3, env 2 20 1 0, env 0 20 8 3, env (-3) (-8) 9 (-2),
   env (-3) 7 0 0, env 1 (-7) 0 1, env 2 (-7) (-1) 6, env 0 0 0 0]
def testContexts : List GuardIR :=
  [.top, nz, .nonZero compoundD, compoundCtx, .conj nz (.nonZero (.var 3)), .imp nz .bot]
def testExprs : List Expr :=
  [nestedNum, nestedDen, differentDivisors, numeratorTrap, compound, arithmeticDenominator,
   reuseUnchecked, guardedCancellation, branchFactsMustNotLeak, bothBranchesCheck,
   .mul (lit 0) trapExpr, .mul (lit 0) ubExpr, .add trapExpr ubExpr, .add ubExpr trapExpr,
   mkCancelExpr (.sub (.var 1) (.lit 3)) (.var 0), reverseCancel]
def agreesWhenContext (rho : Env) (ctx : GuardIR) (e : Expr) : Bool :=
  (!evalGuard rho ctx) || decide (evalExpr rho (optimizeExpr ctx e) = evalExpr rho e)

theorem sweep_dimensions :
    testEnvs.length = 8 ∧ testContexts.length = 6 ∧ testExprs.length = 16 := by
  decide

theorem concrete_semantic_sweep :
    testEnvs.all (fun rho =>
      testContexts.all (fun ctx => testExprs.all (agreesWhenContext rho ctx))) = true := by
  decide

end CatSem.PostImplAudit

-- Explicit dependency reports for the submitted public API and every audit declaration.
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
#print axioms CatSem.synthesizeGuardIR
#print axioms CatSem.optimizeExpr
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
#print axioms CatSem.PostImplAudit.env
#print axioms CatSem.PostImplAudit.lit
#print axioms CatSem.PostImplAudit.v
#print axioms CatSem.PostImplAudit.nz
#print axioms CatSem.PostImplAudit.trapExpr
#print axioms CatSem.PostImplAudit.ubExpr
#print axioms CatSem.PostImplAudit.nestedNum
#print axioms CatSem.PostImplAudit.nestedDen
#print axioms CatSem.PostImplAudit.differentDivisors
#print axioms CatSem.PostImplAudit.numeratorTrap
#print axioms CatSem.PostImplAudit.reuseUnchecked
#print axioms CatSem.PostImplAudit.arithmeticDenominator
#print axioms CatSem.PostImplAudit.compoundD
#print axioms CatSem.PostImplAudit.compoundX
#print axioms CatSem.PostImplAudit.compoundY
#print axioms CatSem.PostImplAudit.compound
#print axioms CatSem.PostImplAudit.compoundCtx
#print axioms CatSem.PostImplAudit.guardedCancellation
#print axioms CatSem.PostImplAudit.branchFactsMustNotLeak
#print axioms CatSem.PostImplAudit.bothBranchesCheck
#print axioms CatSem.PostImplAudit.reverseCancel
#print axioms CatSem.PostImplAudit.guard_normalization
#print axioms CatSem.PostImplAudit.residual_truth_cases
#print axioms CatSem.PostImplAudit.conservative_atomic_reasoning
#print axioms CatSem.PostImplAudit.nested_numerator_positive
#print axioms CatSem.PostImplAudit.nested_numerator_zero_traps
#print axioms CatSem.PostImplAudit.nested_numerator_negative
#print axioms CatSem.PostImplAudit.nested_denominator_positive
#print axioms CatSem.PostImplAudit.zero_quotient_retains_outer_trap
#print axioms CatSem.PostImplAudit.nested_denominator_zero_traps
#print axioms CatSem.PostImplAudit.distinct_divisors_stay_independent
#print axioms CatSem.PostImplAudit.nonpure_numerator_is_not_cancelled
#print axioms CatSem.PostImplAudit.negative_division_cases
#print axioms CatSem.PostImplAudit.signed_cancellation_both_orders
#print axioms CatSem.PostImplAudit.arithmetic_denominator_recovery
#print axioms CatSem.PostImplAudit.nonbenchmark_compound_reduction
#print axioms CatSem.PostImplAudit.unchecked_left_success_and_failure
#print axioms CatSem.PostImplAudit.zero_times_failure_is_strict
#print axioms CatSem.PostImplAudit.failure_order_is_preserved
#print axioms CatSem.PostImplAudit.guard_branch_contexts
#print axioms CatSem.PostImplAudit.conditional_facts_do_not_leak
#print axioms CatSem.PostImplAudit.branch_join_precision_limit
#print axioms CatSem.PostImplAudit.testEnvs
#print axioms CatSem.PostImplAudit.testContexts
#print axioms CatSem.PostImplAudit.testExprs
#print axioms CatSem.PostImplAudit.agreesWhenContext
#print axioms CatSem.PostImplAudit.sweep_dimensions
#print axioms CatSem.PostImplAudit.concrete_semantic_sweep


/-!
Milestone 2 Gate 2 implementation audit for submission
a113c8855634580c0a4d8fb84ed50d15b77e757ca99156ac1af66313dffe5be8.
The preceding Milestone 1 tests are retained unchanged.
These tests compute with the public compiler functions and independent evaluator.
-/
namespace CatSem.PostImplAudit.M2

/-- Save x in two fresh variables, clobber both sources, then reassign from the saved copy. -/
def aliasSteps : Stmt :=
  .seq (.assign 7 (.var 1))
    (.seq (.assign 9 (.var 7))
      (.seq (.assign 1 (.lit 0))
        (.seq (.assign 7 (.lit 0))
          (.assign 0 (.mul (.var 9) (.lit (-1)))))))
def aliasBlock : BlockProg :=
  { body := aliasSteps, ret := mkDualDivExpr (.lit (-7)) (.lit 5) (.var 0) }
def xnz : GuardIR := .nonZero (.var 1)

/-- The second assignment kills a saved fact despite a true entry context. -/
def clobberSteps : Stmt :=
  .seq (.assign 7 (.var 1))
    (.seq (.assign 1 (.lit 0))
      (.seq (.assign 7 (.var 1)) (.assign 0 (.var 7))))
def clobberBlock : BlockProg :=
  {body := clobberSteps, ret := mkDualDivExpr (.lit (-7)) (.lit 5) (.var 0)}

/-- Distinct arms establish the same nonzero postcondition by different arithmetic. -/
def asymmetricSteps : Stmt :=
  .ite (.eq (.var 1) (.lit 0))
    (.seq (.assign 7 (.lit (-2))) (.assign 0 (.mul (.var 7) (.lit 3))))
    (.seq (.assign 9 (.var 1)) (.assign 0 (.mul (.var 9) (.lit (-1)))))
def asymmetricBlock : BlockProg :=
  {body := asymmetricSteps, ret := mkDualDivExpr (.lit (-7)) (.lit 5) (.var 0)}

/-- Only one arm establishes nonzeroness: facts must not escape that arm. -/
def partialDiamond : BlockProg :=
  {body := .ite (.nonZero (.var 1)) (.assign 0 (.lit (-2))) (.assign 0 (.lit 0)),
   ret := mkDualDivExpr (.lit (-7)) (.lit 5) (.var 0)}

/-- A branch initially testing x != 0 writes x := 0 before testing x again. -/
def changedPathSteps : Stmt :=
  .ite (.nonZero (.var 1))
    (.seq (.assign 1 (.lit 0))
      (.ite (.nonZero (.var 1)) (.assign 0 (.lit 0)) (.assign 0 (.lit (-3)))))
    (.seq (.assign 1 (.lit 2))
      (.ite (.eq (.var 1) (.lit 0)) (.assign 0 (.lit 0)) (.assign 0 (.lit 4))))
def changedPathBlock : BlockProg :=
  {body := changedPathSteps, ret := mkDualDivExpr (.lit (-7)) (.lit 5) (.var 0)}

/-- Inner conditions are entailed by the outer path, without a constant assignment. -/
def correlatedSteps : Stmt :=
  .ite (.nonZero (.var 1))
    (.ite (.nonZero (.var 1)) (.assign 0 (.var 1)) (.assign 0 (.lit 0)))
    (.ite (.nonZero (.var 1)) (.assign 0 (.lit 0)) (.assign 0 (.lit (-2))))
def correlatedBlock : BlockProg :=
  {body := correlatedSteps, ret := mkDualDivExpr (.lit (-7)) (.lit 5) (.var 0)}

/-- A branch pruned under a true context mutates the variable in that context. -/
def mutatingDeadBlock : BlockProg :=
  {body := .ite xnz
      (.seq (.assign 1 (.lit 0)) (.assign 0 (.lit (-3))))
      (.assign 0 (.lit 0)),
   ret := mkCancelExpr (.add (.var 1) (.lit (-7))) (.var 0)}

/-- The context proves a false branch, including after a prefix changes the state. -/
def falseBranchBlock : BlockProg :=
  {body := .seq (.assign 1 (.lit 0))
      (.ite xnz (.assign 0 (.lit 0)) (.assign 0 (.lit (-2)))),
   ret := mkCancelExpr (.lit (-7)) (.var 0)}

/-- Source and destination coincide; guards and RHSs must still read the old state. -/
def selfAliasBlock : BlockProg :=
  {body := .ite (.eq (.var 1) (.lit 0))
      (.assign 1 (.lit (-2))) (.assign 1 (.mul (.var 1) (.lit (-1)))),
   ret := mkDualDivExpr (.lit (-7)) (.lit 5) (.var 1)}

/-- Candidates include non-pure AST encodings of pure divisors and return guard atoms. -/
def returnGuardBlock : BlockProg :=
  {body := .seq (.assign 7 (.lit (-3))) (.assign 9 (.lit (-2))),
   ret := .iteGuard (.eq (.var 7) (.lit (-3)))
     (.sub (.checkedDiv (lit (-7)) (.add (v 9) (lit (-1))))
       (mkCancelExpr (.lit 4) (.add (.var 9) (.lit (-1)))))
     trapExpr}

/-- Nonzero atomic inference is deliberately conservative for variable arithmetic. -/
def conservativeBlock : BlockProg :=
  {body := .assign 0 (.add (.sub (.var 1) (.var 1)) (.lit 1)),
   ret := .checkedDiv (lit (-7)) (v 0)}

/-- Existing UB and failure order remain observable after a statement clobber. -/
def failureBlock (ret : Expr) : BlockProg :=
  {body := clobberSteps, ret := ret}

theorem self_assignment_is_simultaneous :
    pullbackGuardIR (.assign 1 (.add (.var 1) (.lit 1))) (.eq (.var 1) (.lit 0)) =
      .eq (.add (.var 1) (.lit 1)) (.lit 0) ∧
    evalGuard (env 4 (-1) 0 0)
      (pullbackGuardIR (.assign 1 (.add (.var 1) (.lit 1))) (.eq (.var 1) (.lit 0))) = true ∧
    evalGuard (env 4 0 0 0)
      (pullbackGuardIR (.assign 1 (.add (.var 1) (.lit 1))) (.eq (.var 1) (.lit 0))) = false := by
  decide

theorem multistep_aliasing_and_signed_reassignment :
    evalGuard (env 4 3 0 0) xnz = true ∧
    execStmt aliasSteps (env 4 3 0 0) 1 = 0 ∧
    execStmt aliasSteps (env 4 3 0 0) 7 = 0 ∧
    execStmt aliasSteps (env 4 3 0 0) 9 = 3 ∧
    execStmt aliasSteps (env 4 3 0 0) 0 = -3 ∧
    pullbackGuardIR aliasSteps nz = .nonZero (.mul (.var 1) (.lit (-1))) ∧
    synthesizeStmtGuardIR aliasSteps xnz nz = .top ∧
    evalBlock (env 4 3 0 0) aliasBlock = .val 8 ∧
    evalBlock (env 4 3 0 0) (optimizeBlock xnz aliasBlock) = .val 8 ∧
    evalBlock (env 4 (-3) 0 0) aliasBlock = .val 2 ∧
    evalBlock (env 4 (-3) 0 0) (optimizeBlock xnz aliasBlock) = .val 2 ∧
    checkedDivCount (optimizeBlock xnz aliasBlock).ret = 0 ∧
    divOpCount (optimizeBlock xnz aliasBlock).ret = 1 ∧
    execBlockCheckCost (env 4 3 0 0) aliasBlock = 2 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock xnz aliasBlock) = 0 := by
  decide

theorem clobbered_fact_is_rejected :
    evalGuard (env 4 3 0 0) (.conj xnz nz) = true ∧
    execStmt clobberSteps (env 4 3 0 0) 0 = 0 ∧
    evalGuard (env 4 3 0 0)
      (synthesizeStmtGuardIR clobberSteps (.conj xnz nz) nz) = false ∧
    evalBlock (env 4 3 0 0) clobberBlock = .trap ∧
    evalBlock (env 4 3 0 0) (optimizeBlock (.conj xnz nz) clobberBlock) = .trap ∧
    checkedDivCount (optimizeBlock (.conj xnz nz) clobberBlock).ret = 1 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock (.conj xnz nz) clobberBlock) = 1 := by
  decide

theorem residual_guard_truth_table :
    evalGuard (env 4 0 0 0)
      (synthesizeStmtGuardIR (.assign 0 (.var 1)) (.nonZero (.var 2)) nz) = true ∧
    evalGuard (env 4 0 2 0)
      (synthesizeStmtGuardIR (.assign 0 (.var 1)) (.nonZero (.var 2)) nz) = false ∧
    evalGuard (env 4 (-3) 2 0)
      (synthesizeStmtGuardIR (.assign 0 (.var 1)) (.nonZero (.var 2)) nz) = true := by
  decide

theorem arithmetic_guard_normalization :
    synthesizeStmtGuardIR .skip .top (.nonZero (.sub (.lit (-2)) (.lit 1))) = .top ∧
    synthesizeStmtGuardIR .skip (.eq (.lit (-3)) (.var 1)) xnz = .top ∧
    synthesizeStmtGuardIR .skip (.eq (.var 1) (.lit (-3))) xnz = .top ∧
    synthesizeStmtGuardIR .skip (.nonZero (.mul (.var 1) (.var 2))) xnz = .top ∧
    synthesizeStmtGuardIR .skip (.conj xnz (.nonZero (.var 2)))
      (.nonZero (.mul (.var 1) (.var 2))) = .top := by
  decide

theorem asymmetric_diamond_join :
    synthesizeStmtGuardIR asymmetricSteps .top nz = .top ∧
    evalBlock (env 4 0 0 0) asymmetricBlock = .val 7 ∧
    evalBlock (env 4 0 0 0) (optimizeBlock .top asymmetricBlock) = .val 7 ∧
    evalBlock (env 4 3 0 0) asymmetricBlock = .val 8 ∧
    evalBlock (env 4 3 0 0) (optimizeBlock .top asymmetricBlock) = .val 8 ∧
    evalBlock (env 4 (-3) 0 0) asymmetricBlock = .val 2 ∧
    evalBlock (env 4 (-3) 0 0) (optimizeBlock .top asymmetricBlock) = .val 2 ∧
    checkedDivCount (optimizeBlock .top asymmetricBlock).ret = 0 ∧
    divOpCount (optimizeBlock .top asymmetricBlock).ret = 1 ∧
    guardBranchCount (optimizeBlock .top asymmetricBlock).ret = 0 ∧
    execBlockCheckCost (env 4 0 0 0) asymmetricBlock = 3 ∧
    execBlockCheckCost (env 4 0 0 0) (optimizeBlock .top asymmetricBlock) = 1 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock .top asymmetricBlock) = 1 := by
  decide

theorem partial_diamond_preserves_trapping_arm :
    evalGuard (env 4 0 0 0) (synthesizeStmtGuardIR partialDiamond.body .top nz) = false ∧
    evalGuard (env 4 3 0 0) (synthesizeStmtGuardIR partialDiamond.body .top nz) = true ∧
    evalBlock (env 4 0 0 0) partialDiamond = .trap ∧
    evalBlock (env 4 0 0 0) (optimizeBlock .top partialDiamond) = .trap ∧
    evalBlock (env 4 3 0 0) partialDiamond = .val 9 ∧
    evalBlock (env 4 3 0 0) (optimizeBlock .top partialDiamond) = .val 9 ∧
    checkedDivCount (optimizeBlock .top partialDiamond).ret = 1 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock .top partialDiamond) = 2 ∧
    evalGuard (env 4 3 0 0) xnz = true ∧
    evalBlock (env 4 3 0 0) (optimizeBlock xnz partialDiamond) = .val 9 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock xnz partialDiamond) = 0 := by
  decide

theorem nested_condition_uses_reassigned_state :
    (optimizeBlock .top changedPathBlock).body =
      .ite xnz
        (.seq (.assign 1 (.lit 0)) (.assign 0 (.lit (-3))))
        (.seq (.assign 1 (.lit 2)) (.assign 0 (.lit 4))) ∧
    synthesizeStmtGuardIR changedPathSteps .top nz = .top ∧
    evalBlock (env 4 3 0 0) changedPathBlock = .val 8 ∧
    evalBlock (env 4 3 0 0) (optimizeBlock .top changedPathBlock) = .val 8 ∧
    evalBlock (env 4 0 0 0) changedPathBlock = .val 3 ∧
    evalBlock (env 4 0 0 0) (optimizeBlock .top changedPathBlock) = .val 3 ∧
    execBlockCheckCost (env 4 3 0 0) changedPathBlock = 4 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock .top changedPathBlock) = 1 ∧
    execBlockCheckCost (env 4 0 0 0) (optimizeBlock .top changedPathBlock) = 1 := by
  decide

theorem correlated_paths_prune_nested_dead_arms :
    (optimizeBlock .top correlatedBlock).body =
      .ite xnz (.assign 0 (.var 1)) (.assign 0 (.lit (-2))) ∧
    synthesizeStmtGuardIR correlatedSteps .top nz = .top ∧
    evalBlock (env 4 3 0 0) correlatedBlock = .val 2 ∧
    evalBlock (env 4 3 0 0) (optimizeBlock .top correlatedBlock) = .val 2 ∧
    evalBlock (env 4 0 0 0) correlatedBlock = .val 9 ∧
    evalBlock (env 4 0 0 0) (optimizeBlock .top correlatedBlock) = .val 9 ∧
    execBlockCheckCost (env 4 3 0 0) correlatedBlock = 4 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock .top correlatedBlock) = 1 := by
  decide

theorem dead_branch_context_can_be_killed :
    evalGuard (env 4 3 0 0) xnz = true ∧
    evalGuard (execStmt mutatingDeadBlock.body (env 4 3 0 0)) xnz = false ∧
    (optimizeBlock xnz mutatingDeadBlock).body =
      .seq (.assign 1 (.lit 0)) (.assign 0 (.lit (-3))) ∧
    (optimizeBlock xnz mutatingDeadBlock).ret = .pure (.add (.var 1) (.lit (-7))) ∧
    evalBlock (env 4 3 0 0) mutatingDeadBlock = .val (-7) ∧
    evalBlock (env 4 3 0 0) (optimizeBlock xnz mutatingDeadBlock) = .val (-7) ∧
    execBlockCheckCost (env 4 3 0 0) mutatingDeadBlock = 2 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock xnz mutatingDeadBlock) = 0 := by
  decide

theorem prefix_proves_false_branch :
    (optimizeBlock .top falseBranchBlock).body =
      .seq (.assign 1 (.lit 0)) (.assign 0 (.lit (-2))) ∧
    evalBlock (env 4 3 0 0) falseBranchBlock = .val (-7) ∧
    evalBlock (env 4 3 0 0) (optimizeBlock .top falseBranchBlock) = .val (-7) ∧
    divOpCount (optimizeBlock .top falseBranchBlock).ret = 0 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock .top falseBranchBlock) = 0 := by
  decide

theorem diamond_source_destination_alias :
    evalBlock (env 4 0 0 0) selfAliasBlock = .val 9 ∧
    evalBlock (env 4 0 0 0) (optimizeBlock .top selfAliasBlock) = .val 9 ∧
    evalBlock (env 4 3 0 0) selfAliasBlock = .val 8 ∧
    evalBlock (env 4 3 0 0) (optimizeBlock .top selfAliasBlock) = .val 8 ∧
    checkedDivCount (optimizeBlock .top selfAliasBlock).ret = 0 ∧
    execBlockCheckCost (env 4 0 0 0) (optimizeBlock .top selfAliasBlock) = 1 := by
  decide

theorem terminal_guard_and_compound_divisor :
    evalBlock (env 4 3 0 0) returnGuardBlock = .val (-1) ∧
    evalBlock (env 4 3 0 0) (optimizeBlock .top returnGuardBlock) = .val (-1) ∧
    checkedDivCount (optimizeBlock .top returnGuardBlock).ret = 0 ∧
    guardBranchCount (optimizeBlock .top returnGuardBlock).ret = 0 ∧
    divOpCount (optimizeBlock .top returnGuardBlock).ret = 1 ∧
    execBlockCheckCost (env 4 3 0 0) returnGuardBlock = 3 ∧
    execBlockCheckCost (env 4 3 0 0) (optimizeBlock .top returnGuardBlock) = 0 := by
  decide

theorem clobbered_failure_order_and_existing_ub :
    evalGuard (env 4 3 0 0) (.conj xnz nz) = true ∧
    evalBlock (env 4 3 0 0)
      (failureBlock (.add (.checkedDiv (lit (-7)) (v 0)) ubExpr)) = .trap ∧
    evalBlock (env 4 3 0 0)
      (optimizeBlock (.conj xnz nz)
        (failureBlock (.add (.checkedDiv (lit (-7)) (v 0)) ubExpr))) = .trap ∧
    evalBlock (env 4 3 0 0)
      (failureBlock (.add ubExpr (.checkedDiv (lit (-7)) (v 0)))) = .ub ∧
    evalBlock (env 4 3 0 0)
      (optimizeBlock (.conj xnz nz)
        (failureBlock (.add ubExpr (.checkedDiv (lit (-7)) (v 0))))) = .ub ∧
    evalBlock (env 4 3 0 0)
      (failureBlock (.uncheckedDiv (lit (-7)) (v 0))) = .ub ∧
    evalBlock (env 4 3 0 0)
      (optimizeBlock (.conj xnz nz) (failureBlock (.uncheckedDiv (lit (-7)) (v 0)))) = .ub := by
  decide

/-- General soundness does not promise a complete polynomial arithmetic solver. -/
theorem conservative_arithmetic_precision :
    synthesizeStmtGuardIR conservativeBlock.body .top nz =
      .nonZero (.add (.sub (.var 1) (.var 1)) (.lit 1)) ∧
    checkedDivCount (optimizeBlock .top conservativeBlock).ret = 1 ∧
    evalBlock (env 4 (-3) 0 0) conservativeBlock = .val (-7) ∧
    evalBlock (env 4 (-3) 0 0) (optimizeBlock .top conservativeBlock) = .val (-7) := by
  decide


def states : List Env :=
  [env 4 3 2 1, env 0 0 0 0, env (-2) (-3) 5 (-1),
   env 4 (-1) 0 (-2), env 3 1 (-1) 0, env (-3) 0 2 7]
def contexts : List GuardIR :=
  [.top, xnz, .conj xnz nz, .eq (.var 1) (.lit 0), .nonZero (.mul (.var 1) (.var 2))]
def guards : List GuardIR :=
  [.top, .bot, xnz, nz, .eq (.var 1) (.lit 0), .eq (.var 1) (.lit (-3)),
   .nonZero (.mul (.var 1) (.var 2)), .imp (.nonZero (.var 2)) nz]
def statements : List Stmt :=
  [.skip, .assign 1 (.add (.var 1) (.lit 1)), aliasSteps, clobberSteps,
   asymmetricSteps, changedPathSteps, correlatedSteps, partialDiamond.body,
   mutatingDeadBlock.body, falseBranchBlock.body, selfAliasBlock.body,
   returnGuardBlock.body, conservativeBlock.body]
def blocks : List BlockProg :=
  [aliasBlock, clobberBlock, asymmetricBlock, partialDiamond, changedPathBlock,
   correlatedBlock, mutatingDeadBlock, falseBranchBlock, selfAliasBlock,
   returnGuardBlock, conservativeBlock,
   failureBlock (.add (.checkedDiv (lit (-7)) (v 0)) ubExpr),
   failureBlock (.add ubExpr (.checkedDiv (lit (-7)) (v 0))),
   failureBlock (.uncheckedDiv (lit (-7)) (v 0))]
def pullbackAgrees (rho : Env) (s : Stmt) (g : GuardIR) : Bool :=
  decide (evalGuard rho (pullbackGuardIR s g) = evalGuard (execStmt s rho) g)
def synthesisAgrees (rho : Env) (s : Stmt) (ctx g : GuardIR) : Bool :=
  decide (evalGuard rho (synthesizeStmtGuardIR s ctx g) =
    (!evalGuard rho ctx || evalGuard (execStmt s rho) g))
def blockAgrees (rho : Env) (ctx : GuardIR) (p : BlockProg) : Bool :=
  (!evalGuard rho ctx) || decide (evalBlock rho (optimizeBlock ctx p) = evalBlock rho p)

theorem sweep_sizes :
    states.length = 6 ∧ contexts.length = 5 ∧ guards.length = 8 ∧
    statements.length = 13 ∧ blocks.length = 14 := by
  decide

/-- Every tested entry context has a concrete satisfying state in the sweep. -/
theorem sweep_contexts_are_inhabited :
    contexts.all (fun ctx => states.any (fun rho => evalGuard rho ctx)) = true := by
  decide

theorem pullback_semantic_sweep :
    states.all (fun rho => statements.all (fun s =>
      guards.all (pullbackAgrees rho s))) = true := by
  decide

/-- Tests false as well as true antecedents, without filtering out either case. -/
theorem synthesis_semantic_sweep :
    states.all (fun rho => statements.all (fun s => contexts.all (fun ctx =>
      guards.all (synthesisAgrees rho s ctx)))) = true := by
  decide

theorem block_semantic_sweep :
    states.all (fun rho => contexts.all (fun ctx =>
      blocks.all (blockAgrees rho ctx))) = true := by
  decide

end CatSem.PostImplAudit.M2

-- M2 compiler API and transitive dependency reports for every new audit declaration.
#print axioms CatSem.pullbackGuardIR
#print axioms CatSem.synthesizeStmtGuardIR
#print axioms CatSem.optimizeBlock
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
#print axioms CatSem.PostImplAudit.M2.aliasSteps
#print axioms CatSem.PostImplAudit.M2.aliasBlock
#print axioms CatSem.PostImplAudit.M2.xnz
#print axioms CatSem.PostImplAudit.M2.clobberSteps
#print axioms CatSem.PostImplAudit.M2.clobberBlock
#print axioms CatSem.PostImplAudit.M2.asymmetricSteps
#print axioms CatSem.PostImplAudit.M2.asymmetricBlock
#print axioms CatSem.PostImplAudit.M2.partialDiamond
#print axioms CatSem.PostImplAudit.M2.changedPathSteps
#print axioms CatSem.PostImplAudit.M2.changedPathBlock
#print axioms CatSem.PostImplAudit.M2.correlatedSteps
#print axioms CatSem.PostImplAudit.M2.correlatedBlock
#print axioms CatSem.PostImplAudit.M2.mutatingDeadBlock
#print axioms CatSem.PostImplAudit.M2.falseBranchBlock
#print axioms CatSem.PostImplAudit.M2.selfAliasBlock
#print axioms CatSem.PostImplAudit.M2.returnGuardBlock
#print axioms CatSem.PostImplAudit.M2.conservativeBlock
#print axioms CatSem.PostImplAudit.M2.failureBlock
#print axioms CatSem.PostImplAudit.M2.self_assignment_is_simultaneous
#print axioms CatSem.PostImplAudit.M2.multistep_aliasing_and_signed_reassignment
#print axioms CatSem.PostImplAudit.M2.clobbered_fact_is_rejected
#print axioms CatSem.PostImplAudit.M2.residual_guard_truth_table
#print axioms CatSem.PostImplAudit.M2.arithmetic_guard_normalization
#print axioms CatSem.PostImplAudit.M2.asymmetric_diamond_join
#print axioms CatSem.PostImplAudit.M2.partial_diamond_preserves_trapping_arm
#print axioms CatSem.PostImplAudit.M2.nested_condition_uses_reassigned_state
#print axioms CatSem.PostImplAudit.M2.correlated_paths_prune_nested_dead_arms
#print axioms CatSem.PostImplAudit.M2.dead_branch_context_can_be_killed
#print axioms CatSem.PostImplAudit.M2.prefix_proves_false_branch
#print axioms CatSem.PostImplAudit.M2.diamond_source_destination_alias
#print axioms CatSem.PostImplAudit.M2.terminal_guard_and_compound_divisor
#print axioms CatSem.PostImplAudit.M2.clobbered_failure_order_and_existing_ub
#print axioms CatSem.PostImplAudit.M2.conservative_arithmetic_precision
#print axioms CatSem.PostImplAudit.M2.states
#print axioms CatSem.PostImplAudit.M2.contexts
#print axioms CatSem.PostImplAudit.M2.guards
#print axioms CatSem.PostImplAudit.M2.statements
#print axioms CatSem.PostImplAudit.M2.blocks
#print axioms CatSem.PostImplAudit.M2.pullbackAgrees
#print axioms CatSem.PostImplAudit.M2.synthesisAgrees
#print axioms CatSem.PostImplAudit.M2.blockAgrees
#print axioms CatSem.PostImplAudit.M2.sweep_sizes
#print axioms CatSem.PostImplAudit.M2.sweep_contexts_are_inhabited
#print axioms CatSem.PostImplAudit.M2.pullback_semantic_sweep
#print axioms CatSem.PostImplAudit.M2.synthesis_semantic_sweep
#print axioms CatSem.PostImplAudit.M2.block_semantic_sweep
