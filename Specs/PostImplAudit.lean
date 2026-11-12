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

/-!
Milestone 3 Gate 2 implementation audit for submission
ba5aeefca9f932707e8e24ca27029ce2717882a48ab2dc68f1b13103528fc5bf.
The preceding Milestone 1 and Milestone 2 audits are retained unchanged.
Every computation below uses the submitted public compiler and the independent
operational evaluator; no target stubs or custom elaborator syntax are used.
-/
namespace CatSem.PostImplAudit.M3

def nzAt (v : VarId) : GuardIR := .nonZero (.var v)
def counted : WhileLoop := mkCountedDivLoop 0 1 2 3 (.lit 8) (.lit 5)
def versionBodyChecks : LoopProg → Option (Nat × Nat)
  | .iteLoop _ (.whileLoop t) (.whileLoop f) => some (checkedDivCount t.body, checkedDivCount f.body)
  | _ => none
def versionGuard : LoopProg → Option GuardIR
  | .iteLoop g _ _ => some g
  | _ => none
def invariantAt (acc : VarId) (s : Stmt) (target : GuardIR) (rho : Env) : Bool :=
  match strengthenLoopInvariantIR acc s target with
  | some inv => evalGuard rho inv
  | none => false

def mixedLoop : WhileLoop :=
  {init := .skip, cond := nzAt 2, accVar := 3,
   body := .add (.checkedDiv (lit 8) (v 0)) (.checkedDiv (lit 9) (v 1)),
   latch := .assign 2 (.sub (.var 2) (.lit 1)), ret := v 3}
def accumulatorLoop : WhileLoop :=
  {init := .skip, cond := nzAt 2, accVar := 3,
   body := .checkedDiv (lit 1) (v 3),
   latch := .assign 2 (.sub (.var 2) (.lit 1)), ret := v 3}
def copiedAccumulatorLoop : WhileLoop :=
  {init := .skip, cond := nzAt 2, accVar := 3,
   body := .checkedDiv (lit 1) (v 0),
   latch := .seq (.assign 0 (.var 3)) (.assign 2 (.sub (.var 2) (.lit 1))), ret := v 3}
def counterDivisionLoop : WhileLoop :=
  {init := .skip, cond := nzAt 2, accVar := 3,
   body := .add (v 3) (.checkedDiv (lit 8) (v 2)),
   latch := .assign 2 (.sub (.var 2) (.lit 1)), ret := v 3}
def checkedExit : WhileLoop := {counterDivisionLoop with ret := .checkedDiv (lit 1) (v 2)}

def chainMoves (start : Nat) : Nat → Stmt
  | 0 => .skip
  | edges + 1 => .seq (.assign start (.var (start + 1))) (chainMoves (start + 1) edges)
def chainLoop (stages : Nat) : WhileLoop :=
  {init := .skip, cond := nzAt 20, accVar := 21,
   body := .add (v 21) (.checkedDiv (lit 12) (v 0)),
   latch := .seq (chainMoves 0 (stages - 1)) (.assign 20 (.sub (.var 20) (.lit 1))), ret := v 21}
def nzRange (start : Nat) : Nat → GuardIR
  | 0 => .top
  | count + 1 => .conj (nzAt start) (nzRange (start + 1) count)
def chainEnv (last count : Int) : Env :=
  fun j => if j = 0 then 2 else if j = 1 then 3 else if j = 2 then 4
    else if j = 3 then 6 else if j = 4 then last else if j = 20 then count
    else if j = 21 then 0 else 1

def stableBranch : Stmt := .ite (nzAt 7) (.assign 0 (.var 1)) (.assign 0 (.var 4))
def changingBranch : Stmt :=
  .seq stableBranch (.assign 7 (.sub (.lit 1) (.var 7)))
def branchLoop (changing : Bool) : WhileLoop :=
  {init := .skip, cond := nzAt 2, accVar := 3,
   body := .add (v 3) (.checkedDiv (lit 12) (v 0)),
   latch := .seq (if changing then changingBranch else stableBranch)
     (.assign 2 (.sub (.var 2) (.lit 1))), ret := v 3}
def branchEnv (d a b tag count acc : Int) : Env :=
  fun j => if j = 0 then d else if j = 1 then a else if j = 4 then b
    else if j = 7 then tag else if j = 2 then count else if j = 3 then acc else 0
def stableReq : GuardIR :=
  .conj (nzAt 0) (.conj (.imp (nzAt 7) (nzAt 1)) (.imp (.imp (nzAt 7) .bot) (nzAt 4)))
def allSources : GuardIR := .conj (nzAt 0) (.conj (nzAt 1) (nzAt 4))

def ubExit : WhileLoop :=
  {init := .skip, cond := .bot, accVar := 3, body := lit 0, latch := .skip, ret := ubExpr}
def outerChoice : LoopProg := .iteLoop (nzAt 7) (.whileLoop counted) (.whileLoop ubExit)

def resetAccumulatorLoop : WhileLoop :=
  {accumulatorLoop with
   latch := .seq (.assign 3 (.lit 2)) (.assign 2 (.sub (.var 2) (.lit 1)))}
def invariantPreheader (w : WhileLoop) (ctx target : GuardIR) : Option GuardIR :=
  (strengthenLoopInvariantIR w.accVar w.latch target).map (hoistLoopGuardIR w.init ctx)
def directBodyRetChecks : LoopProg → Option (Nat × Nat)
  | .whileLoop w => some (checkedDivCount w.body, checkedDivCount w.ret)
  | _ => none
def clobberedSourceFrame : WhileLoop :=
  mkFrameStmtDivLoop 0 1 2 3 (.var 0) (.lit 5) (.assign 0 (.lit 0))
    (.ite (nzAt 0) .skip (.assign 7 (.lit 1)))
def swapPre : Stmt :=
  .seq (.assign 4 (.lit 0)) (.ite (nzAt 5) (.assign 9 (.lit (-1))) .skip)
def swapPost : Stmt :=
  .ite (.eq (.var 4) (.lit 2)) (.assign 9 (.lit 1)) (.assign 9 (.lit 2))
def swapping : WhileLoop := mkSwapDivLoop 0 1 2 3 4 5 6 (.lit 8) (.lit 5) swapPre swapPost
def swapEnv (x z count acc : Int) : Env :=
  fun j => if j = 0 then x else if j = 1 then z else if j = 5 then count else if j = 6 then acc else 0
def strictLoop (body : Expr) : WhileLoop :=
  {init := .skip, cond := .top, accVar := 3, body := body, latch := .skip, ret := lit 7}
theorem havoc_transparency_and_tautologies :
    havocGuardIR 3 (.nonZero (.lit 2)) = .nonZero (.lit 2) ∧
    havocGuardIR 3 (.eq (.var 3) (.var 3)) = .top ∧
    havocGuardIR 3 (.conj (nzAt 0) (.eq (.var 3) (.var 3))) = nzAt 0 ∧
    havocGuardIR 3 (nzAt 3) = .bot := by
  decide

theorem havoc_implication_truth_table :
    havocGuardIR 3 (.imp (nzAt 3) (nzAt 0)) = nzAt 0 ∧
    havocGuardIR 3 (.imp (nzAt 0) (nzAt 3)) = .imp (nzAt 0) .bot ∧
    evalGuard (env 0 0 0 2) (havocGuardIR 3 (.imp (nzAt 0) (nzAt 3))) = true ∧
    evalGuard (env 2 0 0 2) (havocGuardIR 3 (.imp (nzAt 0) (nzAt 3))) = false := by
  decide

theorem counted_known_reduction :
    evalGuard (env 2 0 2 0) (nzAt 0) = true ∧
    evalLoop 3 (env 2 0 2 0) (.whileLoop counted) = .done (.val 18) ∧
    evalLoop 3 (env 2 0 2 0) (optimizeLoop (nzAt 0) (.whileLoop counted)) = .done (.val 18) ∧
    loopCheckedDivCount (optimizeLoop (nzAt 0) (.whileLoop counted)) = 0 ∧
    loopDivOpCount (optimizeLoop (nzAt 0) (.whileLoop counted)) = 1 ∧
    loopBranchCount (optimizeLoop (nzAt 0) (.whileLoop counted)) = 0 ∧
    execLoopCheckCost 3 (env 2 0 2 0) (.whileLoop counted) = 7 ∧
    execLoopCheckCost 3 (env 2 0 2 0) (optimizeLoop (nzAt 0) (.whileLoop counted)) = 3 := by
  decide

theorem counted_preheader_versioning :
    invariantPreheader counted (nzAt 0) (nzAt 1) = some .top ∧
    invariantPreheader counted .top (nzAt 1) = some (nzAt 0) ∧
    versionGuard (optimizeLoop .top (.whileLoop counted)) = some (nzAt 0) ∧
    versionBodyChecks (optimizeLoop .top (.whileLoop counted)) = some (0, 1) ∧
    loopBranchCount (optimizeLoop .top (.whileLoop counted)) = 1 ∧
    evalLoop 3 (env 2 0 2 0) (optimizeLoop .top (.whileLoop counted)) = .done (.val 18) ∧
    execLoopCheckCost 3 (env 2 0 2 0) (optimizeLoop .top (.whileLoop counted)) = 4 := by
  decide

/-- The preheader tests the source of initialization, not the old divisor value. -/
theorem zero_trip_zero_divisor_safety :
    evalLoop 1 (env 0 7 0 5) (.whileLoop counted) = .done (.val 5) ∧
    evalLoop 1 (env 0 7 0 5) (optimizeLoop .top (.whileLoop counted)) = .done (.val 5) ∧
    evalLoop 2 (env 0 7 1 5) (.whileLoop counted) = .done .trap ∧
    evalLoop 2 (env 0 7 1 5) (optimizeLoop .top (.whileLoop counted)) = .done .trap ∧
    evalLoop 0 (env 0 7 0 5) (.whileLoop counted) = .outOfFuel ∧
    evalLoop 0 (env 0 7 0 5) (optimizeLoop .top (.whileLoop counted)) = .outOfFuel := by
  decide

theorem fuel_boundary_and_negative_counter :
    evalLoop 2 (env 2 0 2 0) (.whileLoop counted) = .outOfFuel ∧
    evalLoop 2 (env 2 0 2 0) (optimizeLoop (nzAt 0) (.whileLoop counted)) = .outOfFuel ∧
    execLoopCheckCost 2 (env 2 0 2 0) (.whileLoop counted) = 6 ∧
    execLoopCheckCost 2 (env 2 0 2 0) (optimizeLoop (nzAt 0) (.whileLoop counted)) = 2 ∧
    evalLoop 4 (env 2 0 (-1) 0) (.whileLoop counted) = .outOfFuel ∧
    evalLoop 4 (env 2 0 (-1) 0) (optimizeLoop .top (.whileLoop counted)) = .outOfFuel ∧
    execLoopCheckCost 4 (env 2 0 (-1) 0) (.whileLoop counted) = 12 ∧
    execLoopCheckCost 4 (env 2 0 (-1) 0) (optimizeLoop (nzAt 0) (.whileLoop counted)) = 4 ∧
    execLoopCheckCost 4 (env 2 0 (-1) 0) (optimizeLoop .top (.whileLoop counted)) = 5 := by
  decide

theorem static_facts_survive_in_slow_version :
    evalGuard (env 2 3 2 0) (nzAt 0) = true ∧
    versionGuard (optimizeLoop (nzAt 0) (.whileLoop mixedLoop)) = some (nzAt 1) ∧
    versionBodyChecks (optimizeLoop (nzAt 0) (.whileLoop mixedLoop)) = some (0, 1) ∧
    evalLoop 3 (env 2 3 2 0) (.whileLoop mixedLoop) = .done (.val 7) ∧
    evalLoop 3 (env 2 3 2 0) (optimizeLoop (nzAt 0) (.whileLoop mixedLoop)) = .done (.val 7) ∧
    execLoopCheckCost 3 (env 2 3 2 0) (.whileLoop mixedLoop) = 7 ∧
    execLoopCheckCost 3 (env 2 3 2 0) (optimizeLoop (nzAt 0) (.whileLoop mixedLoop)) = 4 ∧
    evalLoop 2 (env 2 0 1 0) (.whileLoop mixedLoop) = .done .trap ∧
    evalLoop 2 (env 2 0 1 0) (optimizeLoop (nzAt 0) (.whileLoop mixedLoop)) = .done .trap := by
  decide

/-- An entry fact about the accumulator cannot survive an arbitrary body write. -/
theorem accumulator_havoc_preserves_checks :
    evalGuard (env 0 0 2 2) (nzAt 3) = true ∧
    invariantAt 3 .skip (nzAt 3) (env 0 0 2 2) = false ∧
    evalLoop 3 (env 0 0 2 2) (.whileLoop accumulatorLoop) = .done .trap ∧
    evalLoop 3 (env 0 0 2 2) (optimizeLoop (nzAt 3) (.whileLoop accumulatorLoop)) = .done .trap ∧
    loopCheckedDivCount (optimizeLoop (nzAt 3) (.whileLoop accumulatorLoop)) = 1 ∧
    loopBranchCount (optimizeLoop (nzAt 3) (.whileLoop accumulatorLoop)) = 0 := by
  decide

theorem havoc_propagates_through_latch_copy :
    evalGuard (env 2 0 2 5) (nzAt 0) = true ∧
    invariantAt 3 copiedAccumulatorLoop.latch (nzAt 0) (env 2 0 2 5) = false ∧
    evalLoop 3 (env 2 0 2 5) (.whileLoop copiedAccumulatorLoop) = .done .trap ∧
    evalLoop 3 (env 2 0 2 5) (optimizeLoop (nzAt 0) (.whileLoop copiedAccumulatorLoop)) = .done .trap := by
  decide

/-- Latch execution follows the body write and may establish a fresh accumulator invariant. -/
theorem latch_reestablishes_accumulator :
    strengthenLoopInvariantIR 3 resetAccumulatorLoop.latch (nzAt 3) = some (nzAt 3) ∧
    evalGuard (env 0 0 2 2) (nzAt 3) = true ∧
    evalLoop 3 (env 0 0 2 2) (.whileLoop resetAccumulatorLoop) = .done (.val 2) ∧
    evalLoop 3 (env 0 0 2 2) (optimizeLoop (nzAt 3) (.whileLoop resetAccumulatorLoop)) = .done (.val 2) ∧
    loopCheckedDivCount (optimizeLoop (nzAt 3) (.whileLoop resetAccumulatorLoop)) = 0 ∧
    execLoopCheckCost 3 (env 0 0 2 2) (.whileLoop resetAccumulatorLoop) = 5 ∧
    execLoopCheckCost 3 (env 0 0 2 2) (optimizeLoop (nzAt 3) (.whileLoop resetAccumulatorLoop)) = 3 ∧
    evalLoop 1 (env 0 0 0 0) (optimizeLoop .top (.whileLoop resetAccumulatorLoop)) = .done (.val 0) ∧
    evalLoop 2 (env 0 0 1 0) (optimizeLoop .top (.whileLoop resetAccumulatorLoop)) = .done .trap := by
  decide

/-- A body check can use the current condition; that fact must not leak into the exit. -/
theorem body_and_exit_conditions_are_distinct :
    evalLoop 3 (env 0 0 2 0) (.whileLoop counterDivisionLoop) = .done (.val 12) ∧
    evalLoop 3 (env 0 0 2 0) (optimizeLoop .top (.whileLoop counterDivisionLoop)) = .done (.val 12) ∧
    loopCheckedDivCount (optimizeLoop .top (.whileLoop counterDivisionLoop)) = 0 ∧
    loopBranchCount (optimizeLoop .top (.whileLoop counterDivisionLoop)) = 0 ∧
    execLoopCheckCost 3 (env 0 0 2 0) (.whileLoop counterDivisionLoop) = 5 ∧
    execLoopCheckCost 3 (env 0 0 2 0) (optimizeLoop .top (.whileLoop counterDivisionLoop)) = 3 ∧
    directBodyRetChecks (optimizeLoop .top (.whileLoop checkedExit)) = some (0, 1) ∧
    evalLoop 3 (env 0 0 2 0) (.whileLoop checkedExit) = .done .trap ∧
    evalLoop 3 (env 0 0 2 0) (optimizeLoop .top (.whileLoop checkedExit)) = .done .trap ∧
    evalLoop 1 (env 0 0 0 0) (.whileLoop checkedExit) = .done .trap ∧
    evalLoop 1 (env 0 0 0 0) (optimizeLoop .top (.whileLoop checkedExit)) = .done .trap := by
  decide

theorem five_stage_pipeline_reduction :
    evalGuard (chainEnv 12 5) (nzRange 0 5) = true ∧
    invariantAt 21 (chainLoop 5).latch (nzAt 0) (chainEnv 12 5) = true ∧
    invariantAt 21 (chainLoop 5).latch (nzAt 0) (chainEnv 0 5) = false ∧
    invariantPreheader (chainLoop 5) (nzRange 0 5) (nzAt 0) = some .top ∧
    evalLoop 6 (chainEnv 12 5) (.whileLoop (chainLoop 5)) = .done (.val 16) ∧
    evalLoop 6 (chainEnv 12 5) (optimizeLoop (nzRange 0 5) (.whileLoop (chainLoop 5))) = .done (.val 16) ∧
    loopCheckedDivCount (optimizeLoop (nzRange 0 5) (.whileLoop (chainLoop 5))) = 0 ∧
    loopBranchCount (optimizeLoop (nzRange 0 5) (.whileLoop (chainLoop 5))) = 0 ∧
    execLoopCheckCost 6 (chainEnv 12 5) (.whileLoop (chainLoop 5)) = 11 ∧
    execLoopCheckCost 6 (chainEnv 12 5) (optimizeLoop (nzRange 0 5) (.whileLoop (chainLoop 5))) = 6 := by
  decide

theorem future_zero_does_not_trap_before_it_is_used :
    evalLoop 5 (chainEnv 0 4) (.whileLoop (chainLoop 5)) = .done (.val 15) ∧
    evalLoop 5 (chainEnv 0 4) (optimizeLoop .top (.whileLoop (chainLoop 5))) = .done (.val 15) ∧
    evalLoop 6 (chainEnv 0 5) (.whileLoop (chainLoop 5)) = .done .trap ∧
    evalLoop 6 (chainEnv 0 5) (optimizeLoop .top (.whileLoop (chainLoop 5))) = .done .trap ∧
    evalLoop 4 (chainEnv 0 5) (.whileLoop (chainLoop 5)) = .outOfFuel ∧
    evalLoop 4 (chainEnv 0 5) (optimizeLoop .top (.whileLoop (chainLoop 5))) = .outOfFuel := by
  decide

theorem bounded_saturation_is_conservative :
    strengthenLoopInvariantIR 21 (chainLoop 9).latch (nzAt 0) = none ∧
    loopCheckedDivCount (optimizeLoop (nzRange 0 9) (.whileLoop (chainLoop 9))) = 1 ∧
    evalGuard (chainEnv 12 1) (nzRange 0 9) = true ∧
    evalLoop 2 (chainEnv 12 1) (.whileLoop (chainLoop 9)) = .done (.val 6) ∧
    evalLoop 2 (chainEnv 12 1) (optimizeLoop (nzRange 0 9) (.whileLoop (chainLoop 9))) = .done (.val 6) := by
  decide

theorem stable_branch_conditional_invariant :
    strengthenLoopInvariantIR 3 stableBranch (nzAt 0) = some stableReq ∧
    invariantAt 3 stableBranch (nzAt 0) (branchEnv 2 3 0 1 2 0) = true ∧
    invariantAt 3 stableBranch (nzAt 0) (branchEnv 2 0 4 0 2 0) = true ∧
    invariantAt 3 stableBranch (nzAt 0) (branchEnv 2 0 4 1 2 0) = false ∧
    invariantAt 3 stableBranch (nzAt 0) (branchEnv 2 3 0 0 2 0) = false ∧
    invariantAt 3 stableBranch (nzAt 0) (branchEnv 0 3 4 1 2 0) = false := by
  decide

theorem stable_branch_allows_unused_zero_source :
    evalGuard (branchEnv 2 3 0 1 2 0) stableReq = true ∧
    evalLoop 3 (branchEnv 2 3 0 1 2 0) (.whileLoop (branchLoop false)) = .done (.val 10) ∧
    evalLoop 3 (branchEnv 2 3 0 1 2 0) (optimizeLoop stableReq (.whileLoop (branchLoop false))) = .done (.val 10) ∧
    loopCheckedDivCount (optimizeLoop stableReq (.whileLoop (branchLoop false))) = 0 ∧
    loopBranchCount (optimizeLoop stableReq (.whileLoop (branchLoop false))) = 0 ∧
    execLoopCheckCost 3 (branchEnv 2 3 0 1 2 0) (.whileLoop (branchLoop false)) = 7 ∧
    execLoopCheckCost 3 (branchEnv 2 3 0 1 2 0) (optimizeLoop stableReq (.whileLoop (branchLoop false))) = 5 := by
  decide

theorem changing_branch_requires_both_sources :
    strengthenLoopInvariantIR 3 changingBranch (nzAt 0) = some allSources ∧
    invariantAt 3 changingBranch (nzAt 0) (branchEnv 2 3 0 1 3 0) = false ∧
    invariantAt 3 changingBranch (nzAt 0) (branchEnv 2 3 4 1 3 0) = true ∧
    evalGuard (branchEnv 2 3 4 1 3 0) allSources = true ∧
    evalLoop 4 (branchEnv 2 3 4 1 3 0) (.whileLoop (branchLoop true)) = .done (.val 13) ∧
    evalLoop 4 (branchEnv 2 3 4 1 3 0) (optimizeLoop allSources (.whileLoop (branchLoop true))) = .done (.val 13) ∧
    loopCheckedDivCount (optimizeLoop allSources (.whileLoop (branchLoop true))) = 0 ∧
    execLoopCheckCost 4 (branchEnv 2 3 4 1 3 0) (.whileLoop (branchLoop true)) = 10 ∧
    execLoopCheckCost 4 (branchEnv 2 3 4 1 3 0) (optimizeLoop allSources (.whileLoop (branchLoop true))) = 7 := by
  decide

theorem changing_branch_trap_is_not_hidden :
    let ctx := GuardIR.conj (nzAt 0) (.conj (nzAt 1) (nzAt 7))
    evalGuard (branchEnv 2 3 0 1 3 0) ctx = true ∧
    versionGuard (optimizeLoop ctx (.whileLoop (branchLoop true))) = some (nzAt 4) ∧
    versionBodyChecks (optimizeLoop ctx (.whileLoop (branchLoop true))) = some (0, 1) ∧
    evalLoop 4 (branchEnv 2 3 0 1 3 0) (.whileLoop (branchLoop true)) = .done .trap ∧
    evalLoop 4 (branchEnv 2 3 0 1 3 0) (optimizeLoop ctx (.whileLoop (branchLoop true))) = .done .trap := by
  decide

theorem source_clobber_does_not_kill_saved_divisor :
    let rho := env 2 0 2 0
    let initial := execStmt clobberedSourceFrame.init rho
    let afterOne := execStmt clobberedSourceFrame.latch (updateEnv initial 3 6)
    evalGuard rho (nzAt 0) = true ∧ evalGuard afterOne (nzAt 0) = false ∧
    evalGuard afterOne (nzAt 1) = true ∧
    evalLoop 3 rho (.whileLoop clobberedSourceFrame) = .done (.val 11) ∧
    evalLoop 3 rho (optimizeLoop (nzAt 0) (.whileLoop clobberedSourceFrame)) = .done (.val 11) ∧
    loopCheckedDivCount (optimizeLoop (nzAt 0) (.whileLoop clobberedSourceFrame)) = 0 ∧
    execLoopCheckCost 3 rho (.whileLoop clobberedSourceFrame) = 9 ∧
    execLoopCheckCost 3 rho (optimizeLoop (nzAt 0) (.whileLoop clobberedSourceFrame)) = 5 := by
  decide

theorem swap_with_nontrivial_surrounding_statements :
    stmtWritesVar 4 swapPre = true ∧ stmtWritesVar 2 swapPre = false ∧
    evalGuard (swapEnv 2 4 2 0) (.conj (nzAt 0) (nzAt 1)) = true ∧
    evalLoop 3 (swapEnv 2 4 2 0) (.whileLoop swapping) = .done (.val 16) ∧
    evalLoop 3 (swapEnv 2 4 2 0) (optimizeLoop (.conj (nzAt 0) (nzAt 1)) (.whileLoop swapping)) = .done (.val 16) ∧
    loopCheckedDivCount (optimizeLoop (.conj (nzAt 0) (nzAt 1)) (.whileLoop swapping)) = 0 ∧
    execLoopCheckCost 3 (swapEnv 2 4 2 0) (.whileLoop swapping) = 11 ∧
    execLoopCheckCost 3 (swapEnv 2 4 2 0) (optimizeLoop (.conj (nzAt 0) (nzAt 1)) (.whileLoop swapping)) = 7 ∧
    evalLoop 3 (swapEnv 2 (-4) 2 0) (optimizeLoop (.conj (nzAt 0) (nzAt 1)) (.whileLoop swapping)) = .done (.val 12) := by
  decide

theorem outer_loop_choices_are_contextual :
    let ctx := GuardIR.conj (nzAt 7) (nzAt 0)
    let rho := branchEnv 2 0 0 1 2 0
    evalGuard rho ctx = true ∧
    evalLoop 3 rho outerChoice = .done (.val 18) ∧
    evalLoop 3 rho (optimizeLoop ctx outerChoice) = .done (.val 18) ∧
    loopBranchCount (optimizeLoop ctx outerChoice) = 0 ∧
    evalGuard (fun _ => 0) (.imp (nzAt 7) .bot) = true ∧
    evalLoop 1 (fun _ => 0) outerChoice = .done .ub ∧
    evalLoop 1 (fun _ => 0) (optimizeLoop (.imp (nzAt 7) .bot) outerChoice) = .done .ub ∧
    loopBranchCount (optimizeLoop (.imp (nzAt 7) .bot) outerChoice) = 0 ∧
    evalLoop 0 (fun _ => 0) (optimizeLoop (.imp (nzAt 7) .bot) outerChoice) = .outOfFuel := by
  decide

theorem decrementing_divisor_keeps_second_trip_trap :
    let w := mkDecrementDivisorLoop 0 1 2 3 (.lit 8)
    evalGuard (env 1 7 2 0) (nzAt 0) = true ∧
    evalLoop 1 (env 1 7 2 0) (.whileLoop w) = .outOfFuel ∧
    evalLoop 1 (env 1 7 2 0) (optimizeLoop (nzAt 0) (.whileLoop w)) = .outOfFuel ∧
    evalLoop 2 (env 1 7 2 0) (.whileLoop w) = .done .trap ∧
    evalLoop 2 (env 1 7 2 0) (optimizeLoop (nzAt 0) (.whileLoop w)) = .done .trap ∧
    evalLoop 3 (env 1 7 2 0) (optimizeLoop (nzAt 0) (.whileLoop w)) = .done .trap ∧
    loopCheckedDivCount (optimizeLoop (nzAt 0) (.whileLoop w)) = 1 := by
  decide

theorem strict_failures_and_existing_ub :
    evalLoop 1 (fun _ => 0) (.whileLoop (strictLoop (.mul (lit 0) trapExpr))) = .done .trap ∧
    evalLoop 1 (fun _ => 0)
      (optimizeLoop .top (.whileLoop (strictLoop (.mul (lit 0) trapExpr)))) = .done .trap ∧
    evalLoop 1 (fun _ => 0) (.whileLoop (strictLoop (.mul (lit 0) ubExpr))) = .done .ub ∧
    evalLoop 1 (fun _ => 0)
      (optimizeLoop .top (.whileLoop (strictLoop (.mul (lit 0) ubExpr)))) = .done .ub ∧
    evalLoop 1 (fun _ => 0)
      (optimizeLoop .top (.whileLoop {strictLoop ubExpr with cond := .bot})) = .done (.val 7) ∧
    evalLoop 3 (env 0 0 2 2)
      (.whileLoop {accumulatorLoop with body := .uncheckedDiv (lit 1) (v 3)}) = .done .ub ∧
    evalLoop 3 (env 0 0 2 2)
      (optimizeLoop (nzAt 3) (.whileLoop {accumulatorLoop with body := .uncheckedDiv (lit 1) (v 3)})) = .done .ub := by
  decide

def sweepCases : List (GuardIR × LoopProg × Env) :=
  [(nzAt 0, .whileLoop counted, env 2 0 2 0),
   (.top, .whileLoop counted, env 0 7 0 5),
   (.top, .whileLoop counted, env 0 7 1 5),
   (nzAt 0, .whileLoop counted, env (-2) 0 2 0),
   (nzAt 0, .whileLoop counted, env 2 0 (-1) 0),
   (nzAt 0, .whileLoop mixedLoop, env 2 0 2 0),
   (nzAt 3, .whileLoop accumulatorLoop, env 0 0 2 2),
   (nzAt 3, .whileLoop resetAccumulatorLoop, env 0 0 2 2),
   (.top, .whileLoop counterDivisionLoop, env 0 0 2 0),
   (.top, .whileLoop checkedExit, env 0 0 2 0),
   (stableReq, .whileLoop (branchLoop false), branchEnv 2 3 0 1 2 0),
   (allSources, .whileLoop (branchLoop true), branchEnv 2 3 4 1 3 0),
   (.conj (nzAt 0) (.conj (nzAt 1) (nzAt 7)), .whileLoop (branchLoop true), branchEnv 2 3 0 1 3 0),
   (nzRange 0 5, .whileLoop (chainLoop 5), chainEnv 12 5),
   (.top, .whileLoop (chainLoop 5), chainEnv 0 4),
   (.top, .whileLoop (chainLoop 5), chainEnv 0 5),
   (nzAt 0, .whileLoop clobberedSourceFrame, env 2 0 2 0),
   (.conj (nzAt 0) (nzAt 1), .whileLoop swapping, swapEnv 2 4 2 0),
   (.conj (nzAt 7) (nzAt 0), outerChoice, branchEnv 2 0 0 1 2 0),
   (.imp (nzAt 7) .bot, outerChoice, fun _ => 0)]
def fuels : List Nat := [0, 1, 2, 3, 4, 5, 6]

theorem sweep_dimensions :
    sweepCases.length = 20 ∧ fuels.length = 7 := by
  decide

theorem sweep_contexts_hold :
    sweepCases.all (fun (ctx, _, rho) => evalGuard rho ctx) = true := by
  decide

theorem bounded_loop_semantic_sweep :
    sweepCases.all (fun (ctx, prog, rho) =>
      fuels.all (fun fuel => decide (evalLoop fuel rho (optimizeLoop ctx prog) = evalLoop fuel rho prog))) = true := by
  decide

end CatSem.PostImplAudit.M3

-- M3 public API and explicit transitive dependency reports for every new audit declaration.
#print axioms CatSem.havocGuardIR
#print axioms CatSem.strengthenLoopInvariantIR
#print axioms CatSem.hoistLoopGuardIR
#print axioms CatSem.optimizeLoop
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
#print axioms CatSem.PostImplAudit.M3.nzAt
#print axioms CatSem.PostImplAudit.M3.counted
#print axioms CatSem.PostImplAudit.M3.versionBodyChecks
#print axioms CatSem.PostImplAudit.M3.versionGuard
#print axioms CatSem.PostImplAudit.M3.invariantAt
#print axioms CatSem.PostImplAudit.M3.mixedLoop
#print axioms CatSem.PostImplAudit.M3.accumulatorLoop
#print axioms CatSem.PostImplAudit.M3.copiedAccumulatorLoop
#print axioms CatSem.PostImplAudit.M3.counterDivisionLoop
#print axioms CatSem.PostImplAudit.M3.checkedExit
#print axioms CatSem.PostImplAudit.M3.chainMoves
#print axioms CatSem.PostImplAudit.M3.chainLoop
#print axioms CatSem.PostImplAudit.M3.nzRange
#print axioms CatSem.PostImplAudit.M3.chainEnv
#print axioms CatSem.PostImplAudit.M3.stableBranch
#print axioms CatSem.PostImplAudit.M3.changingBranch
#print axioms CatSem.PostImplAudit.M3.branchLoop
#print axioms CatSem.PostImplAudit.M3.branchEnv
#print axioms CatSem.PostImplAudit.M3.stableReq
#print axioms CatSem.PostImplAudit.M3.allSources
#print axioms CatSem.PostImplAudit.M3.ubExit
#print axioms CatSem.PostImplAudit.M3.outerChoice
#print axioms CatSem.PostImplAudit.M3.resetAccumulatorLoop
#print axioms CatSem.PostImplAudit.M3.invariantPreheader
#print axioms CatSem.PostImplAudit.M3.directBodyRetChecks
#print axioms CatSem.PostImplAudit.M3.clobberedSourceFrame
#print axioms CatSem.PostImplAudit.M3.swapPre
#print axioms CatSem.PostImplAudit.M3.swapPost
#print axioms CatSem.PostImplAudit.M3.swapping
#print axioms CatSem.PostImplAudit.M3.swapEnv
#print axioms CatSem.PostImplAudit.M3.strictLoop
#print axioms CatSem.PostImplAudit.M3.havoc_transparency_and_tautologies
#print axioms CatSem.PostImplAudit.M3.havoc_implication_truth_table
#print axioms CatSem.PostImplAudit.M3.counted_known_reduction
#print axioms CatSem.PostImplAudit.M3.counted_preheader_versioning
#print axioms CatSem.PostImplAudit.M3.zero_trip_zero_divisor_safety
#print axioms CatSem.PostImplAudit.M3.fuel_boundary_and_negative_counter
#print axioms CatSem.PostImplAudit.M3.static_facts_survive_in_slow_version
#print axioms CatSem.PostImplAudit.M3.accumulator_havoc_preserves_checks
#print axioms CatSem.PostImplAudit.M3.havoc_propagates_through_latch_copy
#print axioms CatSem.PostImplAudit.M3.latch_reestablishes_accumulator
#print axioms CatSem.PostImplAudit.M3.body_and_exit_conditions_are_distinct
#print axioms CatSem.PostImplAudit.M3.five_stage_pipeline_reduction
#print axioms CatSem.PostImplAudit.M3.future_zero_does_not_trap_before_it_is_used
#print axioms CatSem.PostImplAudit.M3.bounded_saturation_is_conservative
#print axioms CatSem.PostImplAudit.M3.stable_branch_conditional_invariant
#print axioms CatSem.PostImplAudit.M3.stable_branch_allows_unused_zero_source
#print axioms CatSem.PostImplAudit.M3.changing_branch_requires_both_sources
#print axioms CatSem.PostImplAudit.M3.changing_branch_trap_is_not_hidden
#print axioms CatSem.PostImplAudit.M3.source_clobber_does_not_kill_saved_divisor
#print axioms CatSem.PostImplAudit.M3.swap_with_nontrivial_surrounding_statements
#print axioms CatSem.PostImplAudit.M3.outer_loop_choices_are_contextual
#print axioms CatSem.PostImplAudit.M3.decrementing_divisor_keeps_second_trip_trap
#print axioms CatSem.PostImplAudit.M3.strict_failures_and_existing_ub
#print axioms CatSem.PostImplAudit.M3.sweepCases
#print axioms CatSem.PostImplAudit.M3.fuels
#print axioms CatSem.PostImplAudit.M3.sweep_dimensions
#print axioms CatSem.PostImplAudit.M3.sweep_contexts_hold
#print axioms CatSem.PostImplAudit.M3.bounded_loop_semantic_sweep
