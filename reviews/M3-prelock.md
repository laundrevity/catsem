PRELOCK STATUS: APPROVED

Milestone 3 Gate 1 Round 3 review following `reviews/M3-prelock-r2-disposition.md`.

Current spec SHA-256:

```text
ea3342a34875761630ac2397b5f3fcad3791d75b355d9dd9014a480920a8ab51
```

This matches `reviews/current_spec.sha256`, the disposition, and the reproduced digest from `shasum -a 256 Specs/Defs.lean Specs/Target.lean Specs/Verify.lean blueprint/lemma_dag.json | shasum -a 256`. The protected specification files were unchanged during this review. Scope was Lean specification semantics; the requested gate command was executed, and scripts were not audited.

**B1-R2 CLOSED — The old countermodels cannot satisfy the current contract.** The new general frame-strengthening obligation requires success and non-vacuous coverage for arbitrary statement trees whose structural write inspection excludes the protected variables. It has no premise involving compiler-supplied guard synthesis or pullback output. `M3R3.round2_full_countermodel_rejected` proves that the Round 2 strengthening matcher fails this obligation for **every** choice of the other helpers. Its safe `skip; assignment` counterexample is therefore rejected even when the legacy closure test is skewed to never return `.top`.

The new optimizer requirements also prevent retaining the old matcher internally. `round2_optimizer_rejected` and `round2_optimizer_full_rejected` prove that `M3.opt`, which still dispatches through the old `M3.plan`, cannot meet the frame-loop elimination requirement: a one-trip, inhabited example retains two checked divisions where zero are required. The earlier constant-false strengthening fallback remains rejected. `wrapped_havoc_rejected` confirms that the new syntactic-transparency obligation excludes wrapper injection on a non-mentioning guard.

The safe stationary/pipeline clauses from Round 2 remain intact, including arbitrary RHSs, coverage of all intended safe headers, and parametric `.top` preheader discharge. The new swap, three-stage pipeline, and branching obligations add unconditional coverage and discharge across arbitrary surrounding frame-preserving statement trees. Matching signatures and axiom-check entries in `Specs/Verify.lean` retain these quantifiers and conclusions.

**TCB review.** `stmtWritesVar` is a total structural inspector: assignments test destination equality, sequential statements combine write information, and conditionals include both arms. Conditions and assignment RHSs are pure reads. `exec_frame` proves that a false write result preserves the inspected variable's value through execution. The four new loop builders construct ordinary ASTs and do not alter the evaluator or cost observer. Their sequencing, accumulator updates, countdown positions, and return expressions match the target claims.

**All 27 M3 targets are constructively satisfiable.** The new `CatSem.RedTeam.M3R3` section supplies a total candidate with structural backward clause transformation, conservative branch joins, accumulator havoc, and at most four closure checks. It does not dispatch on the named latch templates. A successful result contains the target and is closed under the abstract loop transfer. The hoisted guard has the required exact denotation; loop-body rewriting preserves every fuel-indexed outcome.

`all_obligations` packages the 26 compiler-dependent targets, and `M3.state_iterate` supplies the remaining generic target. `satisfiable` constructs the functions explicitly. `compatible_with_m1_m2` verifies that the selected helper bindings also satisfy the complete earlier milestone contracts.

| New target group | Independent witnesses |
| --- | --- |
| Havoc syntactic transparency | `havoc_transparent` |
| General frame, swap, pipeline, and branch strengthening | `frame_safe`, `swap_safe`, `pipe3_safe`, `branch_safe` |
| General frame, swap, pipeline, and branch optimization | `frame_opt`, `swap_opt`, `pipe3_opt`, `branch_opt` |

The strengthening proofs retain arbitrary pre/post statement trees and arbitrary branch conditions. They cover all entry-variable choices, including aliases with initialized variables. The three-stage pipeline requires two backward expansions before closure, as explicitly checked by `pipeline3_multiple_steps`.

The general `run_saving` proof handles arbitrary latch guard costs and proves an exact saving of two division checks per successful iteration. Source and optimized bodies produce the same value, so their accumulator updates, later states, branch choices, and latch costs agree. This yields the four required cost inequalities without assuming that surrounding statements are free of runtime guards.

Concrete kernel-checked witnesses include:

- A framed two-trip loop with nested statements: check cost `11 → 7`.
- A two-trip swap loop whose pre-latch overwrites the scratch variable before the swap saves the divisor: `11 → 7`.
- A three-trip pipeline whose pre-latch invalidates the original entry context while preserving the actual invariant: `16 → 10`.
- A two-trip branching latch taking both arms on successive iterations: `13 → 9`.
- Negative divisors, a zero introduced by a selected branch, zero-trip returns, and the decrementing-divisor trap.

**SCOPE-NOTE — The preserved legacy closure theorem.** The old helper-dependent `strengthenLoopInvariantIR_step_complete` implication still exists and may have a false antecedent with weak helpers. The Round 3 fix closes its use as a bypass by adding independent, unconditional requirements. The witness deliberately retains an admissible weak helper binding while proving every new capability without that implication. Approval rests on the unconditional obligations and the full countermodel rejection proofs, not on asserting that every permitted helper must close every semantic invariant. The specification still permits bounded, conservative analysis outside the required families.

**Validation.** Final lean-lsp diagnostics for `Specs/RedTeam.lean` contain no errors or warnings and 1,981 axiom reports. The new `strengthen`, `hoist`, and `opt` functions report only `propext`; the full satisfiability and rejection proofs use only `{propext, Quot.sound}`. No `Specs.Target` compiler stub or theorem placeholder is invoked.

`./scripts/verify.sh --spec-audit` exited **0**, reporting `GATE 1 SPEC AUDIT PASSED`. It verified 1,981 unique declaration reports, 2,276 kernel declarations (717 in `Specs.Defs`, 1,559 in `Specs.RedTeam`), all 47 anonymous TCB examples, and successful kernel replay. The audited TCB and witnesses have zero `sorryAx`, `Classical.choice`, or other non-whitelisted dependencies. Expected target-placeholder build warnings are separate from the clean audit-file diagnostics.
