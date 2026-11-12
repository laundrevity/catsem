PRELOCK STATUS: CHANGES REQUESTED

Milestone 3 Gate 1 pre-lock review — Lean specification semantics.

Spec digest from `reviews/current_spec.sha256`:

```text
e8f568da6301459f8d78f38a82657d1d272ff65603a45a3e65a901e39e3bcbfc
```

Reproduced with `shasum -a 256 Specs/Defs.lean Specs/Target.lean Specs/Verify.lean blueprint/lemma_dag.json | shasum -a 256`. The protected specifications were unchanged. Inputs reviewed were `CHARTER.md`, the digest, and the three Lean specification files. The requested gate command was used for validation; scripts and build tooling were not audited.

**BLOCKING B1 — Strengthening success may be everywhere false.** The inductive-soundness obligation allows an uninhabited invariant, and both `strengthenLoopInvariantIR_stationary` and `strengthenLoopInvariantIR_pipeline` require only `∃ inv, ... = some inv`. Consequently, the total computable function

```lean
fun (_acc : VarId) (_latch : Stmt) (_target : GuardIR) => some GuardIR.bot
```

satisfies all three strengthening obligations. `False` is preserved by the havoc/latch transfer and implies any target. Returning `some` does not establish that a usable invariant was discovered.

This is a full-contract counterexample, not just an isolated weakening. In `Specs/RedTeam.lean`, `M3.replace_strengthener` proves that replacing the strengthening component of **any** satisfying implementation with `M3.vacuousStrengthen` preserves all fourteen compiler-dependent M3 obligations. The remaining state-transfer iteration theorem is independent of that component. `M3.vacuous_countermodel` instantiates the replacement with a total, sound optimizer that independently uses a certified invariant planner, and proves that every reported strengthening result has no satisfying environment. The optimizer capability theorems therefore cannot repair the strengthening API's missing coverage requirement. `M3.vacuous_success_rejects_safe_entry` exhibits a true, safe pipeline entry context rejected by the resulting hoisted false invariant.

`Specs/Verify.lean` repeats the same existential-only success signatures, so it does not exclude this countermodel. This is an anti-vacuity defect in the advertised strengthening capability and the charter's rejection of constant-false fallbacks; it is not an inconsistency in Lean or the evaluator.

To close B1, strengthen the two success obligations with semantic coverage of the intended safe headers, alongside their existing success and inductive-soundness requirements. Suitable lower bounds on the returned invariant are:

- Stationary case: `denoteGuard (.nonZero (.var d)) ≤ denoteGuard inv`.
- Pipeline case: `denoteGuard (.conj (.nonZero (.var d)) (.nonZero (.var nextD))) ≤ denoteGuard inv`.

These bounds exclude false or arbitrarily narrow success results without fixing their AST representation. Requiring establishment of the returned invariant from the corresponding parametric entry contexts is another viable formulation. Update the matching Lean verification signatures. The constructive witness already returns the stated nonzero guard/conjunction, so these repairs do not require an unbounded invariant search or a classical decision procedure.

**NON-BLOCKING — All fifteen obligations are jointly constructively satisfiable.** `M3.satisfiable` and `M3.constructive_obligations` supply a total computable implementation for all fourteen compiler-dependent targets; `M3.state_iterate` independently proves the generic iteration target. The compiler obtains proof-carrying invariants for stationary assignments and copying pipeline latches, computes a normalized syntactic preheader guard, and rewrites the loop body under that invariant. Unknown preconditions select between an optimized loop and the original loop. The original return, loop condition, and latch are preserved. All unsupported cases retain the source program.

| Target group | Independent witnesses |
| --- | --- |
| State-transfer iteration (1) | `state_iterate` |
| Havoc soundness and non-mention exactness (2) | `havoc_sound`, `havoc_exact` |
| Strengthening soundness and two success obligations (3) | `constructive_inductive`, `constructive_stationary`, `constructive_pipeline` |
| Hoist denotation and arbitrary-iteration target preservation (2) | `hoist_denote`, `hoist_iterate` |
| Guarded and operational loop soundness (2) | `opt_guarded`, `opt_sound` |
| Known/unknown-context costs, zero-divisor behavior, pipeline elimination, decrement trap (5) | `known_elim`, `unknown_hoist`, `zero_behavior`, `pipeline_elim`, `decrement_trap` |

The capability proofs retain every target parameter and side condition. `countdown_cost` proves the costs for arbitrary natural trip counts, not a finite sample. The usable pipeline invariant is inhabited and remains active after every number of abstract steps, as proved by `strengthened_pipeline_all_depths_active`.

**NON-BLOCKING — Other anti-degeneracy requirements have substantive force.** `counted_family_injective` and `finite_fixture_rejected` rule out finite exact fixture tables that leave sufficiently fresh counted loops unchanged; `identity_rejected` is a corollary. `zero_step_only_rejected` proves that a strengthening algorithm restricted to `none` or the unchanged target cannot meet the pipeline obligation, because `d ≠ 0` alone is not inductive when `nextD = 0`. This rejection does not exclude the false-invariant loophole in B1.

Concrete witnesses reject entry-only unchecked division: with an initially nonzero divisor that is decremented, the source traps on iteration two while the naive rewrite produces UB. They also reject eager preheader trapping on a zero divisor when the loop has zero trips: the source returns the accumulator. The sound candidate preserves both outcomes and retains checks on the decrementing-divisor loop.

**NON-BLOCKING — TCB semantics and costs are coherent.** `havocTransfer` uses existential postconditions and universal pullbacks, with a constructive Galois-connection proof. `loopStepTransfer` composes arbitrary accumulator writes before the latch, matching successful body evaluation in `runWhileSteps`. It conservatively includes all accumulator values and does not filter by the loop condition. The evaluator executes initialization, then the condition, body, accumulator update, and latch in the prescribed order; traps and UB stop before the latch and return. The cost observer follows the same selected path and stopping points.

The concrete checks cover accumulator/latch ordering; signed arithmetic; both successful and exhausted-fuel outcomes; zero and positive trip counts; a three-trip pipeline; a zero divisor introduced by its second stage; and failure short-circuiting. Costs include counted-loop `7 → 3` under a known context, `7 → 4` with versioning, and pipeline `10 → 4`.

**SCOPE-NOTE — Fuel and conservative analysis.** Fuel counts loop-header visits: `n` successful iterations plus the final false condition require `n + 1` fuel. Zero fuel returns `.outOfFuel`, even for a zero-trip loop, while initialization and preheader-version guards may already incur cost. The evaluator is total for finite fuel; the specification does not assert termination of arbitrary source loops. Conservative havoc may reject guards that mention the written variable even when those guards are tautologies; its advertised exactness applies only to non-mentioning guards.

**Validation.** Final lean-lsp diagnostics for `Specs/RedTeam.lean` report no errors or warnings and 1,668 axiom reports. The implementations, satisfiability theorem, replacement theorem, and full countermodel have transitive dependencies contained in `{propext, Quot.sound}`. `havoc` and `vacuousStrengthen` have no axiom dependencies; the usable compiler functions report only `propext`. No `Specs.Target` placeholder is invoked.

`./scripts/verify.sh --spec-audit` completed with exit code **0** and `GATE 1 SPEC AUDIT PASSED`. Its output records 1,668 unique declaration reports, successful auditing of 1,931 kernel declarations (709 in `Specs.Defs`, 1,222 in `Specs.RedTeam`), all 41 anonymous TCB examples, and successful kernel replay. There are zero `sorryAx`, `Classical.choice`, or other non-whitelisted dependencies in the audited TCB and witnesses. Expected placeholder warnings during the target-interface build are separate from the clean audit-file diagnostics.

The successful validation certifies both the useful implementation witness and the vacuous countermodel. B1 remains a specification defect requiring changes before lock.
