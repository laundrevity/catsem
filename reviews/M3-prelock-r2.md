PRELOCK STATUS: CHANGES REQUESTED

Milestone 3 Gate 1 re-review following `reviews/M3-prelock-r1-disposition.md`.

Current spec SHA-256:

```text
3caeef405a5117aadae5081939cc243ffa4dc63e902d00aee35bd6bbba824a44
```

This matches `reviews/current_spec.sha256`, the disposition, and the reproduced digest from `shasum -a 256 Specs/Defs.lean Specs/Target.lean Specs/Verify.lean blueprint/lemma_dag.json | shasum -a 256`. The protected specification files were unchanged during this review. Scope was the Lean specifications; the requested gate command was executed, and scripts were not audited.

**RESOLVED — Constant-false success and finite exact fixtures.** The new `strengthenLoopInvariantIR_stationary_safe` and `strengthenLoopInvariantIR_pipeline_safe` clauses provide the requested semantic coverage for all safe headers, for arbitrary assignment RHS expressions. They also require syntactic `.top` preheader discharge for every entry-variable choice. The matching `Specs/Verify.lean` checks preserve these quantifiers and conclusions, and all three new declarations have axiom-check entries.

`M3R2.bottom_rejected` and `M3R2.updated_bottom_rejected` prove that the old everywhere-`some .bot` countermodel cannot satisfy the revised contract, independently of the other compiler functions. `M3R2.finite_fixture_fallback_rejected` uses an infinite injective family of literal-assignment latches to reject any finite exact fixture table that eventually returns either `none` or `some .bot`.

**BLOCKING B1-R2 — The general one-step completeness premise can be false for every input.** The remaining claim in the disposition—excluding a strengthening function restricted to the named latch forms—is not established by `strengthenLoopInvariantIR_step_complete`. Its antecedent tests for syntactic `.top` using compiler-supplied `synthesizeGuardIR`, `pullbackGuardIR`, and `havocGuardIR`. Their existing contracts permit the following combined implementation:

- `M1R2.synth` satisfies every M1 synthesis obligation but retains a raw implication when both the context and target are conjunctions.
- `M2.wp` satisfies every M2 pullback obligation and preserves an outer conjunction when pulling back the candidate through any statement.
- `M3.havoc` is sound and exact on non-mentioning guards; it returns either the original conjunction or `.bot`.

Because the candidate is always `.conj target g₁`, this synthesizer therefore returns an implication, never syntactic `.top`, in the new closure test. `M3R2.weak_closure_never_top` proves this for **all** accumulator variables, latches, and targets. The general completeness implication consequently imposes no additional constraint in this model.

This is compatible with the earlier milestones, not an assumption that ignores helper specifications. `M3R2.shape_countermodel_compatible_with_m1_m2` proves the full M1 and M2 contracts together with all revised compiler-dependent M3 obligations. The remaining generic state-iteration theorem is independently supplied by `M3.state_iterate`. The strengthening component is the old `M3.constructiveStrengthen`: it handles the two required statement forms with arbitrary RHSs, yet rejects every member of the safe, inhabited family

```text
accVar = 3
latch  = skip; variable 2 := literal k
target = variable 0 != 0
```

`M3R2.remaining_shape_countermodel` proves that rejection for every natural `k`, while `wrapped_family_is_safe` proves preservation and an all-ones environment witnesses non-vacuity. Thus finite exact tables are excluded, but the restricted statement-form matcher remains admitted.

A minimal explanation is `c := conj (nonZero (var 0)) (nonZero (var 0))`. The permitted weak synthesizer returns `imp c c`, whose Boolean value is true but whose syntax is not `.top`. `weak_and_strong_closure_comparison` computes this distinction, and `wrapped_candidate_is_inductive` proves that the concrete candidate is in fact inductive. This is an anti-vacuity gap in the new generality requirement, not an inconsistency in the loop evaluator.

To close B1-R2, make the closure criterion non-vacuous independently of discretionary helper output syntax. One approach is a fixed, sound, computable reference closure checker. If the trigger remains compiler-supplied, add sufficient helper normalization/discharge requirements and explicit inhabited closure obligations on parametric latches outside the two named forms. In particular, an unconditional success-and-coverage requirement for the wrapped-assignment family above would exclude this countermodel. General frame-preserving statements provide a broader, still decidable family. General reflexivity/conjunction discharge would reject the weak synthesizer shown here, but its interaction with allowed pullback/havoc representations also needs specification. No unbounded semantic arithmetic decision procedure is requested.

**NON-BLOCKING — A general total computable candidate satisfies all eighteen targets.** `M3R2.strengthen` uniformly forms the one-step candidate for any statement and guard, checks its preservation with a stronger conjunction-discharge synthesizer, and returns it only when the check succeeds. It has no latch-form dispatch. `strengthen_inductive` proves categorical soundness; `general_stationary_safe`, `general_pipeline_safe`, and `general_step_complete` prove the new requirements with their full quantifiers.

`M3R2.general_all_obligations` and `M3R2.satisfiable` package all seventeen compiler-dependent obligations; `M3.state_iterate` supplies the eighteenth. `general_compatible_with_m1_m2` also proves that this candidate's helper bindings satisfy the earlier milestone contracts. The previous all-fuel soundness, cost, zero-trip, pipeline, and decrementing-divisor proofs remain intact. Concrete witnesses additionally exercise arbitrary signed RHS arithmetic, nested sequencing, compound target guards, preheader aliasing, and rejection of a target invalidated by accumulator havoc.

**Validation.** The extended `Specs/RedTeam.lean` uses no `Specs.Target` compiler stubs or theorem placeholders. Final lean-lsp diagnostics contain no errors or warnings and 1,747 axiom reports. The general candidate, the rejection proofs, and the surviving countermodel all have transitive dependencies within `{propext, Quot.sound}`; the new `strengthen` function itself reports only `propext`.

`./scripts/verify.sh --spec-audit` exited **0**, reporting `GATE 1 SPEC AUDIT PASSED`. It verified 1,747 unique declaration reports, 2,010 kernel declarations (709 in `Specs.Defs`, 1,301 in `Specs.RedTeam`), all 41 anonymous TCB examples, and successful kernel replay. There are zero `sorryAx`, `Classical.choice`, or other non-whitelisted dependencies in the audited TCB and witnesses. Expected warnings while building the target placeholders are not dependencies of the audit proofs.

The passing validation certifies the surviving countermodel as well as the general witness. B1-R2 must be closed before approval.
