PRELOCK STATUS: CHANGES REQUESTED

**Milestone 1 — Gate 1 Pre-Lock Specification Review**

Recorded spec digest: `2a18d05064e8e9e296f347c1b3d154d674a3e9075b84ce80b66f9cdf2bf0c430`

The digest in [current_spec.sha256](current_spec.sha256) was reproduced from the reviewed working-tree bytes with:

```sh
shasum -a 256 Specs/Defs.lean Specs/Target.lean Specs/Verify.lean blueprint/lemma_dag.json | shasum -a 256
```

The digest covers those four files, in that order. [CHARTER.md](../CHARTER.md) and [scripts/verify.sh](../scripts/verify.sh) were inspected separately. Only `Specs/RedTeam.lean` and this review were changed. This is a specification review, not Gate 2 approval of a submission.

**Verdict.** The M1 mathematical obligations are satisfiable, and no in-context outcome-soundness contradiction was found. The added audit supplies total computable candidate functions, independent proofs of every M1 obligation, and positive and negative runtime cases. Approval is withheld because the obligations admit a fixture-only optimizer and the supplied verification gate does not enforce the charter's axiom allowlist.

**BLOCKING B1 — Fixed fixtures do not rule out a trivial, benchmark-only implementation.**

The capability requirements at [Target:373](../Specs/Target.lean#L373), [Target:380](../Specs/Target.lean#L380), [Target:386](../Specs/Target.lean#L386), and [Target:393](../Specs/Target.lean#L393) name two exact ASTs and two exact context syntaxes. They impose no reduction requirement on renamed, substituted, or nested instances.

The computable audit candidate [M1.opt](../Specs/RedTeam.lean#L2343) recognizes only these cases:

| Context and expression | Returned expression |
| --- | --- |
| `nonZero(var 0)`, `m1BenchExpr` | `uncheckedDiv(var 1, var 0) + var 2` |
| `nonZero(var 0)`, `m1CancelExpr` | `var 1` |
| `top`, `m1BenchExpr` | A nonzero-guard branch selecting the fast expression or the original benchmark |
| Everything else | The original expression |

This is not an unsound implementation: its exact outcome theorem holds for **every** expression and environment satisfying the supplied context. Its false branch genuinely retains the source trap. Nevertheless, it performs no optimization outside the fixtures. [renamed_untouched](../Specs/RedTeam.lean#L2458) and [renamed_still_checks](../Specs/RedTeam.lean#L2461) prove that an alpha-renamed copy of the same benchmark is unchanged and still has two checked divisions.

The guard candidate and this optimizer jointly satisfy all nine compiler-dependent M1 obligations in [candidate_obligations](../Specs/RedTeam.lean#L2488). The lifting bridge and both compatibility theorems are proved independently as well. No target placeholder is invoked. The optimizer does not need to call the synthesizer: their semantic contracts are independent.

Before locking a general guarded-optimizer milestone, specify a minimum family of reductions over arbitrary relevant variable names/pure operands and contexts, with positive witnesses and outcome preservation. Renaming/substitution or context-compositionality requirements would make the intended scope clearer. Alternatively, explicitly narrow M1 to a fixture-specialized compiler and revise the anti-triviality expectation. The present obligations do not certify a generic optimization capability.

**BLOCKING B2 — The verification path does not enforce the allowed proof dependencies.**

[CHARTER.md:7](../CHARTER.md#L7) permits only `propext` and `Quot.sound`. [Verify:321](../Specs/Verify.lean#L321) onward merely prints dependencies. [scripts/verify.sh:16](../scripts/verify.sh#L16) rejects `sorryAx` alone; it has no rejection for `Classical.choice` or another non-whitelisted axiom. The computability wrappers at [Verify:257](../Specs/Verify.lean#L257) address compiler executability, not proof dependencies.

The installed Lean 4.35.0 `LeanChecker.lean` fresh-check implementation replays the environment; it has no project-specific axiom allowlist. Kernel acceptance therefore does not imply compliance with this charter. A proof using choice can pass the script's dependency test even though it is forbidden here.

Add a fail-closed check of the **transitive dependencies of the audited definitions, compiler passes, and proofs**, permitting only the two named axioms. Merely detecting axioms present somewhere in imported Mathlib would be the wrong check. Keep the compiler computability checks and kernel replay as separate protections. The full `scripts/verify.sh` was not run during this review because it copies a submission from another worktree at line 7.

**NON-BLOCKING N1 — Residual normalization is specified only narrowly.**

The always-`.imp` synthesizer is excluded by syntactic self-discharge. But a synthesizer that returns `.top` for syntactically identical inputs and `.imp a b` otherwise satisfies denotation, universality, and self-discharge. [unsimplified_top_residual](../Specs/RedTeam.lean#L2466) proves that the accepted candidate leaves `imp top (nonZero p)` intact.

Thus broader normalization, residual-size bounds, and general guard-cost reduction are not established. Add laws such as top-antecedent simplification if those are intended M1 deliverables; otherwise document the limited normalization guarantee. This does not invalidate the existing denotation theorem.

**NON-BLOCKING N2 — Modeled IR cost and actual evaluator traversal must be distinguished.**

[evalExpr](../Specs/Defs.lean#L252) supplies both recursively evaluated operands to `bindOutcome2`. Lean's runtime evaluates the right operand even when the left result is `.trap`. [execCheckCost](../Specs/Defs.lean#L309) instead omits right-side checks after a left trap or UB.

A Lean runtime probe used a tracing environment returning 7, with:

```lean
trapExpr := checkedDiv (lit 1) (lit 0)
rhs      := checkedDiv (var 42) (lit 1)
```

Evaluating `add trapExpr rhs` printed `read variable 42` before returning `.trap`; the cost observer returned `1` without that read. This was an execution probe, not a kernel theorem about host evaluation order.

The kernel-checked outcome equations still implement the intended left-biased object-IR semantics: all subtree evaluators are total and trap/UB are returned data. The observer is internally consistent as an **abstract object-IR check count**, not a measurement of host interpreter work. State that boundary explicitly, or implement sequencing by matching the left result before evaluating the right. A single evaluator returning outcome plus cost, with projection proofs, would prevent future drift. If M1 is intended to certify actual Lean evaluator work, this issue must be promoted to blocking.

**SCOPE-NOTE S1 — Arithmetic, UB, contexts, and performance have deliberately limited meanings.**

The IR uses unbounded Lean `Int` arithmetic and Euclidean division. [integer_division_scope](../Specs/RedTeam.lean#L2598) checks that `checkedDiv(-3, 2)` yields `val(-2)`; machine-width overflow and truncation-toward-zero semantics are not modeled.

UB is a distinct observable outcome, not an arbitrary-behavior refinement relation. Exact outcome equality forbids changing a source trap to UB or a fabricated value on any environment satisfying the context. It also forbids replacing `0 * trappingExpr` with zero. Conversely, behavior outside the context is unconstrained: [outside_context_ub](../Specs/RedTeam.lean#L2526) exhibits UB for the known-context optimized benchmark when the nonzero context is false. That is not an in-context soundness counterexample.

The unknown-context performance bound applies only when the divisor is nonzero. The accepted candidate costs two modeled checks on the zero-divisor path versus the source's one, while preserving the trap. No general check-cost, expression-size, or total-runtime non-regression guarantee is stated.

**Kernel-checked evidence and satisfiability.**

The [M1 audit section](../Specs/RedTeam.lean#L2323) imports `Specs.Target` as required but never invokes its admitted compiler functions or theorems. [compiler_obligations_satisfiable](../Specs/RedTeam.lean#L2499) explicitly constructs a function pair satisfying the compiler contract. The three non-compiler TCB obligations are independently established by `lift_bridge`, `addition_compatible`, and `checked_division_compatible`.

| Question | Result and witness |
| --- | --- |
| Can the global identity optimizer pass? | No: [identity_rejected](../Specs/RedTeam.lean#L2530) contradicts the required zero checked-division count. |
| Can an always-false synthesizer pass? | No: [constant_bot_rejected](../Specs/RedTeam.lean#L2537) contradicts the denotation of top implying top. |
| Can an always-unsimplified implication pass? | No: [raw_imp_rejected](../Specs/RedTeam.lean#L2545) contradicts syntactic self-discharge. |
| Can a false runtime guard merely keep the slow fallback? | That shape retains two checks and a branch: [false_fallback_still_checks](../Specs/RedTeam.lean#L2551). |
| Are the positive obligations non-vacuous? | [positive_reduction_witness](../Specs/RedTeam.lean#L2507) supplies a satisfying environment, value 6, source cost 2, known-context cost 0, and unknown-context cost 1. |
| Is trap preservation real? | [zero_trap_witness](../Specs/RedTeam.lean#L2517) retains the source trap. [trap_to_ub_rejected](../Specs/RedTeam.lean#L2586) and [dropping_strict_operand_rejected](../Specs/RedTeam.lean#L2592) reject unsound alternatives. |
| Are strict outcomes and cost edge cases checked? | [strict_outcomes](../Specs/RedTeam.lean#L2561), [short_circuit_costs](../Specs/RedTeam.lean#L2569), and [guard_short_circuit](../Specs/RedTeam.lean#L2576) cover trap/UB precedence, strict multiplication, unselected branches, operand failures, and guard short-circuiting. |
| Does the semantic bridge lose state or outcome information? | No: [lift_bridge](../Specs/RedTeam.lean#L2408) proves equivalence to exact same-state runtime outcome equality, constructively. |

Lean-LSP diagnostics for the extended file were clean. The independent `synth` and `opt` were also executed with `#eval`. A full dependency scan checked **362 declarations**: named audit declarations, relevant constructors/projections, and the M1 TCB including derived decidable-equality instances. Every dependency set was a subset of `{propext, Quot.sound}`; **zero `sorryAx` or `Classical.choice` dependencies** were found. Both candidate compiler functions have no axiom dependencies. `evalExpr`, `evalGuard`, `liftEval`, and `liftBinarySem` have none; `execCheckCost` uses only `propext`.

The current target stubs remain intentionally unproved and were not counted as approved implementations. Resolve B1 and B2, record the resulting scope and enforcement changes, regenerate the spec digest where applicable, and repeat Gate 1 before locking.

