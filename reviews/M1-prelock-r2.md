PRELOCK STATUS: CHANGES REQUESTED

**Milestone 1 — Gate 1 Pre-Lock Re-Review (Round 2)**

Current spec digest: `34bcfbacfc9a6ed1b89955c5fdc6efe889ca5c8e2d98e227a688b3e6ef962ea8`

This matches [current_spec.sha256](current_spec.sha256) and was reproduced with:

```sh
shasum -a 256 Specs/Defs.lean Specs/Target.lean Specs/Verify.lean blueprint/lemma_dag.json | shasum -a 256
```

This supersedes the Round 1 review of digest `2a18d05064e8e9e296f347c1b3d154d674a3e9075b84ce80b66f9cdf2bf0c430` and checks [the disposition](M1-prelock-r1-disposition.md). The spec digest excludes the charter and gate scripts; their inspected versions were:

| File | SHA-256 |
| --- | --- |
| `CHARTER.md` | `80672e03087a12ff63eba9022b57e95795975cd2263bca3ebb5c8b3b6b215db9` |
| `scripts/verify.sh` | `1eca2d88ca5dfcbf31eebd240f4f93d54d1ccaa03fb0a7236d48fea35aaf5c2a` |
| `scripts/check_axioms.py` | `a331d22e0aa3284c1080972b50c745b6504ce115827d9427349f246384711fb3` |

**Verdict.** B1, N1, N2, and S1 are resolved for the stated milestone scope. A general constructive candidate satisfies every revised M1 obligation. The individual axiom checkers work, but B2 remains **BLOCKING** because Gate 1's shell control flow can bypass the parser. The real `--spec-audit` command returned success without actually running its advertised external allowlist check.

| Prior finding | Re-review result |
| --- | --- |
| B1: fixture-only compiler | **RESOLVED.** Parametric obligations reject the old candidate; a structural, parameterized candidate satisfies them. |
| B2: axiom enforcement | **PARTIALLY RESOLVED / BLOCKING.** Both checkers reject forbidden dependencies when invoked, but the Gate 1 wrapper can skip invocation. |
| N1: residual normalization | **RESOLVED.** All six added laws have independent proofs; the old synthesizer is rejected. |
| N2: evaluator traversal/cost mismatch | **RESOLVED.** Explicit left-outcome matching skips the RHS after trap/UB; the runtime probe confirms it. |
| S1: arithmetic, UB, and cost scope | **RESOLVED AS A SCOPE-NOTE.** Explicit in [CHARTER.md:18](../CHARTER.md#L18). |

**B1 — The old optimizer is rejected, and all revised obligations remain satisfiable.**

[fixture_optimizer_rejected](../Specs/RedTeam.lean#L3023) proves that **no guard synthesizer** can make the original `M1.opt` satisfy the revised contract. On the renamed benchmark, it retains two checked divisions, contradicting the new parametric requirement of zero. This proof uses an optimizer obligation, independently of the guard-normalization failure.

The [M1R2 candidate](../Specs/RedTeam.lean#L2627) is total computable Lean code. It recursively discovers nonzero facts in conjunctions and optimizes expression subtrees. It eliminates checks on pure denominators known nonzero and cancels either multiplication orientation. Its top-context rule recognizes the shared-divisor shape over arbitrary `PureExpr` operands. The rules contain no fixed variable identifiers or named benchmark constants.

[UpdatedObligations](../Specs/RedTeam.lean#L2957) packages all nine original compiler-dependent requirements plus the six normalization and six parametric optimizer requirements. [all_obligations](../Specs/RedTeam.lean#L3002) proves every field; [updated_obligations_satisfiable](../Specs/RedTeam.lean#L3017) explicitly constructs the function pair. The three independent TCB obligations—lifting bridge, addition compatibility, and checked-division compatibility—remain proved in `M1`. No admitted target compiler or theorem is invoked.

The positive witness uses `x = var7 + 1`, `y = var9 * 3`, `d = 2`, and an environment returning 4. It produces `val 14`, reduces unknown-context check cost from 2 to 1, and eliminates checks in a nested known-context arithmetic expression. [renamed_reduction](../Specs/RedTeam.lean#L3060) compares the new zero-check output with the old candidate's two checks. These are satisfying, non-vacuous instances. The contract certifies these general rule families, not global optimizer completeness.

**N1 — The requested normalization is enforced.**

The candidate proves top-right, bottom-left, top-left nonzero, both conjunctive discharge laws, and duplicate-conjunct normalization for arbitrary operands. [old_synth_rejected](../Specs/RedTeam.lean#L3033) proves that `M1.synth` fails the new top-left law. A runtime check returns `nonZero(var7)` directly rather than an implication wrapper. General implications remain valid residual syntax when no mandated simplification applies.

**N2 and S1 — Evaluation order and scope are aligned.**

The new `evalExpr` matches the left outcome before evaluating the right operand in all five binary constructors. The former tracing-environment probe was rerun with a left checked-division trap and a right expression reading variable 42. It returned `.trap` without the right-side read; `execCheckCost` returned 1. Kernel-checked strict-outcome, trap/UB, and cost witnesses still compile.

The charter now explicitly specifies unbounded Lean `Int`/Euclidean division, exact observable UB semantics within the assumed context, unconstrained behavior outside that context, and abstract object-IR check costs. The observer does not claim to measure interpreter overhead or improve trapping-input cost.

**BLOCKING B2-R2 — Gate 1 still fails open.**

The new [Verify command](../Specs/Verify.lean#L13) correctly uses `Lean.collectAxioms` transitively and rejects dependencies outside `{propext, Quot.sound}`. The Python parser correctly rejects forbidden axioms in recognized reports. However, [verify.sh:17–19](../scripts/verify.sh#L17) calls that parser only if an `echo | grep -q` condition succeeds. Two bypasses were reproduced:

1. **No reports means no check.** A silent declaration with an indirect `Classical.choice` dependency compiled with exit 0 and passed the exact Gate 1 filtering fragment. A theorem invoking admitted `CatSem.synthesizeGuard_sound` also compiled silently; adding `#print axioms` exposed `[propext, sorryAx]`. The final replay of `Specs.Target` at line 25 does not inspect RedTeam.

2. **Large output can skip the check even when reports exist.** Under `pipefail`, `grep -q` exits after its first match, and the still-writing `echo` can fail with SIGPIPE. The observed pipeline status was **141**, making the `if` condition false. A log beginning with a forbidden `Classical.choice` report followed by 5,000 allowed reports passed the exact shell fragment with exit 0 and no parser output. Direct Python parsing of the same log exited 1. Independent repeats with `sorryAx` and a custom axiom also passed the fragment. The later `grep -q "sorry"` check is vulnerable to the same issue.

This also affected the real final run: `./scripts/verify.sh --spec-audit` exited **0** and emitted **1,002 axiom reports**, but did **not** emit the Python checker's success line. The parser was skipped. A separate direct invocation of `check_axioms.py 1002` on the actual RedTeam output succeeded.

Before approval, require an **unconditional, complete transitive audit of RedTeam and the TCB**, rejecting missing or incomplete coverage. Do not decide whether to audit from optional log text. Feed output through a file or here-string rather than an early-exiting consumer pipeline; any remaining warning greps need the same treatment. A minimum count is insufficient as a coverage check: duplicate reports count toward it, and arbitrary `info:` lines are ignored.

The new [persistent RedTeam audit](../Specs/RedTeam.lean#L3082) protects this artifact: it enumerates the RedTeam namespace and imported `Specs.Defs` declarations, rejects forbidden transitive dependencies, and emits their reports. Injected-choice and imported-stub tests both failed as intended. This independent protection does not repair the wrapper's general fail-open control flow.

**Checker and execution tests.**

The exact command body from `Specs/Verify.lean` was extracted verbatim into isolated temporary harnesses. Its SHA-256 was `8a4c34e1b38789218c7f095d84cd409dbdad1f0595fa521a54e8f27b64be3d78`. This tests the actual implementation without importing an unfinished submission. Deliberately forbidden test declarations were not added to the permanent audit.

| Test | Observed result |
| --- | --- |
| Lean checker: clean proof, `propext`, `Quot.sound` | Exit 0 |
| Lean checker: indirect `Classical.choice` | Exit 1 |
| Lean checker: two-hop custom axiom | Exit 1 |
| Lean checker: `sorryAx` or unknown declaration | Exit 1 |
| Python: allowed/no-axiom records | Exit 0 |
| Python: choice, sorry, custom, native-reduction axiom records | Exit 1 |
| Python: empty, malformed, unknown-line, insufficient-record input | Exit 1 |
| Gate fragment: silent choice / imported-placeholder dependence | **Exit 0 — defect** |
| Gate fragment: large forbidden-axiom report stream | **Exit 0 — defect** |
| Persistent RedTeam checker: injected choice / target-placeholder dependence | Expected compilation failure |
| Actual `./scripts/verify.sh --spec-audit` | Exit 0; external parser skipped |
| Direct `check_axioms.py 1002` on complete audit output | Exit 0; all records allowed |

The isolated harnesses and results are under `/private/tmp/catsem-m1-r2-gate-tests/`; the actual gate log is `/private/tmp/catsem-m1-r2-spec-audit-final.log`. The silent placeholder probe was:

```lean
import Specs.Target
theorem delegatedSound (a b : Prop) :
    a ⊓ CatSem.synthesizeGuard a b ≤ b :=
  CatSem.synthesizeGuard_sound a b
```

Adding `#print axioms delegatedSound` reveals the forbidden dependency. The large-output probe supplied a leading `'bad' depends on axioms: [Classical.choice]` line followed by thousands of valid reports to the unmodified filtering fragment with `set -euo pipefail`.

**Proof and artifact integrity.**

RedTeam compiles without errors or warnings. Its **1,002 transitive dependency checks** found no `sorryAx`, `Classical.choice`, or other non-whitelisted axiom. Only `propext` and `Quot.sound` occur. Runtime checks also produced the normalized atomic guard, `val 14`, unknown-context cost 1, and zero checks on the renamed benchmark.

Only `Specs/RedTeam.lean` and this review were changed. The spec files, charter, disposition, and gate scripts were not modified; the recorded digest still matches. The full submission-copying mode was not run. Close B2-R2, record the corrected gate-script version, and repeat Gate 1 before locking.

