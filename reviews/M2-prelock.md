PRELOCK STATUS: APPROVED

Milestone 2 Gate 1 pre-lock review — Lean specification semantics.

Spec digest recorded in `reviews/current_spec.sha256`:

```text
34de6ec95f03f6715abc6c3486050d33a4a1d5e831c9594c655f9261c2940910
```

Reproduced with `shasum -a 256 Specs/Defs.lean Specs/Target.lean Specs/Verify.lean blueprint/lemma_dag.json | shasum -a 256`. The protected specifications were unchanged. Review inputs were `CHARTER.md`, the recorded digest, and the three Lean specification files. The requested gate command was used for validation; scripts and build tooling were not audited.

No blocking mathematical or anti-degeneracy defect was found. The new `CatSem.RedTeam.M2` section in `Specs/RedTeam.lean` supplies total computable functions satisfying every M2 target, with constructive proofs independent of the `Specs.Target` placeholders.

**NON-BLOCKING — Operational semantics and cost are coherent.** `execStmt` evaluates an assignment RHS in the incoming environment, updates exactly its destination, executes sequences in forward order, and selects a branch using the environment at that branch. `evalBlock` evaluates the return in the resulting environment. `stmtGuardCost` charges the condition plus only the selected branch and threads updated environments through sequences; `execBlockCheckCost` adds the return-expression check cost in the final environment. Structural recursion and decidable variable equality make these definitions total and computable. Statements have pure, total RHS expressions, so traps and UB arise only in the terminal expression and retain M1's distinct observable outcomes.

The concrete witnesses check self-updates, preservation of other variables, saving a divisor before clobbering its source, returns that read updated variables, correct backward substitution order, and guards/checks whose behavior changes after assignment. No contradictory state-invariance premise is needed.

**NON-BLOCKING — All obligations have a constructive implementation witness.** `M2.wp` substitutes through arbitrary pure expressions and guards, reverses sequential composition for pullbacks, and combines both conditional branches. `M2.synthStmt` normalizes guards and reuses the independently proved `M1R2.synth`. `M2.blockOpt` prunes a provably selected top-level branch, obtains terminal-divisor facts through the statement pullback, and applies the independently proved `M1R2.opt` under those post-state facts. It does not assume that the entry context survives assignments.

`M2.Obligations` restates all 15 compiler-dependent M2 targets with their original quantifiers and premises; `M2.all_obligations` and `M2.satisfiable` construct a joint witness. The remaining, compiler-independent state/lifting target is proved by `M2.state_lift_bridge`. Coverage is:

| Target group | Independent witness theorems |
| --- | --- |
| State-transfer/lifting equivalence | `state_lift_bridge` |
| Pullback denotation and sequencing | `wp_denote`, `wp_seq` |
| Guard denotation, forcing universal property, diamond rewrite soundness | `synthStmt_denote`, `synthStmt_universal`, `synth_diamond_sound` |
| Literal, assignment, and safe-diamond guard normalization | `synth_literal`, `synth_assign`, `synth_diamond` |
| Guarded and concrete block soundness | `block_guarded`, `block_sound` |
| Literal/clobber/diamond/dead-branch reductions and clobber trap preservation | `literal_elim`, `clobber_elim`, `diamond_elim`, `dead_elim`, `clobber_trap` |

The matching signatures in `Specs/Verify.lean` preserve these parameters and side conditions; its M2 computable wrappers name all three compiler functions.

**NON-BLOCKING — Degenerate fallbacks and finite fixture tables are excluded.** `identity_rejected`, `bot_synthesis_rejected`, `top_synthesis_rejected`, and `raw_imp_rejected` prove that those candidate strategies cannot satisfy the contract. `literal_family_injective` and `finite_fixture_rejected` exhibit an unbounded family of distinct blocks: every fresh-variable member must lose its two checked divisions, so a finite table that returns all remaining blocks unchanged fails. `finite_guard_fixture_rejected` similarly rules out eventual raw-implication fallback on nonzero literal guard queries. These are quantified negative proofs, not just tests of a fixed list of fixtures.

**NON-BLOCKING — Positive premises and trap protections are non-vacuous.** Concrete proofs exhibit a true entry context and successful clobber optimization; both safe-diamond arms with cost (3 → 1); literal elimination with cost (2 → 0); and dead-branch cancellation with cost zero. A dead-branch example assigns to a variable used in its own entry guard, making that guard false afterward while preserving the correct result. Safe diamonds also work with aliased source/destination variables and negative literals. `wrapped_diamond` checks a sequentially wrapped diamond outside the named benchmark body shapes.

The clobber tests show why its positive capability needs `d ≠ x`: aliasing produces a trap, which the candidate preserves. `stale_nonzero_fact_rejected` gives an environment satisfying the pre-context where an unsafe unchecked rewrite changes `.trap` to `.ub`; exact operational soundness rejects it. The zero-literal diamond witness also confirms that the `n ≠ 0` condition is substantive.

**SCOPE-NOTE — Observation and optimization coverage.** This milestone models finite structured statement trees, pure assignments, and terminal `Outcome` observation. It does not specify loops, effectful/trapping assignment RHSs, or final-environment equivalence as a separate observable. The candidate additionally preserves its statement transfer under the entry context. Cost measures object-IR guards and division checks, not arithmetic operations, assignment work, compiler runtime, or machine instructions. Positive capability obligations range over unbounded syntactic families; they do not require complete simplification of every semantically equivalent block or a particular analysis algorithm. These limits are consistent with the stated milestone and do not permit the rejected finite-fixture fallbacks.

**Validation.** Final lean-lsp diagnostics for `Specs/RedTeam.lean` report no errors or warnings and 1,315 axiom reports. The existential witness proof has no remaining goals. In particular, `M2.wp` has no axiom dependencies; `M2.synthStmt` and `M2.blockOpt` use only `propext`; and `M2.all_obligations`, `M2.satisfiable`, the state/lifting bridge, and both finite-fixture rejection proofs use only `{propext, Quot.sound}`.

`./scripts/verify.sh --spec-audit` completed with exit code **0** and `GATE 1 SPEC AUDIT PASSED`. Its output confirms 1,315 unique declaration reports, a complete audit of 1,512 kernel declarations (554 in `Specs.Defs`, 958 in `Specs.RedTeam`), all 35 anonymous `Specs.Defs` examples, and successful kernel replay. There are zero `sorryAx`, `Classical.choice`, or other non-whitelisted dependencies in the audited TCB and witnesses. Expected placeholder warnings from building `Specs.Target` are separate from the clean audit-file diagnostics; none of those placeholder declarations is used by the witness proofs.

Review artifacts: the `CatSem.RedTeam.M2` section of `Specs/RedTeam.lean` and this report. No specification changes are requested.
