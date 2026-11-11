# Disposition of Gate 1 Pre-Lock Review (Round 1)
Reviewed Spec Digest: `2a18d05064e8e9e296f347c1b3d154d674a3e9075b84ce80b66f9cdf2bf0c430`

- **BLOCKING B1 (Fixture-only optimizer loophole) — ACCEPTED & RESOLVED:**
  Added parametric AST constructors (`mkCancelExpr`, `mkDualDivExpr`) and universally quantified obligations over arbitrary `PureExpr` operands, conjunctive `GuardIR` contexts, and binary `Expr` subtrees (`optimizeExpr_elim_checkedDiv_param`, `optimizeExpr_cancel_div_param`, `optimizeExpr_compositional_binary`, `optimizeExpr_known_ctx_elim_param`, `optimizeExpr_unknown_ctx_dedup_param`, `optimizeExpr_zero_div_trap_param`).
- **BLOCKING B2 (Fail-closed axiom allowlist & script sync) — ACCEPTED & RESOLVED:**
  Added in-Lean kernel transitive axiom verification (`Lean.collectAxioms` allowlist `{propext, Quot.sound}`) in `Specs/Verify.lean`, added fail-closed `scripts/check_axioms.py` in `scripts/verify.sh`, added `--spec-audit` mode for Gate 1 execution, and synced `CHARTER.md` + `scripts/` to all worktrees.
- **NON-BLOCKING N1 (Narrow residual normalization) — ACCEPTED & RESOLVED:**
  Added parametric normalization obligations (`synthesizeGuardIR_top_right`, `synthesizeGuardIR_bot_left`, `synthesizeGuardIR_top_left_nonZero`, `synthesizeGuardIR_discharge_conj_left`, `synthesizeGuardIR_discharge_conj_right`, `synthesizeGuardIR_dedup_conj`).
- **NON-BLOCKING N2 (Host evaluation order vs. modeled check cost) — ACCEPTED & RESOLVED:**
  Refactored `evalExpr` in `Specs/Defs.lean` to match left-operand outcomes before evaluating right operands, aligning Lean host short-circuiting with `execCheckCost` while remaining extensionally equal to `bindOutcome2`.
- **SCOPE-NOTE S1 (Arithmetic, UB, and fallback cost model) — ACKNOWLEDGED IN CHARTER:**
  Explicitly documented in `CHARTER.md` under Milestone 1 Scope Assumptions.
