# CatSem Project Charter

## Guiding Principle
Develop an executable compiler in Lean 4 certified as a constructive realization of specified categorical structures, paired with operational equivalence proofs over an independent concrete evaluator.

## Foundational & Execution Discipline
1. Kernel axioms: Only `propext` and `Quot.sound` are permitted. `sorryAx` and `Classical.choice` are forbidden across all definitions, compiler passes, and proofs.
2. Executability: Compiler passes (`synthesizeGuardIR`, `optimizeExpr`, etc.) must be total, computable Lean functions (no `noncomputable`).
3. Trust boundary: Milestone 1 trusts the Lean 4 kernel and Lean runtime evaluation of computable functions; binary machine-code verification is deferred.
4. Separation of concerns:
   - `Specs/Defs.lean`: Trusted Computing Base (IR syntax, concrete evaluators, semantic bridges, static/dynamic cost observers).
   - `Specs/Target.lean`: Stub signatures for compiler functions and target correctness/capability theorems.
   - `Proofs/Submission.lean`: Executable compiler implementations and constructive proofs.
   - `Specs/RedTeam.lean`: Gate 1 pre-lock specification and TCB audit (imports `Specs.Target`).
   - `Specs/PostImplAudit.lean`: Gate 2 post-implementation adversarial audit against actual compiler code (imports `Proofs.Submission`).
5. Anti-degeneracy: Every executable milestone must rule out identity compilers, constant-false guard fallbacks, and unsimplified residual wrappers via concrete positive reduction witnesses and negative trap-preservation tests.

## Milestone 1 Scope Assumptions (S1)
- Arithmetic uses unbounded Lean `Int` with Euclidean division (`Int.ediv`); fixed-width machine overflow and truncation-toward-zero are deferred.
- `Outcome.ub` is modeled as a distinct observable failure value under exact outcome equality on all environments satisfying `ctx`; behavior outside `ctx` is unconstrained.
- `execCheckCost` measures abstract object-IR guard and division-check evaluations; unknown-context deduplication bounds apply on non-zero divisors while zero-divisor paths preserve `.trap` without claiming check-cost reduction on trapping inputs.
