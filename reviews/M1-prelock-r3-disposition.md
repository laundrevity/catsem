# Disposition of Gate 1 Pre-Lock Review (Round 3)
Reviewed Spec Digest (unchanged): `34bcfbacfc9a6ed1b89955c5fdc6efe889ca5c8e2d98e227a688b3e6ef962ea8`
Reviewed Prior Gate Digest: `752c99a76f3d90b17b5896a7b1fa5b7be8ac480ece5f66f56e575df4eee9c2e4`
Updated Gate Digest: `3dda332bf2969c124a976c9ec6a456d9346742d011fa00ec144ced85c231736a`

- **B1, N1, N2, S1:** Confirmed resolved in Rounds 2–3; `Specs/{Defs,Target,Verify}.lean` and `blueprint/lemma_dag.json` remain byte-for-byte unchanged.
- **BLOCKING B2-R3a (Anonymous `example` declarations escaping module axiom enumeration) — ACCEPTED & RESOLVED:**
  1. Extended `scripts/audit_modules.py` with a full Lean Frontend elaboration & `InfoTree` kernel-snapshot pass (`run_source_frontend_audit`) executed on every audited module's `.lean` source file alongside `.olean` module-constant enumeration.
  2. For each audited source file, Lean elaborates with `infoState.enabled := true`, rejects all compiler errors and non-whitelisted warnings, verifies `infoState.enabled` remains active, and inspects `(env.setExporting false).checked.get.constants.foldStage2` across both the final environment and every saved `ContextInfo.env` snapshot in `infoState.trees` (capturing transient `_example` declarations elaborated inside `withoutModifyingEnv`).
  3. Every persistent and transient declaration is checked with `Lean.collectAxioms` against `{propext, Quot.sound}`; `unsafe example` and local `axiom` declarations are rejected outright, and exact 1-to-1 parity (`auditedExamples == expectedExamples`) is enforced against parsed `Lean.Parser.Command.example` syntax nodes. This closes all three anonymous counterexamples: admitted `Specs.Target` stub invocations, `set_option warn.sorry false in example := by sorry`, and `Classical.choice` examples.
- **BLOCKING B2-R3b (Ambiguous `.olean` path selection & artifact-binding gap) — ACCEPTED & RESOLVED:**
  1. Removed `find .lake/build | head -n 1` from `scripts/verify.sh`. Canonical `.olean` paths are now resolved exclusively through `Lean.findOLean` (`scripts/audit_modules.py --resolve-olean`), with a fail-closed scan (`check_no_ambiguous_project_oleans`) across both `.lake/build` and every `LEAN_PATH` entry that rejects any duplicate/decoy `Specs/*` or `Proofs/*` `.olean` tree.
  2. `compile_bound_module` deletes any pre-existing target `.olean` before invoking `lean -o`, hashes both `.lean` source and newly produced `.olean` with SHA-256, and immediately verifies via `Lean.findOLean` (`--verify-olean`) that Lean resolves the module to that exact canonical file and SHA-256.
  3. `scripts/audit_modules.py` (`--expect-olean`, `--expect-source`) verifies inside Lean (`Lean.findOLean` + `IO.FS.realPath`) and in Python (pre- and post-audit SHA-256 checks) that both module enumeration and Frontend import resolution load the exact bound `.olean` and `.lean` bytes, and `replay_bound_module` re-verifies `Lean.findOLean` path + SHA-256 immediately before and after every `leanchecker --fresh` replay.
- **Gate 2 Environment Isolation & Sync Hardening:**
  1. Split Stage `[5/6]` in `scripts/verify.sh` into two `scripts/audit_modules.py` invocations—first `Specs.Defs Specs.RedTeam`, and second `Specs.Defs Proofs.Submission` (plus `Specs.PostImplAudit` when present)—so `Specs.RedTeam` (which imports `Specs.Target`) is never imported into the same Lean environment as `Proofs.Submission`, while keeping `Specs/Verify.lean` compilation + `check_axioms.py` in Stage `[3/6]` and `leanchecker --fresh Specs.Verify` in Stage `[5/6]`.
  2. Added `scripts/test_gate_regressions.py` testing a clean positive control, all four full-gate Round 3 counterexamples (imported target stub `example`, `warn.sorry false` `example := by sorry`, `Classical.choice` `example`, and stale canonical `RedTeam.olean` + decoy `.lake/build/decoy/Specs/Defs.olean`), direct SHA-256 tamper & `unsafe example` probes, and the full real `Specs/RedTeam.lean` suite inside an isolated temporary checkout.
  3. Updated `scripts/sync_specs.sh` to pull `../wt-antigravity/scripts/*` and `reviews/M1-prelock-r3-disposition.md` into `main` before computing `reviews/current_gate.sha256` and syncing across all worktrees.

### Digest Recipes
```sh
shasum -a 256 Specs/Defs.lean Specs/Target.lean Specs/Verify.lean blueprint/lemma_dag.json | shasum -a 256
shasum -a 256 CHARTER.md scripts/verify.sh scripts/check_axioms.py scripts/audit_modules.py scripts/sync_specs.sh scripts/sync_for_audit.sh scripts/test_gate_regressions.py | shasum -a 256
```
