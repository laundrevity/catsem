PRELOCK STATUS: CHANGES REQUESTED

**Milestone 1 — Gate 1 Pre-Lock Round 3 (B2 closure check)**

Spec digest, verified unchanged: `34bcfbacfc9a6ed1b89955c5fdc6efe889ca5c8e2d98e227a688b3e6ef962ea8`

Gate digest, reproduced: `752c99a76f3d90b17b5896a7b1fa5b7be8ac480ece5f66f56e575df4eee9c2e4`

These match [current_spec.sha256](current_spec.sha256) and [current_gate.sha256](current_gate.sha256). The exact recipes are:

```sh
shasum -a 256 Specs/Defs.lean Specs/Target.lean Specs/Verify.lean blueprint/lemma_dag.json | shasum -a 256
shasum -a 256 CHARTER.md scripts/verify.sh scripts/check_axioms.py scripts/audit_modules.py scripts/sync_specs.sh scripts/sync_for_audit.sh | shasum -a 256
```

This review checks [the Round 2 disposition](M1-prelock-r2-disposition.md). B1, N1, N2, and S1 remain resolved as established in [Round 2](M1-prelock-r2.md); their spec bytes have not changed. This round does not reopen the mathematical specification or replace the general candidate.

**Verdict.** The prior log-control, large-output/SIGPIPE, duplicate-inflation, and ordinary-warning bypasses are closed. The module auditor correctly rejects forbidden dependencies in the named declarations it loads. The real audit passes the updated gate. Two **BLOCKING** gaps nevertheless remain: anonymous proof examples are discarded before auditing, and ambiguous object-file selection can make the gate audit a stale module instead of the one it just compiled. Both were reproduced through the complete gate using the unchanged spec and gate-script versions above.

**Verified improvements.**

[verify.sh:28](../scripts/verify.sh#L28) now compiles RedTeam to an object file, writes the log to a file, invokes the parser unconditionally, audits compiled modules, and freshly replays both Target and RedTeam. The previous `echo ... | grep -q` control flow is gone.

[check_axioms.py](../scripts/check_axioms.py) counts unique declarations, rejects forbidden axiom reports even with `info:` prefixes, and rejects non-whitelisted warnings. Duplicate records cannot satisfy a larger minimum; `--forbid-duplicates` rejects duplication outright. Large streams no longer depend on an early-exiting shell pipeline.

[audit_modules.py:50](../scripts/audit_modules.py#L50) inspects stored module declarations and their transitive dependencies independently of printed reports. It rejects non-whitelisted dependencies and local axioms, including unused and private ones. Tests showed that named/private proofs importing admitted target theorems and named/private choice-dependent definitions are rejected with zero `#print axioms` output.

Unsafe implementation auxiliaries are explicitly excluded from the module inventory. That exclusion did not provide a safe-theorem/compiler-wrapper bypass in this review. The separate object-file selection flaw is described in B2-R3b below.

**Requested adversarial regressions.**

The parser harness ran 41 synthetic cases with no unexpected results. Actual compiled-module and compiler-warning probes supplemented those cases.

| Probe | Observed result |
| --- | --- |
| Silent named indirect `Classical.choice`, no reports | Module audit exits 1; empty-log validation also rejects |
| Silent named theorem invoking a `Specs.Target` placeholder, no reports | Module audit exits 1 with `sorryAx` |
| Private named choice/stub dependencies | Module audit exits 1 |
| Unused public/private local axioms | Module audit exits 1 |
| Clean named module with no reports | Module audit passes; Gate 1's empty-log parser rejects the missing report |
| 6,001-line stream with leading or trailing forbidden choice/sorry/custom/native axiom | Parser exits 1 |
| Duplicate report inflation against a larger unique minimum | Parser exits 1 |
| Duplicate records with `--forbid-duplicates` | Parser exits 1 |
| Prefixed forbidden reports, malformed/empty logs, suspicious info continuations | Parser exits 1 |
| Ordinary anonymous `example := by sorry` warning, including location/severity prefixes | Log parser exits 1 |
| Hidden anonymous admitted/choice proofs described below | **Accepted — residual defect** |
| Fresh named choice-dependent audit compiled into a decoy directory while a stale clean module is imported | **Full gate exits 0 — artifact-binding defect** |

**Actual positive gate run.**

The unmodified command was run in the real working tree:

```sh
./scripts/verify.sh --spec-audit
```

It exited **0**, with all four stages executed. The log verifier checked **1,002 unique reports**, the module audit checked **1,132 kernel declarations** (`Specs.Defs=443`, `Specs.RedTeam=689`), and both fresh kernel replays passed. The allowed dependencies were only `propext` and `Quot.sound`.

This confirms the prior general candidate and actual audit artifact remain valid. It does not eliminate the two residual gate bypasses.

**BLOCKING B2-R3a — Anonymous audit examples can escape both channels.**

Lean elaborates `example` under `withoutModifyingEnv` and does not retain its proof as a module constant. This behavior is visible in Lean 4.35.0's `Lean/Elab/MutualDef.lean` around lines 1196–1197. Consequently, module enumeration cannot recover the example's transitive axioms after compilation.

An anonymous example can depend on an admitted target theorem without emitting a direct-sorry warning. The following complete audit file passed:

```lean
import Specs.Target

example (a b : Prop) :
    a ⊓ CatSem.synthesizeGuard a b ≤ b :=
  CatSem.synthesizeGuard_sound a b

theorem clean : True := True.intro
#print axioms clean
```

A second complete file also passed, despite an admitted proof of `False`:

```lean
import Specs.Target

set_option warn.sorry false in
example : False := by sorry

theorem clean : True := True.intro
#print axioms clean
```

The clean report is deliberate: it satisfies the log minimum while the forbidden anonymous proof remains unreported and absent from the object-file declaration inventory. This is not duplicate inflation or the old empty-output bypass.

Both files were tested through the **unmodified full `verify.sh --spec-audit`**, not merely individual checkers. The test used an isolated temporary checkout with byte-identical gate scripts and spec files, its own `.lake/build`, and only the dependency cache shared with the real project. Each run exited **0**:

- log validation accepted one unique clean report;
- module auditing accepted 444 declarations (`Specs.Defs=443`, test `Specs.RedTeam=1`);
- fresh Target and RedTeam replays passed;
- the final gate success message was printed.

An anonymous choice proof also passed compilation, log parsing, and module auditing without any warning suppression:

```lean
example : True := Classical.choice ⟨True.intro⟩
```

Thus merely forcing direct-sorry warnings on would not fix the imported-placeholder or anonymous-choice variants. Ordinary unsuppressed sorry warnings are now correctly rejected; the problem is that these proof terms never become objects available to the module auditor.

**Required closure.** Make every accepted audit proof persistent and subject to the transitive check, or check anonymous proofs during elaboration before they are discarded. One option is to require named audit theorems and enforce that policy; another is a checked-example mechanism that registers/checks the elaborated proof. Retain the existing named/private module checks and warning rejection. A larger log minimum, more `#print axioms` lines, or additional object-file replay cannot recover discarded examples. Add both full-gate counterexamples above as negative regressions.

This finding concerns discarded examples, not the module checker's handling of stored named proof dependencies. The existing named M1 proofs remain accepted and were not changed. The next finding instead concerns which stored module is checked.

**BLOCKING B2-R3b — The newly compiled object need not be the object that is audited.**

[locate_specs_olean_dir](../scripts/verify.sh#L13) selects the first filesystem match for `Specs/Defs.olean` anywhere under `.lake/build`. It is not tied to Lean's module import resolution. [The compile step](../scripts/verify.sh#L29) writes RedTeam next to that selected file, while `audit_modules.py` and `leanchecker` subsequently import `Specs.RedTeam` using the normal search path.

An isolated reproduction used byte-identical real spec files, Lake configuration, and current gate scripts, retaining the exact two digests recorded above:

1. Compile a clean RedTeam module into the canonical `.lake/build/lib/lean/Specs/RedTeam.olean`.
2. Add a second `Specs/Defs.olean` under `.lake/build/decoy`, arranged to be the first `find` result.
3. Replace the temporary project's RedTeam source with a silent named choice dependency and a clean control report:

   ```lean
   import Specs.Target
   noncomputable def forbiddenFresh : Nat :=
     Classical.choice (inferInstance : Nonempty Nat)
   theorem cleanArtifact : True := True.intro
   #print axioms cleanArtifact
   ```

4. Run the unmodified `./scripts/verify.sh --spec-audit`.

The complete gate exited **0**. It compiled the fresh source into the decoy directory, but the module audit and both replays read the stale clean canonical RedTeam module. The module auditor reported `Specs.Defs=443, Specs.RedTeam=1`.

Direct inspection distinguished the artifacts:

| Artifact | SHA-256 / observation |
| --- | --- |
| Fresh decoy `RedTeam.olean` | `12aa2bbeea8100f084b525316a6e4a05482160e883c9e5f3e8b8d7b39b44897f`; `forbiddenFresh` depends on `[Classical.choice]` |
| Stale canonical `RedTeam.olean` | `6c11b14539b4c648b1ae2dca9c2600c09018a43f5ab0120b4518f75b8446b216`; `forbiddenFresh` is unknown |

The allowlist checker works on the module it imports, but that module need not represent the current audit source. This bypass requires an ambiguous/stale build-artifact layout; it does not require modifying the gate scripts or the protected spec files.

**Required closure.** Use Lake's configured artifact location or Lean's actual module resolution rather than the first `find` match. Verify that the path/hash subsequently imported by the module auditor and replayed by `leanchecker` is exactly the freshly produced artifact; reject ambiguous locations. Add this stale-canonical/decoy-output setup as a full-gate negative regression. The issue is artifact binding, separate from possible fail-closed behavior of the `find | head` pipeline itself.

**Reproduction evidence and integrity.**

Temporary harnesses and results are available at:

- `/private/tmp/catsem-m1-r3-log-tests/run_tests.py`, `results.json`, and `summary.json`;
- `/private/tmp/catsem-m1-r3-module-tests/summary.json`;
- `/private/tmp/catsem-m1-r3-module-tests/full_gate_tests.py` and `full_gate_results.json`;
- `/private/tmp/catsem-m1-r3-module-tests/anonymous_imported_stub_full_gate.log`;
- `/private/tmp/catsem-m1-r3-module-tests/hidden_example_sorry_full_gate.log`;
- `/private/tmp/catsem-r3-artifact-exact-clsdwjab/results.json` for the exact-spec stale-artifact reproduction;
- `/private/tmp/catsem-r3-artifact-7g25dzb2/reproduce_exact.py` for its harness;
- `/private/tmp/catsem-m1-r3-spec-audit.log` for the real positive run.

The full-gate harness copies the unchanged scripts/specs into its isolated project and replaces only that project's RedTeam fixture. The real `Specs/RedTeam.lean` was never replaced by an adversarial file, and its compiled object hash remained unchanged during the isolated tests.

Only this review was updated. The charter, specs, blueprint, gate scripts, recorded digests, and RedTeam source were left unchanged. Both recorded digests were rechecked at completion. Approval is withheld for B2-R3a and B2-R3b; close the anonymous-proof coverage and artifact-binding gaps, then repeat the focused gate check.

