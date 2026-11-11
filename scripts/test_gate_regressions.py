#!/usr/bin/env python3
"""End-to-end regression suite for Milestone 1 Gate 1/2 verification scripts.

Runs in an isolated temporary workspace copy (sharing only the read-only
`.lake/packages` dependency cache via symlink) and tests:
  0. Positive control (clean named + anonymous `example` declarations) -> PASS (exit 0)
  1. B2-R3a #1: Anonymous `example` invoking admitted `Specs.Target` stub -> FAIL (exit != 0)
  2. B2-R3a #2: `set_option warn.sorry false in example : False := by sorry` -> FAIL (exit != 0)
  3. B2-R3a #3: Anonymous `example` using `Classical.choice` -> FAIL (exit != 0)
  4. B2-R3b: Stale clean canonical `RedTeam.olean` + decoy `.lake/build/decoy/Specs/Defs.olean`
             + fresh `RedTeam.lean` with silent named `Classical.choice` -> FAIL (exit != 0)
  5. B2-R3b hash-binding & `unsafe example` checks -> FAIL (exit != 0)
  6. Real `Specs/RedTeam.lean` positive run (if available locally or in `../wt-codex`) -> PASS (exit 0)
"""

import os
import shutil
import subprocess
import sys
import tempfile

CLEAN_CONTROL_REDTEAM = """import Specs.Target

namespace CatSem.RedTeamTest

theorem clean_refl (a : Prop) : a ≤ a := le_rfl

example (a b : Prop) : a ⊓ b ≤ a := inf_le_left

namespace Nested
example : (1 : Nat) + 1 = 2 := rfl
end Nested

end CatSem.RedTeamTest

#print axioms CatSem.RedTeamTest.clean_refl
"""

COUNTEREXAMPLE_1_IMPORTED_STUB = """import Specs.Target

example (a b : Prop) :
    a ⊓ CatSem.synthesizeGuard a b ≤ b :=
  CatSem.synthesizeGuard_sound a b

theorem clean : True := True.intro
#print axioms clean
"""

COUNTEREXAMPLE_2_HIDDEN_SORRY = """import Specs.Target

set_option warn.sorry false in
example : False := by sorry

theorem clean : True := True.intro
#print axioms clean
"""

COUNTEREXAMPLE_3_ANON_CHOICE = """import Specs.Target

example : True := Classical.choice ⟨True.intro⟩

theorem clean : True := True.intro
#print axioms clean
"""

COUNTEREXAMPLE_4_FRESH_NAMED_CHOICE = """import Specs.Target

noncomputable def forbiddenFresh : Nat :=
  Classical.choice (inferInstance : Nonempty Nat)

theorem cleanArtifact : True := True.intro
#print axioms cleanArtifact
"""

COUNTEREXAMPLE_5_UNSAFE_EXAMPLE = """import Specs.Target

namespace Sneaky
unsafe example : Nat := 0
end Sneaky

theorem clean : True := True.intro
#print axioms clean
"""


def setup_isolated_workspace(repo_root: str, tmp_root: str) -> str:
    proj = os.path.join(tmp_root, "proj")
    os.makedirs(proj, exist_ok=True)

    for top_file in (
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "Specs.lean",
        "Proofs.lean",
        "CHARTER.md",
    ):
        src = os.path.join(repo_root, top_file)
        if os.path.isfile(src):
            shutil.copy2(src, os.path.join(proj, top_file))

    for sub_dir in ("Specs", "blueprint", "scripts"):
        src_dir = os.path.join(repo_root, sub_dir)
        dst_dir = os.path.join(proj, sub_dir)
        os.makedirs(dst_dir, exist_ok=True)
        for fn in os.listdir(src_dir):
            s = os.path.join(src_dir, fn)
            if os.path.isfile(s):
                shutil.copy2(s, os.path.join(dst_dir, fn))

    # Remove any copied RedTeam.lean / PostImplAudit.lean so tests control RedTeam.lean explicitly
    for extra in ("RedTeam.lean", "PostImplAudit.lean"):
        p = os.path.join(proj, "Specs", extra)
        if os.path.exists(p):
            os.remove(p)

    lake_dir = os.path.join(proj, ".lake")
    os.makedirs(lake_dir, exist_ok=True)
    orig_packages = os.path.realpath(os.path.join(repo_root, ".lake", "packages"))
    if not os.path.isdir(orig_packages):
        raise RuntimeError(f"Missing .lake/packages at {orig_packages}")
    os.symlink(orig_packages, os.path.join(lake_dir, "packages"))
    return proj


def write_redteam(proj: str, content: str) -> None:
    rt_path = os.path.join(proj, "Specs", "RedTeam.lean")
    with open(rt_path, "w", encoding="utf-8") as f:
        f.write(content)


def run_spec_audit(proj: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["bash", "scripts/verify.sh", "--spec-audit"],
        cwd=proj,
        capture_output=True,
        text=True,
    )


def assert_true(cond: bool, msg: str, proc: subprocess.CompletedProcess[str] | None = None) -> None:
    if not cond:
        print(f"❌ REGRESSION TEST FAILED: {msg}", file=sys.stderr)
        if proc is not None:
            print("--- STDOUT ---", file=sys.stderr)
            print(proc.stdout, file=sys.stderr)
            print("--- STDERR ---", file=sys.stderr)
            print(proc.stderr, file=sys.stderr)
        sys.exit(1)


def main() -> int:
    repo_root = os.path.realpath(os.path.join(os.path.dirname(__file__), ".."))
    print(f"=== Setting up isolated gate regression workspace from {repo_root} ===")

    with tempfile.TemporaryDirectory(prefix="catsem_gate_regressions_") as tmp_root:
        proj = setup_isolated_workspace(repo_root, tmp_root)

        # 0. Positive baseline control (leaves a clean canonical RedTeam.olean in .lake/build/lib/lean/Specs/)
        print("[0/6] Running positive baseline control (clean named + anonymous examples)...")
        write_redteam(proj, CLEAN_CONTROL_REDTEAM)
        p0 = run_spec_audit(proj)
        assert_true(p0.returncode == 0, "Clean control should pass verify.sh --spec-audit", p0)
        print("  -> PASS (exit 0)")

        # 1. Counterexample 1 (B2-R3a #1): anonymous example using admitted Specs.Target stub
        print("[1/6] Testing B2-R3a #1 (anonymous example referencing Specs.Target stub)...")
        write_redteam(proj, COUNTEREXAMPLE_1_IMPORTED_STUB)
        p1 = run_spec_audit(proj)
        comb1 = p1.stdout + "\n" + p1.stderr
        assert_true(p1.returncode != 0, "Counterexample 1 (imported target stub in example) must fail", p1)
        assert_true("sorryAx" in comb1, "Counterexample 1 failure must identify transitive sorryAx", p1)
        print("  -> REJECTED as expected (caught transitive sorryAx in anonymous example)")

        # 2. Counterexample 2 (B2-R3a #2): set_option warn.sorry false in example : False := by sorry
        print("[2/6] Testing B2-R3a #2 (set_option warn.sorry false in anonymous example := by sorry)...")
        write_redteam(proj, COUNTEREXAMPLE_2_HIDDEN_SORRY)
        p2 = run_spec_audit(proj)
        comb2 = p2.stdout + "\n" + p2.stderr
        assert_true(p2.returncode != 0, "Counterexample 2 (warn.sorry false example) must fail", p2)
        assert_true("sorryAx" in comb2, "Counterexample 2 failure must identify sorryAx", p2)
        print("  -> REJECTED as expected (caught suppressed sorryAx in anonymous example)")

        # 3. Counterexample 3 (B2-R3a #3): anonymous example using Classical.choice
        print("[3/6] Testing B2-R3a #3 (anonymous example using Classical.choice)...")
        write_redteam(proj, COUNTEREXAMPLE_3_ANON_CHOICE)
        p3 = run_spec_audit(proj)
        comb3 = p3.stdout + "\n" + p3.stderr
        assert_true(p3.returncode != 0, "Counterexample 3 (anonymous Classical.choice) must fail", p3)
        assert_true("Classical.choice" in comb3, "Counterexample 3 failure must identify Classical.choice", p3)
        print("  -> REJECTED as expected (caught Classical.choice in anonymous example)")

        # 4. Counterexample 4 (B2-R3b): stale clean canonical RedTeam.olean + decoy Specs/Defs.olean + fresh named choice
        print("[4/6] Testing B2-R3b (stale canonical RedTeam.olean + decoy .lake/build/decoy/Specs/Defs.olean)...")
        write_redteam(proj, CLEAN_CONTROL_REDTEAM)
        p_prep = run_spec_audit(proj)
        assert_true(p_prep.returncode == 0, "Prep clean build for Counterexample 4 must pass", p_prep)

        canonical_defs = os.path.join(proj, ".lake", "build", "lib", "lean", "Specs", "Defs.olean")
        canonical_rt = os.path.join(proj, ".lake", "build", "lib", "lean", "Specs", "RedTeam.olean")
        assert_true(os.path.isfile(canonical_defs) and os.path.isfile(canonical_rt), "Canonical .oleans must exist")

        decoy_specs_dir = os.path.join(proj, ".lake", "build", "decoy", "Specs")
        os.makedirs(decoy_specs_dir, exist_ok=True)
        shutil.copy2(canonical_defs, os.path.join(decoy_specs_dir, "Defs.olean"))

        write_redteam(proj, COUNTEREXAMPLE_4_FRESH_NAMED_CHOICE)
        p4 = run_spec_audit(proj)
        comb4 = p4.stdout + "\n" + p4.stderr
        assert_true(p4.returncode != 0, "Counterexample 4 (decoy Defs.olean + stale canonical RedTeam.olean) must fail", p4)
        assert_true("Ambiguous .olean" in comb4, "Counterexample 4 must reject ambiguous .olean layout", p4)
        print("  -> REJECTED as expected (ambiguous decoy .olean detected and blocked)")

        # 5. Direct SHA-256 mismatch & unsafe example checks (after removing decoy tree)
        print("[5/6] Testing direct .olean SHA-256 tamper rejection, fresh named choice, and unsafe example...")
        shutil.rmtree(os.path.join(proj, ".lake", "build", "decoy"))

        p5a = run_spec_audit(proj)
        comb5a = p5a.stdout + "\n" + p5a.stderr
        assert_true(p5a.returncode != 0 and "Classical.choice" in comb5a, "Fresh named choice without decoy must fail", p5a)

        tampered_sha = "0" * 64
        p5b = subprocess.run(
            ["python3", "scripts/audit_modules.py", "--verify-olean", f"Specs.Defs={canonical_defs}:{tampered_sha}"],
            cwd=proj,
            capture_output=True,
            text=True,
        )
        assert_true(p5b.returncode != 0 and "SHA-256 mismatch" in (p5b.stdout + p5b.stderr), "Tampered SHA-256 must fail", p5b)

        write_redteam(proj, COUNTEREXAMPLE_5_UNSAFE_EXAMPLE)
        p5c = run_spec_audit(proj)
        comb5c = p5c.stdout + "\n" + p5c.stderr
        assert_true(p5c.returncode != 0 and "FORBIDDEN UNSAFE EXAMPLE" in comb5c, "Unsafe example must fail", p5c)
        print("  -> REJECTED as expected (SHA-256 tamper, named choice, and unsafe example all blocked)")

        # 6. Positive check on real Specs/RedTeam.lean if available in repo or ../wt-codex
        real_rt_candidates = [
            os.path.join(repo_root, "Specs", "RedTeam.lean"),
            os.path.join(repo_root, "..", "wt-codex", "Specs", "RedTeam.lean"),
            os.path.join(repo_root, "..", "main", "Specs", "RedTeam.lean"),
        ]
        real_rt = next((p for p in real_rt_candidates if os.path.isfile(p)), None)
        if real_rt is not None:
            print(f"[6/6] Running positive end-to-end gate check on real RedTeam suite ({real_rt})...")
            shutil.copy2(real_rt, os.path.join(proj, "Specs", "RedTeam.lean"))
            p6 = run_spec_audit(proj)
            assert_true(p6.returncode == 0, "Real Specs/RedTeam.lean must pass verify.sh --spec-audit", p6)
            print("  -> PASS (real Specs/RedTeam.lean passed full verify.sh --spec-audit)")
        else:
            print("[6/6] Real Specs/RedTeam.lean not present in adjacent paths; skipped optional check.")

    print("✅ ALL GATE REGRESSION TESTS PASSED!")
    return 0


if __name__ == "__main__":
    sys.exit(main())
