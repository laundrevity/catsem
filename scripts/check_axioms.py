#!/usr/bin/env python3
import argparse
import re
import sys

ALLOWED = {"propext", "Quot.sound"}
NO_AX_RE = re.compile(r"^'([^']+)' does not depend on any axioms$")
HAS_AX_RE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$")
BENIGN_MATHLIB_WARN_RE = re.compile(
    r"^(warning:\s+.*:\s+imports `Mathlib\..*` from package `mathlib`, which is designed for use with the module system"
    r"|⚠ \[\d+/\d+\] (Built|Replayed) Specs\.Defs$)"
)
LOC_PREFIX_RE = re.compile(r"^[^:\n]+:\d+:\d+:\s*(info|warning|error)(?:\([^)]+\))?:\s*(.*)$")
SEV_PREFIX_RE = re.compile(r"^(info|warning|error):\s*(?:[^:\n]+:\d+:\d+:\s*)?(.*)$")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Fail-closed Lean axiom and compiler log verifier.")
    parser.add_argument("legacy_min", nargs="?", type=int, help="Minimum unique declaration count (legacy positional)")
    parser.add_argument("--file", type=str, default=None, help="Read compiler output from file instead of stdin")
    parser.add_argument("--min-unique", type=int, default=None, help="Minimum unique audited declarations required")
    parser.add_argument("--forbid-duplicates", action="store_true", help="Fail if any declaration is reported twice")
    parser.add_argument(
        "--allow-eval-info",
        action="store_true",
        help="Allow non-axiom #eval info diagnostics (still scans them for sorry/axiom leaks)",
    )
    return parser.parse_args()


def check_axiom_record(body: str, seen_decls: set[str], forbid_duplicates: bool) -> bool:
    m_no = NO_AX_RE.match(body)
    if m_no:
        decl = m_no.group(1)
        if forbid_duplicates and decl in seen_decls:
            print(f"❌ FAIL: Duplicate axiom report for '{decl}'.")
            sys.exit(1)
        seen_decls.add(decl)
        return True

    m_has = HAS_AX_RE.match(body)
    if m_has:
        decl = m_has.group(1)
        if forbid_duplicates and decl in seen_decls:
            print(f"❌ FAIL: Duplicate axiom report for '{decl}'.")
            sys.exit(1)
        axioms = [a.strip() for a in m_has.group(2).split(",") if a.strip()]
        if not axioms:
            print(f"❌ FAIL: Empty axiom list in 'depends on axioms' line for '{decl}'.")
            sys.exit(1)
        forbidden = [a for a in axioms if a not in ALLOWED]
        if forbidden:
            print(f"❌ FAIL: '{decl}' depends on forbidden axiom(s): {forbidden} (allowed: {sorted(ALLOWED)})")
            sys.exit(1)
        seen_decls.add(decl)
        return True

    return False


def main() -> int:
    args = parse_args()
    min_unique = args.min_unique if args.min_unique is not None else (args.legacy_min if args.legacy_min is not None else 1)
    if min_unique < 1:
        print("❌ FAIL: min_unique must be >= 1.")
        return 1

    if args.file is not None:
        with open(args.file, "r", encoding="utf-8") as f:
            raw = f.read()
    else:
        raw = sys.stdin.read()

    if not raw.strip():
        print("❌ FAIL: Empty compiler/axiom log input.")
        return 1

    seen_decls: set[str] = set()
    lines = raw.splitlines()
    in_eval_info_block = False

    for line in lines:
        s = line.strip()
        if not s:
            continue

        if BENIGN_MATHLIB_WARN_RE.match(s):
            in_eval_info_block = False
            continue

        if check_axiom_record(s, seen_decls, args.forbid_duplicates):
            in_eval_info_block = False
            continue

        sev = None
        payload = s
        m_loc = LOC_PREFIX_RE.match(s)
        if m_loc:
            sev, payload = m_loc.group(1), m_loc.group(2).strip()
        else:
            m_sev = SEV_PREFIX_RE.match(s)
            if m_sev:
                sev, payload = m_sev.group(1), m_sev.group(2).strip()

        if sev in ("warning", "error"):
            print(f"❌ FAIL: Compiler {sev} detected: {line}")
            return 1

        if sev == "info":
            if check_axiom_record(payload, seen_decls, args.forbid_duplicates):
                in_eval_info_block = False
                continue
            if not args.allow_eval_info:
                print(f"❌ FAIL: Unexpected info diagnostic in strict axiom log: {line}")
                return 1
            lowered = payload.lower()
            if "depends on axioms" in lowered or "does not depend on any axioms" in lowered or "sorryax" in lowered or "declaration uses 'sorry'" in lowered:
                print(f"❌ FAIL: Suspicious axiom/sorry content inside info diagnostic: {line}")
                return 1
            in_eval_info_block = True
            continue

        if in_eval_info_block and args.allow_eval_info:
            lowered = s.lower()
            if "depends on axioms" in lowered or "does not depend on any axioms" in lowered or "sorryax" in lowered or "warning:" in lowered or "error:" in lowered:
                print(f"❌ FAIL: Suspicious continuation line in info block: {line}")
                return 1
            continue

        print(f"❌ FAIL: Unrecognized output line during fail-closed axiom audit: {line}")
        return 1

    if len(seen_decls) < min_unique:
        print(f"❌ FAIL: Expected at least {min_unique} unique audited declarations, saw {len(seen_decls)}.")
        return 1

    print(
        f"✅ Fail-closed log audit verified {len(seen_decls)} unique declarations "
        f"(only {sorted(ALLOWED)} permitted; zero non-whitelisted warnings)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
