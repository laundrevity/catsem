#!/usr/bin/env bash
set -euo pipefail

MODE="${1:-full}"
cd "$(dirname "$0")/.."

TMP_DIR=$(mktemp -d "${TMPDIR:-/tmp}/catsem_verify.XXXXXX")
cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT

sha256_file() {
  shasum -a 256 "$1" | awk '{print $1}'
}

resolve_module_olean() {
  python3 scripts/audit_modules.py --resolve-olean "$1"
}

locate_specs_olean_dir() {
  local defs_olean target_olean defs_dir target_dir
  defs_olean=$(resolve_module_olean Specs.Defs)
  target_olean=$(resolve_module_olean Specs.Target)
  defs_dir=$(dirname "$defs_olean")
  target_dir=$(dirname "$target_olean")
  if [[ "$defs_dir" != "$target_dir" ]]; then
    echo "❌ FAIL: Specs.Defs ($defs_dir) and Specs.Target ($target_dir) resolved to different directories!" >&2
    exit 1
  fi
  echo "$defs_dir"
}

compile_bound_module() {
  local mod_name="$1"
  local src_file="$2"
  local out_olean="$3"
  local log_file="$4"

  if [[ ! -f "$src_file" ]]; then
    echo "❌ FAIL: Source file '$src_file' does not exist for '$mod_name'!" >&2
    exit 1
  fi

  rm -f "$out_olean"
  if ! lake env lean -R . -o "$out_olean" "$src_file" > "$log_file" 2>&1; then
    cat "$log_file"
    echo "❌ FAIL: $src_file failed to compile!" >&2
    exit 1
  fi

  if [[ ! -s "$out_olean" ]]; then
    echo "❌ FAIL: Compiler did not produce non-empty artifact '$out_olean' for '$mod_name'!" >&2
    exit 1
  fi

  local out_sha
  out_sha=$(sha256_file "$out_olean")
  python3 scripts/audit_modules.py --verify-olean "${mod_name}=${out_olean}:${out_sha}"
}

replay_bound_module() {
  local mod_name="$1"
  local expected_olean="$2"
  local expected_sha="$3"

  python3 scripts/audit_modules.py --verify-olean "${mod_name}=${expected_olean}:${expected_sha}"
  lake env leanchecker --fresh "$mod_name"
  python3 scripts/audit_modules.py --verify-olean "${mod_name}=${expected_olean}:${expected_sha}"
}

if [[ "$MODE" == "--spec-audit" ]]; then
  echo "=== [Gate 1: 1/4] Building Specs & binding canonical .olean paths via Lean.findOLean ==="
  lake build Specs
  SPECS_OLEAN_DIR=$(locate_specs_olean_dir)
  DEFS_OLEAN=$(resolve_module_olean Specs.Defs)
  TARGET_OLEAN=$(resolve_module_olean Specs.Target)
  DEFS_SHA=$(sha256_file "$DEFS_OLEAN")
  TARGET_SHA=$(sha256_file "$TARGET_OLEAN")
  DEFS_SRC_SHA=$(sha256_file "Specs/Defs.lean")
  python3 scripts/audit_modules.py \
    --verify-olean "Specs.Defs=${DEFS_OLEAN}:${DEFS_SHA}" \
    --verify-olean "Specs.Target=${TARGET_OLEAN}:${TARGET_SHA}"

  echo "=== [Gate 1: 2/4] Compiling Specs/RedTeam.lean & running fail-closed log verifier ==="
  REDTEAM_OLEAN="$SPECS_OLEAN_DIR/RedTeam.olean"
  REDTEAM_SRC_SHA=$(sha256_file "Specs/RedTeam.lean")
  compile_bound_module "Specs.RedTeam" "Specs/RedTeam.lean" "$REDTEAM_OLEAN" "$TMP_DIR/redteam.log"
  REDTEAM_SHA=$(sha256_file "$REDTEAM_OLEAN")
  python3 scripts/check_axioms.py --file "$TMP_DIR/redteam.log" --min-unique 1 --allow-eval-info

  echo "=== [Gate 1: 3/4] Running complete kernel module + frontend-example audit (Specs.Defs + Specs.RedTeam) ==="
  python3 scripts/audit_modules.py \
    --expect-olean "Specs.Defs=${DEFS_OLEAN}:${DEFS_SHA}" \
    --expect-source "Specs.Defs=Specs/Defs.lean:${DEFS_SRC_SHA}" \
    --expect-olean "Specs.RedTeam=${REDTEAM_OLEAN}:${REDTEAM_SHA}" \
    --expect-source "Specs.RedTeam=Specs/RedTeam.lean:${REDTEAM_SRC_SHA}" \
    Specs.Defs Specs.RedTeam

  echo "=== [Gate 1: 4/4] Replaying hash-bound Specs.Target and Specs.RedTeam in leanchecker ==="
  replay_bound_module "Specs.Target" "$TARGET_OLEAN" "$TARGET_SHA"
  replay_bound_module "Specs.RedTeam" "$REDTEAM_OLEAN" "$REDTEAM_SHA"

  echo "✅ GATE 1 SPEC AUDIT PASSED (unconditional log + hash-bound module & frontend-example audit + leanchecker replay)."
  exit 0
fi

echo "=== [1/6] Pulling candidate Submission.lean and Codex audit suites ==="
cp ../wt-claude/Proofs/Submission.lean Proofs/Submission.lean
if [[ -f ../wt-codex/Specs/RedTeam.lean ]]; then
  cp ../wt-codex/Specs/RedTeam.lean Specs/RedTeam.lean
fi
if [[ -f ../wt-codex/Specs/PostImplAudit.lean ]]; then
  cp ../wt-codex/Specs/PostImplAudit.lean Specs/PostImplAudit.lean
fi

echo "=== [2/6] Building Specs and Proofs.Submission & binding canonical .olean artifacts ==="
lake build Specs Proofs.Submission
SPECS_OLEAN_DIR=$(locate_specs_olean_dir)
DEFS_OLEAN=$(resolve_module_olean Specs.Defs)
TARGET_OLEAN=$(resolve_module_olean Specs.Target)
SUBMISSION_OLEAN=$(resolve_module_olean Proofs.Submission)
DEFS_SHA=$(sha256_file "$DEFS_OLEAN")
TARGET_SHA=$(sha256_file "$TARGET_OLEAN")
SUBMISSION_SHA=$(sha256_file "$SUBMISSION_OLEAN")
DEFS_SRC_SHA=$(sha256_file "Specs/Defs.lean")
SUBMISSION_SRC_SHA=$(sha256_file "Proofs/Submission.lean")
python3 scripts/audit_modules.py \
  --verify-olean "Specs.Defs=${DEFS_OLEAN}:${DEFS_SHA}" \
  --verify-olean "Specs.Target=${TARGET_OLEAN}:${TARGET_SHA}" \
  --verify-olean "Proofs.Submission=${SUBMISSION_OLEAN}:${SUBMISSION_SHA}"

echo "=== [3/6] Verifying signatures, computability, and fail-closed log audit (Specs/Verify.lean) ==="
VERIFY_OLEAN="$SPECS_OLEAN_DIR/Verify.olean"
compile_bound_module "Specs.Verify" "Specs/Verify.lean" "$VERIFY_OLEAN" "$TMP_DIR/verify.log"
VERIFY_SHA=$(sha256_file "$VERIFY_OLEAN")
cat "$TMP_DIR/verify.log"
python3 scripts/check_axioms.py --file "$TMP_DIR/verify.log" --min-unique 60 --forbid-duplicates

echo "=== [4/6] Compiling Codex Gate 1 & Gate 2 regression suites ==="
REDTEAM_OLEAN="$SPECS_OLEAN_DIR/RedTeam.olean"
REDTEAM_SRC_SHA=$(sha256_file "Specs/RedTeam.lean")
compile_bound_module "Specs.RedTeam" "Specs/RedTeam.lean" "$REDTEAM_OLEAN" "$TMP_DIR/redteam.log"
REDTEAM_SHA=$(sha256_file "$REDTEAM_OLEAN")
python3 scripts/check_axioms.py --file "$TMP_DIR/redteam.log" --min-unique 1 --allow-eval-info

SUB_AUDIT_ARGS=(
  --expect-olean "Specs.Defs=${DEFS_OLEAN}:${DEFS_SHA}"
  --expect-source "Specs.Defs=Specs/Defs.lean:${DEFS_SRC_SHA}"
  --expect-olean "Proofs.Submission=${SUBMISSION_OLEAN}:${SUBMISSION_SHA}"
  --expect-source "Proofs.Submission=Proofs/Submission.lean:${SUBMISSION_SRC_SHA}"
)
SUB_AUDIT_MODS=(Specs.Defs Proofs.Submission)

if [[ -f Specs/PostImplAudit.lean ]]; then
  POSTAUDIT_OLEAN="$SPECS_OLEAN_DIR/PostImplAudit.olean"
  POSTAUDIT_SRC_SHA=$(sha256_file "Specs/PostImplAudit.lean")
  compile_bound_module "Specs.PostImplAudit" "Specs/PostImplAudit.lean" "$POSTAUDIT_OLEAN" "$TMP_DIR/postaudit.log"
  POSTAUDIT_SHA=$(sha256_file "$POSTAUDIT_OLEAN")
  python3 scripts/check_axioms.py --file "$TMP_DIR/postaudit.log" --min-unique 1 --allow-eval-info
  SUB_AUDIT_ARGS+=(
    --expect-olean "Specs.PostImplAudit=${POSTAUDIT_OLEAN}:${POSTAUDIT_SHA}"
    --expect-source "Specs.PostImplAudit=Specs/PostImplAudit.lean:${POSTAUDIT_SRC_SHA}"
  )
  SUB_AUDIT_MODS+=(Specs.PostImplAudit)
fi

echo "=== [5/6] Running split kernel module + frontend-example audits & hash-bound leanchecker replays ==="
python3 scripts/audit_modules.py \
  --expect-olean "Specs.Defs=${DEFS_OLEAN}:${DEFS_SHA}" \
  --expect-source "Specs.Defs=Specs/Defs.lean:${DEFS_SRC_SHA}" \
  --expect-olean "Specs.RedTeam=${REDTEAM_OLEAN}:${REDTEAM_SHA}" \
  --expect-source "Specs.RedTeam=Specs/RedTeam.lean:${REDTEAM_SRC_SHA}" \
  Specs.Defs Specs.RedTeam

python3 scripts/audit_modules.py "${SUB_AUDIT_ARGS[@]}" "${SUB_AUDIT_MODS[@]}"

replay_bound_module "Proofs.Submission" "$SUBMISSION_OLEAN" "$SUBMISSION_SHA"
replay_bound_module "Specs.Verify" "$VERIFY_OLEAN" "$VERIFY_SHA"
replay_bound_module "Specs.RedTeam" "$REDTEAM_OLEAN" "$REDTEAM_SHA"
if [[ -f Specs/PostImplAudit.lean ]]; then
  replay_bound_module "Specs.PostImplAudit" "$POSTAUDIT_OLEAN" "$POSTAUDIT_SHA"
fi

if [[ "$MODE" == "--kernel-only" ]]; then
  echo "✅ KERNEL CHECKS PASSED (--kernel-only). Run scripts/sync_for_audit.sh and Gate 2 Codex review before final acceptance."
  exit 0
fi

echo "=== [6/6] Checking Gate 2 independent review sign-off ==="
SUB_SHA=$(sha256_file "Proofs/Submission.lean")
if [[ -f ../wt-codex/reviews/M1-postimpl.md ]]; then
  cp ../wt-codex/reviews/M1-postimpl.md reviews/M1-postimpl.md
fi
python3 - "$SUB_SHA" << 'PY'
import pathlib, sys
sub_sha = sys.argv[1]
p = pathlib.Path("reviews/M1-postimpl.md")
if not p.exists():
    print("❌ FAIL: Missing reviews/M1-postimpl.md.")
    sys.exit(1)
txt = p.read_text(encoding="utf-8")
if sub_sha not in txt or "STATUS: APPROVED" not in txt:
    print(f"❌ FAIL: reviews/M1-postimpl.md lacks STATUS: APPROVED for SHA256 {sub_sha}.")
    sys.exit(1)
print(f"✅ Gate 2 review sign-off verified for Submission SHA256 {sub_sha}.")
PY

echo "✅ ALL KERNEL & INDEPENDENT REVIEW CHECKS PASSED!"
