#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "=== [1/4] Pulling candidate Submission.lean from wt-claude ==="
cp ../wt-claude/Proofs/Submission.lean Proofs/Submission.lean

echo "=== [2/4] Building Proofs.Submission ==="
lake build Proofs.Submission

echo "=== [3/4] Verifying exact theorem signatures & auditing kernel axioms ==="
if ! AXIOM_OUT=$(lake env lean Specs/Verify.lean 2>&1); then
  echo "$AXIOM_OUT"
  echo "❌ FAIL: Specs/Verify.lean failed to compile (missing or mismatched theorem signatures)!"
  exit 1
fi
echo "$AXIOM_OUT"

if echo "$AXIOM_OUT" | grep -q "sorryAx"; then
  echo "❌ FAIL: Proofs/Submission.lean still contains 'sorry' (sorryAx detected)!"
  exit 1
fi

if echo "$AXIOM_OUT" | grep -q "Classical.choice"; then
  echo "❌ FAIL: Non-constructive proof detected (Classical.choice is forbidden in topos internal logic)!"
  exit 1
fi

echo "=== [4/4] Replaying environment from scratch in leanchecker ==="
lake env leanchecker --fresh Proofs.Submission

echo "✅ ALL KERNEL CHECKS PASSED! Proofs/Submission.lean is constructively sound and faithful."
