#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

cp ../wt-claude/Proofs/Submission.lean Proofs/Submission.lean
cp Proofs/Submission.lean ../wt-codex/Proofs/Submission.lean

SUB_SHA=$(shasum -a 256 Proofs/Submission.lean | awk '{print $1}')
echo "$SUB_SHA" > reviews/current_submission.sha256
cp reviews/current_submission.sha256 ../wt-codex/reviews/current_submission.sha256

echo "✅ Submission synced to main and wt-codex for Gate 2 audit (Submission SHA256: $SUB_SHA)"
