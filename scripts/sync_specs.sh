#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "=== Syncing Specs/ and blueprint/ from wt-antigravity -> main, wt-claude, wt-codex ==="
cp ../wt-antigravity/Specs/*.lean Specs/
cp ../wt-antigravity/blueprint/lemma_dag.json blueprint/

cp Specs/*.lean ../wt-claude/Specs/
cp blueprint/lemma_dag.json ../wt-claude/blueprint/

cp Specs/*.lean ../wt-codex/Specs/
cp blueprint/lemma_dag.json ../wt-codex/blueprint/

echo "✅ Specs synced across all worktrees."
