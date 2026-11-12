#!/usr/bin/env bash
set -euo pipefail

SCRIPT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [[ "$(basename "$SCRIPT_ROOT")" != "main" && -d "$SCRIPT_ROOT/../main" ]]; then
  cd "$SCRIPT_ROOT/../main"
else
  cd "$SCRIPT_ROOT"
fi

echo "=== Syncing Specs/{Defs,Target,Verify}.lean, blueprint/, CHARTER.md, and gate scripts ==="
for f in Defs.lean Target.lean Verify.lean; do
  cp "../wt-antigravity/Specs/$f" "Specs/$f"
  cp "Specs/$f" "../wt-claude/Specs/$f"
  cp "Specs/$f" "../wt-codex/Specs/$f"
done

cp ../wt-antigravity/blueprint/lemma_dag.json blueprint/lemma_dag.json
cp blueprint/lemma_dag.json ../wt-claude/blueprint/lemma_dag.json
cp blueprint/lemma_dag.json ../wt-codex/blueprint/lemma_dag.json

mkdir -p scripts reviews
cp ../wt-antigravity/scripts/* scripts/
chmod +x scripts/*.sh scripts/*.py

shopt -s nullglob
for rf in ../wt-antigravity/reviews/M*-prelock*.md; do
  dst="reviews/$(basename "$rf")"
  [[ "$rf" -ef "$dst" ]] || cp "$rf" "$dst"
done

SPEC_SHA=$(shasum -a 256 Specs/Defs.lean Specs/Target.lean Specs/Verify.lean blueprint/lemma_dag.json | shasum -a 256 | awk '{print $1}')
echo "$SPEC_SHA" > reviews/current_spec.sha256

GATE_SHA=$(shasum -a 256 CHARTER.md scripts/verify.sh scripts/check_axioms.py scripts/audit_modules.py scripts/sync_specs.sh scripts/sync_for_audit.sh scripts/test_gate_regressions.py | shasum -a 256 | awk '{print $1}')
echo "$GATE_SHA" > reviews/current_gate.sha256

for wt in ../wt-antigravity ../wt-claude ../wt-codex; do
  mkdir -p "$wt/scripts" "$wt/reviews"
  cp CHARTER.md "$wt/CHARTER.md"
  cp scripts/verify.sh scripts/check_axioms.py scripts/audit_modules.py scripts/sync_specs.sh scripts/sync_for_audit.sh scripts/test_gate_regressions.py "$wt/scripts/"
  chmod +x "$wt/scripts/"*.sh "$wt/scripts/"*.py
  cp reviews/current_spec.sha256 reviews/current_gate.sha256 "$wt/reviews/"
  for rf in reviews/M*-prelock*.md; do
    dst="$wt/reviews/$(basename "$rf")"
    [[ "$rf" -ef "$dst" ]] || cp "$rf" "$dst"
  done
done

echo "✅ Synced across all worktrees:"
echo "   Spec Digest: $SPEC_SHA"
echo "   Gate Digest: $GATE_SHA"
