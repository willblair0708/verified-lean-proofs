#!/usr/bin/env bash
# Verification gate for the proof index.
#
# Fails if:
#   1. any tracked source contains a literal `sorry` or `admit`, or
#   2. `Audit.lean` reports `sorryAx` for any headline theorem, or
#   3. any headline theorem depends on an axiom outside the allowed kernel set.
#
# Run locally with the Mathlib cache primed:
#   lake exe cache get && lake build && bash scripts/check_axioms.sh
set -euo pipefail

ALLOWED='[propext, Classical.choice, Quot.sound]'
fail() { echo "FAIL: $*" >&2; exit 1; }

# 1. No literal sorry / admit in the hosted proofs.
if grep -rnoE '\b(sorry|admit)\b' ErdosProblems/ ; then
  fail "literal sorry/admit in ErdosProblems/"
fi

# 2/3. Build the audit and inspect the axiom report.
report="$(lake env lean Audit.lean 2>&1)"
echo "$report"

echo "$report" | grep -qiE '(^| )error' && fail "Audit.lean did not compile cleanly"
echo "$report" | grep -q 'sorryAx'        && fail "a headline theorem depends on sorryAx"

# Every "depends on axioms:" line must equal the allowed set exactly.
seen=0
while IFS= read -r line; do
  case "$line" in
    *"depends on axioms:"*)
      seen=$((seen+1))
      axioms="${line#*depends on axioms: }"
      [ "$axioms" = "$ALLOWED" ] || fail "unexpected axioms -> $line"
      ;;
  esac
done <<< "$report"

[ "$seen" -gt 0 ] || fail "no axiom report produced (is Audit.lean wired up?)"
echo "PASS: $seen headline theorem(s) clean, axioms = $ALLOWED"
