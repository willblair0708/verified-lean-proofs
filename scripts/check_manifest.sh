#!/usr/bin/env bash
# Keeps proofs.yaml (the machine-readable index that erdos-fc-sync ingests)
# honest: every theorem advertised in the manifest must actually be audited in
# Audit.lean, and every audited theorem must be advertised. No silent drift.
set -euo pipefail
fail() { echo "FAIL: $*" >&2; exit 1; }

manifest_thms="$(grep -E '^[[:space:]]*theorem:' proofs.yaml | sed -E 's/.*theorem:[[:space:]]*//; s/"//g' | sort -u)"
audited_thms="$(grep -E '^#print axioms ' Audit.lean | sed -E 's/^#print axioms //' | sort -u)"

if [ "$manifest_thms" != "$audited_thms" ]; then
  echo "proofs.yaml theorems:"; echo "$manifest_thms" | sed 's/^/  /'
  echo "Audit.lean theorems:";  echo "$audited_thms"  | sed 's/^/  /'
  fail "proofs.yaml and Audit.lean disagree on the tracked theorem set"
fi
echo "PASS: manifest matches the audit ($(echo "$manifest_thms" | grep -c . ) theorem(s))"
