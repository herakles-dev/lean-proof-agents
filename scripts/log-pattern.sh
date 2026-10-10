#!/usr/bin/env bash
# log-pattern.sh — append a winning proof recipe to PROOF_PATTERNS.md (the flywheel).
#
# The proving loop is faster the more recipes it has recorded. Instead of hand-editing the
# table, every solve appends one normalized row via this script (called by /climb step 6, or
# by hand after a /prove solve).
#
#   scripts/log-pattern.sh "<goal shape>" "<recipe: tactic/lemma>" "<seen in>"
#
# Example:
#   scripts/log-pattern.sh "a ^ p = a in ZMod p, prime p" "ZMod.pow_card a (needs [Fact p.Prime])" "C0011"
#
# Idempotent: if an identical goal-shape row already exists, it is not duplicated.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FILE="$ROOT/PROOF_PATTERNS.md"
MARKER="<!-- append new patterns below this line -->"

goal="${1:-}"; recipe="${2:-}"; seen="${3:-}"
if [[ -z "$goal" || -z "$recipe" ]]; then
  echo "usage: log-pattern.sh \"<goal shape>\" \"<recipe>\" [\"<seen in>\"]" >&2
  exit 1
fi
[[ -f "$FILE" ]] || { echo "not found: $FILE" >&2; exit 2; }
grep -qF "$MARKER" "$FILE" || { echo "marker missing in $FILE; add: $MARKER" >&2; exit 2; }

# Escape pipes so we don't break the markdown table.
esc() { printf '%s' "$1" | sed 's/|/\\|/g'; }
row="| $(esc "$goal") | $(esc "$recipe") | $(esc "$seen") |"

# Dedup on the goal-shape cell (first column).
if grep -qF "| $(esc "$goal") |" "$FILE"; then
  echo "already logged (goal shape present): $goal"
  exit 0
fi

printf '%s\n' "$row" >> "$FILE"
echo "logged: $row"
