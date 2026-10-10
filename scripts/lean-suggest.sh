#!/usr/bin/env bash
# lean-suggest.sh — ask Lean itself which lemmas close a goal (exact?/apply?/hint/simp?).
#
# The argument is the "<binders> : <goal>" part of an `example`:
#   scripts/lean-suggest.sh "(a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2"     # default: exact?
#   scripts/lean-suggest.sh --apply "(n : ℕ) : n ∣ n !"
#   scripts/lean-suggest.sh --hint  "(n : ℕ) : 0 ≤ n"
#   scripts/lean-suggest.sh --simp  "(n : ℕ) : n + 0 = n"
#
# ⚠ TRUSTED INPUT ONLY: the argument is interpolated into Lean source and EXECUTED (tactics/`#eval`
# can run arbitrary IO). Never pass text from an untrusted source (web pages, issues, models).
# Requires: bash, mktemp, grep, and the repo's Lean toolchain (elan/lake).
#
# Runs in the repo's Mathlib env (everything in `Mathlib` is in scope). Complements
# mathlib-search.sh: that finds by NAME, this finds by GOAL.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
. "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"

tac="exact?"
case "${1:-}" in
  --apply) tac="apply?"; shift ;;
  --hint)  tac="hint";   shift ;;
  --simp)  tac="simp?";  shift ;;
  --exact) tac="exact?"; shift ;;
  -h|--help|"") echo "usage: lean-suggest.sh [--apply|--hint|--simp] \"<binders> : <goal>\"" >&2; exit 1 ;;
esac
sig="${*:-}"
[[ -z "$sig" ]] && { echo "usage: lean-suggest.sh [--apply|--hint|--simp] \"<binders> : <goal>\"" >&2; exit 1; }

tmp="$(mktemp --suffix=.lean)"
trap 'rm -f "$tmp"' EXIT
# `open Nat Finset in` puts the common notations (`n !`, `∑`, `∏`, `Finset.range`, …) in scope so
# goals written in ordinary math notation elaborate instead of parse-erroring.
printf 'import MathProof.Basic\n\nopen Nat Finset in\nexample %s := by\n  %s\n' "$sig" "$tac" > "$tmp"

echo "── lean-suggest ($tac): $sig ──"
out="$(lake env lean "$tmp" 2>&1 || true)"

# exact?/apply?/simp? print "Try this: …"; `hint` prints bullet lines and bracketed tactic tags
# like `[apply] norm_num` — catch all of them (the old filter dropped hint's bracketed output).
sugg="$(printf '%s' "$out" | grep -iE 'Try (this|these)|^[[:space:]]*•|^[[:space:]]*\[[a-z_]+\]|exact |apply |refine |simp only' || true)"
if [[ -n "$sugg" ]]; then
  printf '%s\n' "$sugg"
else
  echo "(no direct suggestion — goal may need a compound tactic; showing Lean output)"
  printf '%s\n' "$out" | grep -vE '^\s*$' | head -12
fi
