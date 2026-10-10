#!/usr/bin/env bash
# lean-eval.sh — offline numeric oracle: run Lean's own `#eval` / `decide` on a concrete case.
#
# The reliable exploration backend (works offline, unlike OEIS lookups; this uses no network and,
# crucially, the SAME Lean kernel that will judge the eventual proof). Use it to spot-check a
# conjecture at concrete inputs before formalizing, and for proof-auditor anti-vacuity checks.
#
#   scripts/lean-eval.sh "(List.range 6).map Nat.fib"                 # → [0, 1, 1, 2, 3, 5]
#   scripts/lean-eval.sh "∑ i ∈ Finset.range 5, i^2"                  # → 30
#   scripts/lean-eval.sh --decide "∀ n ∈ Finset.range 20, Nat.fib n < 2 ^ n"   # → true | false
#   scripts/lean-eval.sh --decide --open ArithmeticFunction.sigma \
#       "∀ m ∈ Finset.range 24, m + σ 0 m ≤ 26"                                 # → true
#
# `--decide "<prop>"` elaborates the Prop as an abbrev, THEN evaluates `decide` on it; the Prop
# must be Decidable (bounded ∀/∃ over Finset/Fin, concrete numerals, etc.). No network. Not a proof.
# ⚠ TRUSTED INPUT ONLY: the arguments are interpolated into Lean source and EXECUTED (`#eval` can run
# arbitrary IO, incl. shell commands). Never pass text from an untrusted source (web pages, issues, models).
# Requires: bash, mktemp, and the repo's Lean toolchain (elan/lake).
# `--open "<ns…>"` appends namespaces to the default `open Nat Finset` line (e.g. for the `σ` notation).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
. "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"

MODE=eval
OPENS="Nat Finset"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --decide) MODE=decide; shift ;;
    --open) OPENS="$OPENS ${2:-}"; shift 2 ;;
    -h|--help) awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0 ;;
    *) break ;;
  esac
done
expr="${*:-}"
[[ -z "$expr" ]] && { awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0; }

tmp="$(mktemp --suffix=.lean)"
trap 'rm -f "$tmp"' EXIT
if [[ "$MODE" == decide ]]; then
  # Elaborate the proposition as an abbrev FIRST so `Decidable` instance synthesis sees through it
  # with numerals already defaulted to ℕ. Emitting `#eval decide (<prop>)` as a bare term gets
  # stuck on pending numeral metavariables for bounded ∀/∃ over Ico/range with literals.
  printf 'import MathProof.Basic\nopen %s in\nabbrev LeanEvalProp : Prop := %s\n#eval decide LeanEvalProp\n' "$OPENS" "$expr" > "$tmp"
else
  printf 'import MathProof.Basic\nopen %s in\n#eval %s\n' "$OPENS" "$expr" > "$tmp"
fi

out="$(lake env lean "$tmp" 2>&1)" || { echo "❌ lean-eval failed:"; echo "$out"; exit 1; }
# `#eval` output is the (only) non-empty line(s) Lean prints; show them verbatim.
if [[ -z "$out" ]]; then
  echo "(no output — is the expression a term with a printable value / a Decidable Prop?)" >&2
  exit 1
fi
echo "$out"
