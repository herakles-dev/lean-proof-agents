#!/usr/bin/env bash
# lean-goals.sh — objective proof-progress metric for the trajectory ledger.
#
#   scripts/lean-goals.sh C0021InverseSquaresBounded          # human summary
#   scripts/lean-goals.sh MathProof/Challenges/C0021....lean  # path form also accepted
#   scripts/lean-goals.sh C0021InverseSquaresBounded --count  # just the integer (for scripting)
#   scripts/lean-goals.sh C0021InverseSquaresBounded --json   # structured
#
# WHY: the ledger's `goal_delta` (change in open goals + sorries) was hand-typed and subjective
# (docs/PROOF_METHODOLOGY.md Part E; every ledger showed only -1/0). This re-elaborates the module
# with `lake env lean` and counts what Lean itself reports:
#     open = (declarations still using `sorry`) + (unsolved-goal turnstiles `⊢`)
# 0 = complete. Measure before and after an attempt; delta = after - before (NEGATIVE = progress).
#
# Objective, offline, no network. Pairs with proof-ledger.sh:
#     b=$(scripts/lean-goals.sh C#### --count)
#     ...prover attempt...
#     a=$(scripts/lean-goals.sh C#### --count)
#     scripts/proof-ledger.sh attempt <id> <sg> --tier T --sketch "…" \
#         --result $([[ $a -lt $b ]] && echo ok || echo fail) --delta $((a-b))
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2
. "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"

mode="human"
args=()
for a in "$@"; do
  case "$a" in
    --count) mode="count" ;;
    --json)  mode="json" ;;
    *)       args+=("$a") ;;
  esac
done
arg="${args[0]:-}"
[[ -z "$arg" ]] && { echo "usage: lean-goals.sh <ChallengeModule | path> [--count|--json]" >&2; exit 2; }

# Normalize any accepted form to a source file path (same rules as check-proof.sh).
name="${arg##*/}"; name="${name%.lean}"; name="${name##*.}"
file="MathProof/Challenges/${name}.lean"
[[ -f "$file" ]] || { echo "not found: $file" >&2; exit 2; }

out="$(lake env lean "$file" 2>&1)"; rc=$?

# `grep -c` counts matching lines; each open goal Lean prints carries exactly one `⊢`, so the
# turnstile count is the open-goal count. `declaration uses 'sorry'` is one line per sorry-bearing
# declaration. A hard type error (not "unsolved goals") is reported separately, not folded into open.
sorries="$(printf '%s\n' "$out" | grep -c "declaration uses .\?sorry")"
goals="$(printf '%s\n' "$out"   | grep -c "⊢")"
errors="$(printf '%s\n' "$out"  | grep -c "error:")"
# "unsolved goals" errors are goal state, not defects — don't double-count them as hard errors.
unsolved_err="$(printf '%s\n' "$out" | grep -c "unsolved goals")"
hard_errors=$(( errors - unsolved_err )); (( hard_errors < 0 )) && hard_errors=0
open=$(( sorries + goals ))
# A hard error truncates elaboration → goals/sorries undercount → a broken file could score LOWER
# than its working sibling and look like "progress", poisoning the ledger's goal_delta. Fold hard
# errors into `open` so a broken file always scores ≥ the working version (never negative delta).
(( hard_errors > 0 )) && open=$(( open + hard_errors ))

case "$mode" in
  count) echo "$open" ;;
  json)  printf '{"module":"%s","open":%d,"sorries":%d,"unsolved_goals":%d,"hard_errors":%d,"complete":%s}\n' \
           "$name" "$open" "$sorries" "$goals" "$hard_errors" "$([[ $open -eq 0 && $hard_errors -eq 0 ]] && echo true || echo false)" ;;
  *)
    if [[ $open -eq 0 && $hard_errors -eq 0 ]]; then
      echo "✅ $name — complete (0 open goals, 0 sorries)"
    else
      echo "⏳ $name — open=$open  (sorries=$sorries, unsolved goals=$goals, hard errors=$hard_errors)"
    fi ;;
esac
exit 0
