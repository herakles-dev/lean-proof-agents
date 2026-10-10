#!/usr/bin/env bash
# wolfram.sh — Wolfram Alpha LLM API oracle for EXPLORATION ONLY.
#
#   scripts/wolfram.sh "simplify sin(x)^2 + cos(x)^2"      -> 1
#   scripts/wolfram.sh "is sqrt(2) rational"
#   scripts/wolfram.sh "rotate point (0,100) by 30 degrees clockwise around origin"
#
# ⚠️  This is a SCRATCHPAD, not a proof. A challenge is only SOLVED when its Lean
#     module compiles with no `sorry` (see scripts/check-proof.sh). Wolfram tells
#     you WHAT to try to prove; Lean's kernel decides whether it IS proved.
#
# Uses WOLFRAM_LLM_APP_ID (falls back to WOLFRAM_APP_ID) from the environment or a local .env file (see .env.example).
# The app id is passed to curl on stdin (a config), not on its command line; the QUERY text is
# sent to Wolfram Alpha. Requires: bash, curl (and network access).
#
# ── The one hard rule: ATOMIC COMPUTATIONAL QUERIES ONLY ──────────────────────
# The engine rejects definition-laden prose ("verify that if X has property Y…").
# Break every claim into single-purpose queries:
#   • concrete numeric case : "rotate point (0,100) by 30 degrees clockwise around origin"
#   • symbolic identity     : "simplify (cos(t)sin(b))^2 + (cos(t)cos(b))^2 + sin(t)^2"  -> 1
#   • edge-case value       : "log base 2 of (1000/500) and log base 2 of (1000/2000)"   -> {1,-1}
# Avoid underscore variable names (h_old parses as h indexed by old); use a,b,x or numbers.
set -euo pipefail

case "${1:-}" in
  ""|-h|--help)
    sed -n '2,25p' "$0" | sed 's/^# \{0,1\}//'
    exit 0
    ;;
esac

ENVFILE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/.env"
APPID="${WOLFRAM_LLM_APP_ID:-}"
[[ -z "$APPID" ]] && APPID="${WOLFRAM_APP_ID:-}"
if [[ -z "$APPID" && -f "$ENVFILE" ]]; then
  APPID="$(grep -E '^(export )?WOLFRAM_LLM_APP_ID=' "$ENVFILE" | head -1 | sed -E 's/^(export )?WOLFRAM_LLM_APP_ID=//; s/^"//; s/"$//' || true)"
  [[ -z "$APPID" ]] && APPID="$(grep -E '^(export )?WOLFRAM_APP_ID=' "$ENVFILE" | head -1 | sed -E 's/^(export )?WOLFRAM_APP_ID=//; s/^"//; s/"$//' || true)"
fi
if [[ -z "$APPID" ]]; then
  echo "error: no WOLFRAM_LLM_APP_ID / WOLFRAM_APP_ID found (checked env + .env)" >&2
  exit 3
fi

query="$*"
# appid goes in via a curl config on stdin (printf is a builtin → never in argv/ps).
aid="${APPID//\\/\\\\}"; aid="${aid//\"/\\\"}"
resp="$(printf 'data-urlencode = "appid=%s"\n' "$aid" | curl -sS -G -K - "https://www.wolframalpha.com/api/v1/llm-api" \
  --data-urlencode "input=${query}" \
  -w $'\n[HTTP %{http_code}]' 2>&1)" || {
    echo "error: request failed" >&2; echo "$resp" >&2; exit 4;
  }

echo "$resp"

if echo "$resp" | grep -qi "could not understand"; then
  echo >&2
  echo "hint: rejected as too narrative — retry with an ATOMIC query (concrete numbers or 'simplify …'). See --help." >&2
  exit 5
fi
