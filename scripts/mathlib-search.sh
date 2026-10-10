#!/usr/bin/env bash
# mathlib-search.sh — find Mathlib lemmas / definitions for a proof goal.
#
# Backends (tried in order, all best-effort with graceful fallback):
#   1. Loogle  (loogle.lean-lang.org)  — search by name, subexpression, or TYPE pattern.
#   2. LeanSearch (semantic)           — natural-language search (POST leansearch.net/search);
#                                        override host with $LEANSEARCH_URL. Needs jq.
#   3. Local grep over .lake/packages/mathlib — offline, ALWAYS available, never network-bound.
#
# Usage (flags may appear in ANY position):
#   scripts/mathlib-search.sh "Nat.Prime"                    # name / identifier
#   scripts/mathlib-search.sh "Finset.sum_range_succ"        # exact lemma (dotted ok)
#   scripts/mathlib-search.sh --type "_ * _ = _ * _"         # loogle type/shape search (holes = _)
#   scripts/mathlib-search.sh "sum_range" --local            # force offline grep (order-free)
#   scripts/mathlib-search.sh --check Finset.sum_range_succ  # authoritative existence/type (#check @Name)
#   scripts/mathlib-search.sh --nl "sum of a row of Pascal's triangle"   # semantic
#
# In-editor, prefer Lean's own tools (exact?, apply?, rw?, simp?, loogle) — this
# script is for the CLI loop and for agents without an editor.
#
# NOTE: network backends (loogle, LeanSearch) are best-effort — the local grep backend is
# the reliable one and always runs as a fallback. LeanSearch (POST leansearch.net/search) and
# loogle are confirmed reachable from this host; OEIS was not (403). arXiv works over HTTPS.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MATHLIB="$ROOT/.lake/packages/mathlib/Mathlib"

FORCE_LOCAL=false
TYPE_SEARCH=false
NL_SEARCH=false
CHECK=false
args=()
for a in "$@"; do
  case "$a" in
    --local) FORCE_LOCAL=true ;;
    --type)  TYPE_SEARCH=true ;;
    --nl)    NL_SEARCH=true ;;
    --check) CHECK=true ;;
    -h|--help)
      awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0 ;;
    *) args+=("$a") ;;
  esac
done
q="${args[*]:-}"
[[ -z "$q" ]] && { echo "usage: mathlib-search.sh [--local|--type|--nl] <query>" >&2; exit 1; }

# Local grep: match a declaration whose NAME contains the query. Handles dotted queries
# (ZMod.pow_card) by also trying the last path component (pow_card), since the declaration
# is written unqualified inside `namespace ZMod`.
local_grep() {
  [[ -d "$MATHLIB" ]] || { echo "(local Mathlib not found at $MATHLIB — run 'lake exe cache get')" >&2; return 1; }
  local needle="$1" bare="${1##*.}" hits twin thits found=1
  local kw='^(private |protected |noncomputable )*(theorem|lemma|def|instance|abbrev|structure|class)'
  # 1) declaration line whose name contains the (possibly bare) needle
  hits="$(grep -rInE "${kw} +[A-Za-z0-9_'.]*(${needle}|${bare})" "$MATHLIB" 2>/dev/null \
          | sed -E 's/:([0-9]+):/ → L\1  /' | sed "s#${MATHLIB}/##" | head -40)"
  if [[ -z "$hits" ]]; then
    # 2) looser: any declaration mentioning the bare identifier anywhere on its signature line
    hits="$(grep -rInE "${kw} .*${bare}" "$MATHLIB" 2>/dev/null \
            | sed -E 's/:([0-9]+):/ → L\1  /' | sed "s#${MATHLIB}/##" | head -40)"
  fi
  [[ -n "$hits" ]] && { printf '%s\n' "$hits"; found=0; }
  # to_additive twin: additive lemmas (sum_*, add_*, zero_*, …) are auto-generated from a
  # multiplicative source, so the additive NAME never appears as a declaration line. Grep the
  # multiplicative twin so an offline search for e.g. `sum_range_succ` still surfaces the lemma.
  twin="$(printf '%s' "$bare" | sed -E 's/nsmul/pow/g; s/sum/prod/g; s/add/mul/g; s/zero/one/g; s/neg/inv/g; s/sub/div/g')"
  if [[ "$twin" != "$bare" ]]; then
    thits="$(grep -rInE "${kw} +[A-Za-z0-9_'.]*${twin}" "$MATHLIB" 2>/dev/null \
             | sed -E 's/:([0-9]+):/ → L\1  /' | sed "s#${MATHLIB}/##" | head -20)"
    [[ -n "$thits" ]] && { echo "  ── to_additive twin: '$bare' is generated from '$twin' ──"; printf '%s\n' "$thits"; found=0; }
  fi
  return $found
}

# check_name — authoritative existence + signature via Lean's own `#check @Name`.
check_name() {
  ( cd "$ROOT"; . "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"
    local tmp out; tmp="$(mktemp --suffix=.lean)"
    printf 'import MathProof.Basic\n#check @%s\n' "$q" > "$tmp"
    out="$(lake env lean "$tmp" 2>&1 || true)"; rm -f "$tmp"
    if printf '%s' "$out" | grep -qiE 'unknown (identifier|constant)|error'; then
      echo "  ✗ no such declaration: $q"; printf '%s\n' "$out" | grep -iE 'unknown|error' | head -3; return 1
    fi
    printf '%s\n' "$out" )
}

loogle_search() {
  local out qq="$q"
  # loogle name search is happier without a leading namespace for some queries; send as-is.
  out="$(curl -fsS --max-time 12 -G "https://loogle.lean-lang.org/json" --data-urlencode "q=$qq" 2>/dev/null)" || return 1
  [[ -z "$out" ]] && return 1
  if command -v jq >/dev/null 2>&1; then
    # Surface loogle's own error (bad query syntax) instead of silently claiming "unavailable".
    local err; err="$(printf '%s' "$out" | jq -r '.error // empty' 2>/dev/null)"
    if [[ -n "$err" ]]; then echo "  (loogle: $err)" >&2; return 1; fi
    local n; n="$(printf '%s' "$out" | jq -r '.hits // [] | length' 2>/dev/null || echo 0)"
    [[ "$n" == "0" || -z "$n" ]] && return 1
    printf '%s' "$out" | jq -r '.hits[] | "• \(.name)\n    : \(.type)   [\(.module)]"' 2>/dev/null | head -80
  else
    printf '%s' "$out"
  fi
}

# Semantic (natural-language) search via LeanSearch. Confirmed reachable:
# POST https://leansearch.net/search  body {"query":["<nl>"],"num_results":N}
# → nested JSON [[{"result":{name:[...], signature, type, module_name:[...]}}]].
# Override the endpoint with $LEANSEARCH_URL if it moves. Needs jq.
leansearch_search() {
  command -v jq >/dev/null 2>&1 || return 1
  local url="${LEANSEARCH_URL:-https://leansearch.net/search}" out payload
  payload="$(jq -nc --arg q "$q" '{query:[$q],num_results:8}')" || return 1
  out="$(curl -fsS --max-time 15 -X POST "$url" -H 'Content-Type: application/json' -d "$payload" 2>/dev/null)" || return 1
  [[ -z "$out" ]] && return 1
  local parsed
  parsed="$(printf '%s' "$out" | jq -r '
    [.. | objects | select(has("result")) | .result]
    | .[]? | "• \((.name // []) | join(".")) : \(.signature // .type // "")   [\((.module_name // []) | join("."))]"' 2>/dev/null | head -80)"
  [[ -z "$parsed" ]] && return 1
  printf '%s\n' "$parsed"
}

echo "── mathlib-search: \"$q\" ──"

if $CHECK; then check_name; exit $?; fi

if $FORCE_LOCAL; then
  local_grep "$q" || echo "no local matches"
  exit 0
fi

if $NL_SEARCH; then
  if leansearch_search; then exit 0; fi
  echo "(semantic backend unavailable — network/endpoint issue; falling back to local grep)"
  local_grep "$q" || echo "no matches"
  exit 0
fi

# Default: loogle (type or name) → semantic (if configured) → local grep.
if $TYPE_SEARCH; then
  loogle_search && exit 0
  echo "(loogle unavailable for type search — no offline type-pattern search; try a name with --local)"
  exit 0
fi

if loogle_search; then
  exit 0
fi
leansearch_search && exit 0
echo "(loogle/semantic unavailable or no hits — falling back to local grep)"
local_grep "$q" || echo "no matches"
