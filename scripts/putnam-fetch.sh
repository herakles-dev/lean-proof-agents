#!/usr/bin/env bash
# putnam-fetch.sh — fetch + cache PutnamBench Lean 4 problem STATEMENTS (no-network-at-prove-time).
#
# PutnamBench (trishullab/PutnamBench, Apache-2.0) ships 672 Putnam problems as Lean statements
# with `sorry` bodies. Their toolchain is pinned to an OLDER Lean (v4.27) than ours (v4.33), so a
# statement is only *attemptable* here if it still elaborates against OUR Mathlib — that filter is
# `putnam-harness.sh`. This script just pulls the raw statements into a gitignored local snapshot,
# pinned to a single upstream commit for reproducibility, and records provenance + LICENSE.
#
#   scripts/putnam-fetch.sh list [PATTERN]     # list available problem ids (optionally grep PATTERN)
#   scripts/putnam-fetch.sh get <id> [id...]   # fetch problem(s): putnam_1988_b2 | 1988_b2 | 2023_a1
#   scripts/putnam-fetch.sh year <YYYY>        # fetch every problem for a competition year
#   scripts/putnam-fetch.sh sample [N]         # fetch an even spread of N problems (default 12)
#   scripts/putnam-fetch.sh cached             # list what is already in the local snapshot
#   scripts/putnam-fetch.sh where              # print the cache dir + pinned commit
#
# Problem answers: "find/prove-or-disprove" problems carry the ground truth in the comment right
# after `abbrev *_solution := sorry` (e.g. `-- 18`, `-- True`); pure-statement problems have none.
# Cache: .putnam-cache/ (gitignored) — src/*.lean, LICENSE, PROVENANCE (repo + commit + date).
set -euo pipefail
command -v curl >/dev/null 2>&1 || { echo "putnam-fetch.sh: needs curl" >&2; exit 1; }
command -v python3 >/dev/null 2>&1 || { echo "putnam-fetch.sh: needs python3" >&2; exit 1; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

REPO="trishullab/PutnamBench"
CACHE="$ROOT/.putnam-cache"
SRC="$CACHE/src"
PROV="$CACHE/PROVENANCE"
API="https://api.github.com/repos/$REPO"

case "${1:-}" in
  ""|-h|--help) awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0 ;;
esac
cmd="$1"; shift || true

_curl() { curl -fsSL --retry 2 --retry-delay 1 -m 40 "$@"; }

# Resolve (once) the upstream commit we pin the whole snapshot to, fetch LICENSE, write PROVENANCE.
ensure_snapshot() {
  mkdir -p "$SRC"
  if [[ -f "$PROV" ]]; then SHA="$(awk -F': ' '/^commit:/{print $2}' "$PROV")"; return; fi
  echo "→ pinning $REPO snapshot…" >&2
  SHA="$(_curl "$API/commits/main" | python3 -c 'import json,sys;print(json.load(sys.stdin)["sha"])')"
  [[ -n "$SHA" ]] || { echo "❌ could not resolve upstream commit sha" >&2; exit 1; }
  _curl "https://raw.githubusercontent.com/$REPO/$SHA/lean4/LICENSE" -o "$CACHE/LICENSE" \
    || echo "⚠ LICENSE fetch failed (continuing)" >&2
  { echo "source: https://github.com/$REPO"
    echo "path: lean4/src"
    echo "commit: $SHA"
    echo "fetched: $(date -Iseconds)"
    echo "license: Apache-2.0 (see .putnam-cache/LICENSE)"
    echo "toolchain_upstream: v4.27.0   # ours: $(cat "$ROOT/lean-toolchain")"
  } > "$PROV"
  echo "→ pinned at ${SHA:0:12}" >&2
}

# Cache the recursive git tree (once per snapshot) so `list`/`sample` need no repeated API calls.
tree_ids() {
  local tf="$CACHE/tree.txt"
  if [[ ! -s "$tf" ]]; then
    _curl "$API/git/trees/$SHA?recursive=1" \
      | python3 -c 'import json,sys
for e in json.load(sys.stdin).get("tree",[]):
    p=e["path"]
    if p.startswith("lean4/src/putnam_") and p.endswith(".lean"):
        print(p.split("/")[-1][:-5])' | sort > "$tf"
  fi
  cat "$tf"
}

# putnam_1988_b2 | 1988_b2 | 1988_b2.lean  → putnam_1988_b2
norm_id() { local x="${1%.lean}"; [[ "$x" == putnam_* ]] || x="putnam_$x"; echo "$x"; }

fetch_one() {
  local id; id="$(norm_id "$1")"; local dst="$SRC/$id.lean"
  if [[ -s "$dst" ]]; then echo "  ✓ $id (cached)"; return 0; fi
  if _curl "https://raw.githubusercontent.com/$REPO/$SHA/lean4/src/$id.lean" -o "$dst"; then
    echo "  ↓ $id"
  else
    rm -f "$dst"; echo "  ✗ $id (not found upstream)" >&2; return 1
  fi
}

case "$cmd" in
  where)
    ensure_snapshot; echo "cache:  $CACHE"; echo "commit: $SHA"; echo "cached: $(ls "$SRC" 2>/dev/null | wc -l) statement(s)" ;;
  list)
    ensure_snapshot
    if [[ -n "${1:-}" ]]; then tree_ids | grep -i -- "$1" || { echo "(no ids match '$1')" >&2; exit 1; }
    else tree_ids; fi ;;
  cached)
    ls "$SRC"/*.lean 2>/dev/null | xargs -r -n1 basename | sed 's/\.lean$//' || echo "(cache empty)" ;;
  get)
    [[ $# -ge 1 ]] || { echo "usage: putnam-fetch.sh get <id> [id...]" >&2; exit 1; }
    ensure_snapshot; rc=0; for a in "$@"; do fetch_one "$a" || rc=1; done; exit $rc ;;
  year)
    [[ -n "${1:-}" ]] || { echo "usage: putnam-fetch.sh year <YYYY>" >&2; exit 1; }
    ensure_snapshot
    ids="$(tree_ids | grep -E "^putnam_${1}_" || true)"
    [[ -n "$ids" ]] || { echo "(no problems for year $1)" >&2; exit 1; }
    echo "→ $(echo "$ids" | wc -l) problem(s) for $1"; for id in $ids; do fetch_one "$id"; done ;;
  sample)
    ensure_snapshot; n="${1:-12}"
    ids="$(tree_ids | awk -v n="$n" '{a[NR]=$0} END{if(NR<=n){for(i=1;i<=NR;i++)print a[i];exit} step=NR/n; for(i=0;i<n;i++) print a[int(i*step)+1]}')"
    echo "→ sampling $(echo "$ids" | wc -l) of $(tree_ids | wc -l) problems (even spread)"
    for id in $ids; do fetch_one "$id"; done ;;
  *) echo "unknown command: $cmd (try --help)" >&2; exit 1 ;;
esac
