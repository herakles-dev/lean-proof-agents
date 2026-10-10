#!/usr/bin/env bash
# erdos-fetch.sh — fetch + cache the Erdős problems corpus (statuses, prizes, tags) as our target feed.
#
# Erdős Problems (teorth/erdosproblems, Apache-2.0) ships `data/problems.yaml` — 1217 problems, each with
# an `informal_status.state` (open / solved / disproved / falsifiable / decidable / verifiable / …),
# a `prize` ("$500", "£25", or "no"), `oeis`, `tags`, and update dates. The finite-computation bucket
# we can actually attempt is **cat-(a)**: `informal_status.state ∈ {falsifiable, decidable, verifiable}`
# — 41 problems (all unformalized), 33 with a Lean statement in google-deepmind/formal-conjectures,
# 7 carrying money. This script pins ONE upstream commit of that yaml into a gitignored snapshot and
# parses it with python3 stdlib only (no pyyaml). erdosproblems.com 403s from this host — the yaml is
# the data source.
#
#   scripts/erdos-fetch.sh where              # cache dir + pinned commit + corpus size
#   scripts/erdos-fetch.sh cached             # what is already in the local snapshot
#   scripts/erdos-fetch.sh list [PATTERN]     # one line per problem (id/state/prize/tags); PATTERN filters
#   scripts/erdos-fetch.sh get <N> [N...]     # print the yaml block for problem N + its formal-conjectures .lean
#   scripts/erdos-fetch.sh cat-a              # THE target board: the 41 finite-computation targets, prize desc
#
# Cache: .erdos-cache/ (gitignored) — src/problems.yaml (pinned), LICENSE, PROVENANCE (repo+commit+date+license),
# fc-files.txt (best-effort index of formal-conjectures ErdosProblems ids, from `main` — NOT pinned).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

REPO="teorth/erdosproblems"
YAML_PATH="data/problems.yaml"
CACHE="$ROOT/.erdos-cache"
SRC="$CACHE/src"
YAML="$SRC/problems.yaml"
PROV="$CACHE/PROVENANCE"
FCIDX="$CACHE/fc-files.txt"
API="https://api.github.com/repos/$REPO"
FC_REPO="google-deepmind/formal-conjectures"
FC_DIR="FormalConjectures/ErdosProblems"
FC_RAW="https://raw.githubusercontent.com/$FC_REPO/main/$FC_DIR"

case "${1:-}" in
  ""|-h|--help) awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0 ;;
esac
cmd="$1"; shift || true

_curl() { curl -fsSL --retry 2 --retry-delay 1 -m 40 "$@"; }

# Resolve (once) the upstream commit we pin the snapshot to, fetch the yaml + LICENSE, write PROVENANCE.
ensure_snapshot() {
  mkdir -p "$SRC"
  if [[ -f "$PROV" && -s "$YAML" ]]; then SHA="$(awk -F': ' '/^commit:/{print $2}' "$PROV")"; return; fi
  echo "→ pinning $REPO snapshot…" >&2
  SHA="$(_curl "$API/commits/main" | python3 -c 'import json,sys;print(json.load(sys.stdin)["sha"])')"
  [[ -n "$SHA" ]] || { echo "❌ could not resolve upstream commit sha" >&2; exit 1; }
  _curl "https://raw.githubusercontent.com/$REPO/$SHA/$YAML_PATH" -o "$YAML" \
    || { echo "❌ could not fetch $YAML_PATH@$SHA" >&2; exit 1; }
  _curl "https://raw.githubusercontent.com/$REPO/$SHA/LICENSE" -o "$CACHE/LICENSE" \
    || echo "⚠ LICENSE fetch failed (continuing)" >&2
  { echo "source: https://github.com/$REPO"
    echo "path: $YAML_PATH"
    echo "commit: $SHA"
    echo "fetched: $(date -Iseconds)"
    echo "license: Apache-2.0 (see .erdos-cache/LICENSE)"
    echo "formal_conjectures: https://github.com/$FC_REPO ($FC_DIR, main — moving, best-effort)"
  } > "$PROV"
  echo "→ pinned at ${SHA:0:12}" >&2
}

# Best-effort index of which Erdős numbers have a formal-conjectures Lean statement (from main, moving).
# Never fatal: if it fails, cat-a/list just show '?' in the FC column.
ensure_fc_index() {
  [[ -s "$FCIDX" ]] && return 0
  _curl "https://api.github.com/repos/$FC_REPO/contents/$FC_DIR?ref=main" 2>/dev/null \
    | python3 -c 'import json,sys
try: d=json.load(sys.stdin)
except Exception: sys.exit(1)
if not isinstance(d,list): sys.exit(1)
print("\n".join(sorted((e["name"][:-5] for e in d if e.get("name","").endswith(".lean")),
                        key=lambda x:int(x) if x.isdigit() else 0)))' > "$FCIDX" 2>/dev/null \
    || { rm -f "$FCIDX"; echo "⚠ formal-conjectures index unavailable (FC column = ?)" >&2; }
}

# Single python engine over the pinned yaml + FC index. argv: <yaml> <fc-index> <mode> [args...]
_engine() {
  python3 - "$YAML" "$FCIDX" "$@" <<'PY'
import sys, re
from collections import defaultdict

YAML, FCI, MODE = sys.argv[1], sys.argv[2], (sys.argv[3] if len(sys.argv) > 3 else "")
ARGS = sys.argv[4:]
CAT = {"falsifiable", "decidable", "verifiable"}

def load():
    recs=[]; cur=None; section=None
    with open(YAML, encoding="utf-8") as fh:
        for raw in fh:
            line=raw.rstrip("\n")
            m=re.match(r'^- number:\s*"?([^"]+)"?\s*$', line)
            if m:
                cur={"number":m.group(1), "_raw":[line]}; recs.append(cur); section=None; continue
            if cur is None: continue
            cur["_raw"].append(line)
            m2=re.match(r'^  (\w+):\s*(.*)$', line)   # 2-space field
            if m2:
                section=m2.group(1); val=m2.group(2).strip()
                if val: cur[section]=val
                continue
            m3=re.match(r'^    (\w+):\s*(.*)$', line)  # 4-space subfield
            if m3 and section:
                cur["%s.%s" % (section, m3.group(1))]=m3.group(2).strip()
    return recs

def unq(s): return (s or "").strip().strip('"')
def state(r): return unq(r.get("informal_status.state",""))
def prize(r): return unq(r.get("prize",""))
def has_money(r): return bool(re.match(r'^[$£€]', prize(r)))
def amount(r):
    m=re.search(r'(\d[\d,]*)', prize(r)); return int(m.group(1).replace(",","")) if m else -1
def prize_disp(r): return prize(r) if has_money(r) else "—"
def taglist(r):
    raw=r.get("tags","")
    return [t.strip().strip('"') for t in raw.strip().lstrip("[").rstrip("]").split(",") if t.strip()]
def tags_disp(r): return ", ".join(taglist(r))

try:
    FC=set(open(FCI).read().split()); FC_OK=True
except OSError:
    FC=set(); FC_OK=False
def fc_mark(r):
    if not FC_OK: return "?"
    return "✓" if r["number"] in FC else "·"

recs=load()

if MODE=="counts":
    cat=[r for r in recs if state(r) in CAT]
    print("%d\t%d" % (len(recs), len(cat)))

elif MODE=="list":
    pat=ARGS[0].lower() if ARGS else None
    for r in sorted(recs, key=lambda r:int(r["number"]) if r["number"].isdigit() else 1<<30):
        line="#%-5s %-11s %-7s %s" % (r["number"], state(r) or "-", prize_disp(r), tags_disp(r))
        if pat and pat not in line.lower(): continue
        print(line)

elif MODE=="getblock":
    n=ARGS[0]
    for r in recs:
        if r["number"]==n:
            block=r["_raw"][:]
            while block and not block[-1].strip(): block.pop()   # trim trailing blank(s)
            print("\n".join(block)); sys.exit(0)
    sys.stderr.write("  ✗ problem %s not found in corpus\n" % n); sys.exit(1)

elif MODE=="cat-a":
    cat=[r for r in recs if state(r) in CAT]
    cat.sort(key=lambda r:(0 if has_money(r) else 1, -amount(r),
                           int(r["number"]) if r["number"].isdigit() else 1<<30))
    by=defaultdict(int); sums=defaultdict(int); nmoney=0; nfc=0
    for r in cat:
        by[state(r)]+=1
        if has_money(r): sums[prize(r)[0]]+=amount(r); nmoney+=1
        if FC_OK and r["number"] in FC: nfc+=1
    print("%-6s %-11s %-7s %-3s %s" % ("ID","STATE","PRIZE","FC","TAGS"))
    print("%-6s %-11s %-7s %-3s %s" % ("-"*5,"-"*11,"-"*6,"-"*2,"-"*30))
    for r in cat:
        print("#%-5s %-11s %-7s %-3s %s" % (r["number"], state(r), prize_disp(r),
                                            fc_mark(r), tags_disp(r)))
    money=" + ".join("%s%s" % (c, format(v, ",")) for c,v in sorted(sums.items()))
    order=" · ".join("%d %s" % (by[s], s) for s in ("falsifiable","decidable","verifiable") if by.get(s))
    print()
    print("%d cat-(a) targets (unformalized, finite-computation): %s" % (len(cat), order))
    fcline=("%d have a formal-conjectures Lean statement" % nfc) if FC_OK else "formal-conjectures index unavailable (FC=?)"
    print("%d carry money = %s   |   %s" % (nmoney, money or "—", fcline))
    print("state key: falsifiable=find a counterexample · decidable=finite case-check · verifiable=exhibit+check a witness")
else:
    sys.stderr.write("engine: unknown mode %r\n" % MODE); sys.exit(2)
PY
}

case "$cmd" in
  where)
    ensure_snapshot
    read -r TOTAL CATA < <(_engine counts)
    echo "cache:  $CACHE"
    echo "commit: $SHA"
    echo "source: $REPO  $YAML_PATH"
    echo "corpus: $TOTAL problems  ($CATA cat-a: falsifiable/decidable/verifiable)"
    ;;
  cached)
    if [[ -s "$YAML" ]]; then
      echo "problems.yaml: present ($(wc -c < "$YAML") bytes)"
      [[ -f "$PROV" ]] && awk -F': ' '/^commit:/{print "commit: "$2} /^fetched:/{print "fetched: "$2}' "$PROV"
      [[ -s "$FCIDX" ]] && echo "fc-index: $(wc -l < "$FCIDX") formal-conjectures files" || echo "fc-index: (not built — run cat-a)"
    else
      echo "(cache empty — run any command to pin the snapshot)"
    fi
    ;;
  list)
    ensure_snapshot; ensure_fc_index
    _engine list "${1:-}"
    ;;
  get)
    [[ $# -ge 1 ]] || { echo "usage: erdos-fetch.sh get <N> [N...]" >&2; exit 1; }
    ensure_snapshot
    tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
    rc=0
    for n in "$@"; do
      echo "════════ Erdős problem #$n ════════"
      _engine getblock "$n" || { rc=1; continue; }
      echo "──── formal-conjectures (best-effort, $FC_REPO@main) ────"
      if _curl "$FC_RAW/$n.lean" -o "$tmp" 2>/dev/null; then
        cat "$tmp"
      else
        echo "(no $FC_DIR/$n.lean — 404 or unreachable)"
      fi
      echo
    done
    exit $rc
    ;;
  cat-a)
    ensure_snapshot; ensure_fc_index
    _engine cat-a
    ;;
  *) echo "unknown command: $cmd (try --help)" >&2; exit 1 ;;
esac
