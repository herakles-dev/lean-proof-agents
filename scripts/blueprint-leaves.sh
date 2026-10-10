#!/usr/bin/env bash
# blueprint-leaves.sh — list PROOF-READY leaf lemmas from a Lean blueprint dependency graph.
#
# A blueprint's dep_graph page embeds a Graphviz DOT graph. Node fill color encodes state;
# `#A3D6FF` marks "statement in Lean, all prerequisites proved — ready to prove now" (an
# `ellipse` is a lemma/theorem, a `box` a definition). Those blue ellipses are the recognition-
# win targets: claim one on Lean Zulip, formalize the proof → contributor credit.
# Feeds the `blueprint-scout` agent.
#
#   scripts/blueprint-leaves.sh                       # default: Prime Number Theorem And More
#   scripts/blueprint-leaves.sh <dep_graph_url>       # any project's dep_graph_document.html
#   scripts/blueprint-leaves.sh --file page.html      # parse an already-downloaded page
#   scripts/blueprint-leaves.sh --colors <url>        # show the fillcolor histogram (legend recon)
#   READY_COLOR=#RRGGBB scripts/blueprint-leaves.sh … # override the "proof-ready" color
#
# Network best-effort (curl). If a project uses different color semantics, run --colors first.
set -euo pipefail

DEFAULT_URL="https://AlexKontorovich.github.io/PrimeNumberTheoremAnd/blueprint/dep_graph_document.html"
READY_COLOR="${READY_COLOR:-#A3D6FF}"
MODE=leaves
SRC=""
FILE=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --colors) MODE=colors ;;
    --file)   FILE="${2:-}"; shift ;;
    -h|--help) sed -n '2,19p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) SRC="$1" ;;
  esac
  shift
done

tmp=""
if [[ -n "$FILE" ]]; then
  html_path="$FILE"
  [[ -f "$html_path" ]] || { echo "no such file: $html_path" >&2; exit 1; }
else
  url="${SRC:-$DEFAULT_URL}"
  tmp="$(mktemp --suffix=.html)"; trap 'rm -f "$tmp"' EXIT
  if ! curl -fsS --max-time 30 -o "$tmp" "$url" 2>/dev/null; then
    echo "❌ could not fetch $url (network may be blocked from this host; try --file)" >&2
    exit 1
  fi
  html_path="$tmp"
fi

MODE="$MODE" READY_COLOR="$READY_COLOR" python3 - "$html_path" <<'PY'
import os, re, sys
html = open(sys.argv[1], encoding='utf-8', errors='replace').read()
mode = os.environ.get("MODE", "leaves")
ready = os.environ.get("READY_COLOR", "#A3D6FF").lower()

# Node defs look like:  "node-id"  [color=green, fillcolor="#A3D6FF", label="...", shape=ellipse, style=filled];
node_re = re.compile(r'"([^"]+)"\s*\[([^\]]*)\]', re.S)
nodes = []
for m in node_re.finditer(html):
    nid, attrs = m.group(1), m.group(2)
    fc = re.search(r'fillcolor\s*=\s*"?(#[0-9A-Fa-f]{6})"?', attrs)
    sh = re.search(r'shape\s*=\s*"?([A-Za-z]+)"?', attrs)
    if fc:
        nodes.append((nid, fc.group(1).lower(), sh.group(1).lower() if sh else "?"))

if not nodes:
    print("(no DOT nodes with fillcolor found — is this a blueprint dep_graph page?)")
    sys.exit(0)

if mode == "colors":
    from collections import Counter
    c = Counter(fc for _, fc, _ in nodes)
    print(f"fillcolor histogram ({len(nodes)} nodes):")
    for color, n in c.most_common():
        tag = "  ← READY_COLOR (proof-ready)" if color == ready else ""
        print(f"  {color}  ×{n}{tag}")
    sys.exit(0)

lemmas = [(nid, sh) for nid, fc, sh in nodes if fc == ready and sh == "ellipse"]
defs   = [(nid, sh) for nid, fc, sh in nodes if fc == ready and sh != "ellipse"]
print(f"proof-ready nodes ({ready}): {len(lemmas)} lemmas + {len(defs)} defs, of {len(nodes)} total")
print("── proof-ready LEAF LEMMAS (claim one → formalize → recognition credit) ──")
for nid, _ in sorted(lemmas):
    print(f"  • {nid}")
if defs:
    print(f"── proof-ready definitions ({len(defs)}) ──")
    for nid, _ in sorted(defs)[:15]:
        print(f"  · {nid}")
    if len(defs) > 15:
        print(f"  … +{len(defs)-15} more")
PY