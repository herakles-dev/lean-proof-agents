#!/usr/bin/env bash
# lit-search.sh — the mandatory literature pre-pass: "has this been solved already?"
#
# Fans one query out to free scholarly DATA sources and returns ranked hits, so we never
# invest a Lean proof in a problem the literature quietly closed years ago (the #593/#707
# lesson: the erdosproblems DB lags the papers). This is a SCRATCHPAD gate, NOT a proof and
# NOT a verdict — a human/lit-scout reads the hits and decides. Lean's kernel is the only
# arbiter of a proof; this only tells us whether to bother.
#
#   scripts/lit-search.sh "<query>" [--erdos N] [--since YYYY] [--json]
#
#   --erdos N    also print Erdős problem N's row (state / last_update / prize / oeis) from
#                .erdos-cache/ if present, else fetched from teorth/erdosproblems problems.yaml
#   --since YYYY drop hits older than YYYY (records with no year are kept)
#   --json       emit a JSON array of {source,title,year,url,snippet} on stdout (erdos row + a
#                per-backend reachability line always go to stderr, so stdout stays clean)
#
# Backends (each best-effort: timeout + fail-open, one dead backend never kills the run):
#   arXiv · OpenAlex · zbMATH Open   (the MVP trio, verified live)   → api.zbmath.org/v1/document
#   Crossref · DBLP · StackExchange(MathOverflow)                    (wired, degrade gracefully)
#
# Discipline (the false-negative trap): papers rarely cite the problem NUMBER, so query by
# CONTENT in 2–3 phrasings AND by number, require ≥2 backends to corroborate, and phrase any
# conclusion as "no contradiction found as of <date>" — never a bare "open".
#
# Raw responses cache to gitignored .lit-cache/ (keyed by source+query hash, TTL LIT_CACHE_TTL,
# default 24h). python3 stdlib + curl only; no network at prove-time, no solver installs.
# Env knobs: LIT_CACHE_TTL (cache TTL secs, default 86400) · LIT_TIMEOUT (per-fetch secs, default 25)
#            · LIT_MAX (max hits kept, default 12).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CACHE="$ROOT/.lit-cache"
ERDOS_CACHE="$ROOT/.erdos-cache"          # owned by sibling erdos-fetch.sh; read-only here
TTL="${LIT_CACHE_TTL:-86400}"
TIMEOUT="${LIT_TIMEOUT:-25}"
MAX="${LIT_MAX:-12}"
UA="lean-proof-agents-lit-search/1.0 (research pre-pass)"
YAML_URL="https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml"

case "${1:-}" in
  ""|-h|--help) awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0 ;;
esac

QUERY=""; ERDOS=""; SINCE=""; JSON=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0 ;;
    --erdos)   ERDOS="${2:?--erdos needs a problem number}"; shift 2 ;;
    --since)   SINCE="${2:?--since needs a year}"; shift 2 ;;
    --json)    JSON=1; shift ;;
    --)        shift; while [[ $# -gt 0 ]]; do QUERY="${QUERY:+$QUERY }$1"; shift; done ;;
    --*)       echo "unknown flag: $1 (try --help)" >&2; exit 1 ;;
    *)         QUERY="${QUERY:+$QUERY }$1"; shift ;;
  esac
done

mkdir -p "$CACHE"
RECORDS="$(mktemp)"; trap 'rm -f "$RECORDS" "$RECORDS".*' EXIT

_curl() { curl -fsSL --compressed -A "$UA" --retry 2 --retry-delay 1 -m "$TIMEOUT" "$@"; }
urlenc() { python3 -c 'import sys,urllib.parse as u;print(u.quote(sys.argv[1]))' "$1"; }

# ── one raw HTTP fetch, cached by source+query hash ─────────────────────────────────────────
FETCH_FILE=""; FETCH_CACHED=0
fetch() {  # fetch <source> <url> <ext> → 0 ok (FETCH_FILE set) / 1 unreachable
  local src="$1" url="$2" ext="$3" key f age
  key="$(printf '%s|%s|%s' "$src" "$QUERY" "$SINCE" | sha1sum | cut -c1-12)"
  f="$CACHE/${src}-${key}.${ext}"; FETCH_FILE="$f"; FETCH_CACHED=0
  if [[ -f "$f" ]]; then
    age=$(( $(date +%s) - $(stat -c %Y "$f") ))
    [[ "$age" -lt "$TTL" ]] && { FETCH_CACHED=1; return 0; }
  fi
  if _curl "$url" -o "$f.tmp" 2>/dev/null; then mv "$f.tmp" "$f"; return 0
  else rm -f "$f.tmp"; return 1; fi
}

# ── parse one cached raw response → normalized {source,title,year,url,snippet} JSONL ─────────
parse() {  # parse <source> <file>
  python3 - "$1" "$2" <<'PY'
import sys, json, html, re
from datetime import datetime, timezone
src, path = sys.argv[1], sys.argv[2]
raw = open(path, "rb").read()

def clean(s, n=240):
    if not s: return ""
    s = re.sub(r"<[^>]+>", " ", str(s))
    s = html.unescape(s)
    return re.sub(r"\s+", " ", s).strip()[:n]

def emit(source, title, year, url, snippet):
    title = clean(title, 300)
    if not title: return
    print(json.dumps({"source": source, "title": title,
                      "year": (str(year) if year else ""),
                      "url": (url or ""), "snippet": clean(snippet, 240)},
                     ensure_ascii=False))
try:
    if src == "arxiv":
        import xml.etree.ElementTree as ET
        ns = "{http://www.w3.org/2005/Atom}"
        for e in ET.fromstring(raw).findall(ns + "entry"):
            pub = e.findtext(ns + "published") or ""
            emit("arxiv", e.findtext(ns + "title") or "",
                 pub[:4] if pub[:4].isdigit() else "",
                 (e.findtext(ns + "id") or "").strip(), e.findtext(ns + "summary") or "")
    elif src == "openalex":
        for r in (json.loads(raw).get("results") or []):
            inv = r.get("abstract_inverted_index"); snip = ""
            if inv:
                pos = {}
                for w, idxs in inv.items():
                    for i in idxs: pos[i] = w
                snip = " ".join(pos[i] for i in sorted(pos))
            emit("openalex", r.get("display_name") or r.get("title") or "",
                 r.get("publication_year") or "", r.get("doi") or r.get("id") or "", snip)
    elif src == "zbmath":
        for r in (json.loads(raw).get("result") or []):
            url = r.get("zbmath_url") or ""
            if not url:
                lk = r.get("links") or []
                if lk: url = lk[0].get("url", "")
            auth = ", ".join(a.get("name", "") for a in
                             ((r.get("contributors") or {}).get("authors") or []))
            emit("zbmath", (r.get("title") or {}).get("title") or "",
                 r.get("year") or "", url, auth)
    elif src == "crossref":
        for it in (json.loads(raw).get("message", {}).get("items") or []):
            tl = it.get("title") or []; dp = it.get("issued", {}).get("date-parts") or [[None]]
            emit("crossref", tl[0] if tl else "",
                 dp[0][0] if dp and dp[0] else "", it.get("URL") or "", it.get("abstract", ""))
    elif src == "dblp":
        hits = json.loads(raw).get("result", {}).get("hits", {}).get("hit", [])
        if isinstance(hits, dict): hits = [hits]
        for h in hits:
            info = h.get("info", {})
            emit("dblp", info.get("title") or "", info.get("year") or "",
                 info.get("ee") or info.get("url") or "", info.get("venue") or "")
    elif src == "stackexchange":
        for it in (json.loads(raw).get("items") or []):
            ts = it.get("creation_date")
            yr = datetime.fromtimestamp(ts, timezone.utc).year if ts else ""
            sc = it.get("score")
            snip = ("[MO score %s] " % sc if sc is not None else "") + ", ".join(it.get("tags", []))
            emit("stackexchange", it.get("title") or "", yr, it.get("link") or "", snip)
except Exception as ex:
    sys.stderr.write("[lit] parse-error(%s): %s\n" % (src, ex))
sys.exit(0)  # graceful: partial/zero records, never abort the run
PY
}

# ── run one backend: fetch → parse → append → per-backend reachability line to stderr ───────
emit_backend() {  # emit_backend <source> <url> <ext>
  local src="$1" url="$2" ext="$3" n=0 status tmp
  if fetch "$src" "$url" "$ext"; then
    [[ "$FETCH_CACHED" -eq 1 ]] && status="cached" || status="live"
    # A JSON backend that answers with non-JSON (e.g. DBLP behind Anubis returns HTTP 200 + an HTML
    # anti-bot page, so `curl -f` sees success) is BLOCKED, not "reachable, 0 hits" — surface it
    # honestly (the be-honest-about-reachability discipline) instead of folding a bot-block into the
    # genuine-empty-result path where a reader would misread it as "the source found nothing".
    if [[ "$ext" == "json" ]] && ! python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$FETCH_FILE" 2>/dev/null; then
      echo "[lit] ${src}: blocked (non-JSON response — anti-bot/HTML, not a genuine empty result)" >&2
      return 0
    fi
    tmp="$RECORDS.$src"
    parse "$src" "$FETCH_FILE" > "$tmp" 2>>"$RECORDS.err" || true
    n=$(wc -l < "$tmp" 2>/dev/null || echo 0); n="${n//[[:space:]]/}"
    [[ "$n" -gt 0 ]] && cat "$tmp" >> "$RECORDS"; rm -f "$tmp"
    if [[ "$n" -gt 0 ]]; then echo "[lit] ${src}: ${n} hit(s) (${status})" >&2
    else echo "[lit] ${src}: reachable, 0 parseable hits (${status})" >&2; fi
  else
    echo "[lit] ${src}: unreachable (blocked/timeout)" >&2
  fi
}

# ── local source: the Erdős problem row (decoupled from the not-yet-built erdos-fetch.sh) ───
erdos_yaml() {  # → path on stdout, or 1
  local cand y="$CACHE/erdosproblems.yaml"
  for cand in "$ERDOS_CACHE/src/problems.yaml" "$ERDOS_CACHE/problems.yaml" "$ERDOS_CACHE/${ERDOS}.yaml"; do
    [[ -f "$cand" ]] && { echo "$cand"; return 0; }
  done
  if [[ ! -f "$y" ]] || [[ $(( $(date +%s) - $(stat -c %Y "$y") )) -ge "$TTL" ]]; then
    _curl "$YAML_URL" -o "$y.tmp" 2>/dev/null && mv "$y.tmp" "$y" || rm -f "$y.tmp"
  fi
  [[ -f "$y" ]] && { echo "$y"; return 0; } || return 1
}

show_erdos() {  # show_erdos N  (to stdout in human mode, stderr in --json)
  local n="$1" yaml block summary out
  yaml="$(erdos_yaml)" || { echo "[lit] erdos #${n}: problems.yaml unavailable" >&2; return 0; }
  block="$(awk -v n="$n" '
    /^- number:/ { if ($0 == "- number: \"" n "\"") { s=1; print; next } else if (s) exit; else next }
    s { print }' "$yaml")"
  [[ -n "$block" ]] || { echo "[lit] erdos #${n}: not found in problems.yaml" >&2; return 0; }
  summary="$(BLOCK="$block" python3 - "$n" <<'PY'
import sys, os, re
n = sys.argv[1]; b = os.environ.get("BLOCK", "")
def g(p, d="?"):
    m = re.search(p, b); return m.group(1) if m else d
# anchor to line-start: "formal_status" is a substring of "informal_status", so unanchored
# patterns cross-match. (?m)^[ \t]* pins each key to its own indented line.
prize = g(r'(?m)^[ \t]*prize:\s*"([^"]*)"')
inf = re.search(r'(?m)^[ \t]*informal_status:[ \t]*\n[ \t]*state:\s*"([^"]*)"(?:[ \t]*\n[ \t]*last_update:\s*"([^"]*)")?', b)
istate = inf.group(1) if inf else "?"
iupd   = inf.group(2) if inf and inf.group(2) else "?"
fstate = g(r'(?m)^[ \t]*formal_status:[ \t]*\n[ \t]*state:\s*"([^"]*)"')
oeis   = g(r'(?m)^[ \t]*oeis:\s*\[([^\]]*)\]', "").replace('"', '')
print("[erdos] #%s  prize=%s  informal=%s  last_update=%s  formal_status=%s  oeis=[%s]"
      % (n, prize, istate, iupd, fstate, oeis))
PY
)"
  if [[ "$JSON" -eq 1 ]]; then printf '%s\n' "$summary" >&2
  else printf '%s\n\n' "$summary"; fi
}

# ── render the aggregated records (rank + dedup + since-filter) ──────────────────────────────
render() {
  if [[ "$JSON" -eq 0 ]]; then
    local c; c=$(grep -c . "$RECORDS" 2>/dev/null || echo 0)
    printf '── %s ── (%s raw hits, ranked top %s)\n' "$QUERY" "$c" "$MAX"
  fi
  python3 - "$RECORDS" "$QUERY" "$SINCE" "$JSON" "$MAX" <<'PY'
import sys, json, re
path, query, since_s, as_json, maxn = sys.argv[1:6]
as_json = (as_json == "1"); maxn = int(maxn)
since = int(since_s) if since_s.isdigit() else None
terms = {t for t in re.findall(r"[a-z0-9]+", query.lower()) if len(t) >= 3}

recs = []
with open(path) as f:
    for line in f:
        line = line.strip()
        if not line: continue
        try: r = json.loads(line)
        except Exception: continue
        yr = r.get("year", "")
        if since and yr.isdigit() and int(yr) < since: continue
        recs.append(r)

def score(r):
    hay = (r.get("title", "") + " " + r.get("snippet", "")).lower()
    s = sum(2 for t in terms if t in hay)
    yr = r.get("year", "")
    if yr.isdigit() and int(yr) >= 2015: s += 1
    return s

recs.sort(key=score, reverse=True)  # stable → ties keep backend dispatch order
seen, out = set(), []
for r in recs:
    key = re.sub(r"[^a-z0-9]", "", r.get("title", "").lower())[:60]
    if key in seen: continue
    seen.add(key); out.append(r)
out = out[:maxn]

if as_json:
    print(json.dumps(out, ensure_ascii=False, indent=2)); sys.exit(0)
if not out:
    print("(no parseable hits — try other phrasings / by problem number)"); sys.exit(0)
for i, r in enumerate(out, 1):
    print("[%2d] (%s, %s) %s" % (i, r["source"], r.get("year") or "----", r["title"]))
    if r.get("url"): print("     %s" % r["url"])
    sn = r.get("snippet", "")
    if sn: print("     %s" % (sn[:160] + ("…" if len(sn) > 160 else "")))
PY
}

# ── main ─────────────────────────────────────────────────────────────────────────────────────
[[ -n "$ERDOS" ]] && show_erdos "$ERDOS"

if [[ -n "$QUERY" ]]; then
  Q="$(urlenc "$QUERY")"
  emit_backend arxiv         "https://export.arxiv.org/api/query?search_query=all:${Q}&max_results=5"                                  xml
  emit_backend openalex      "https://api.openalex.org/works?search=${Q}&per-page=5"                                                   json
  emit_backend zbmath        "https://api.zbmath.org/v1/document/_search?search_string=${Q}&results_per_page=5&page=0"                 json
  emit_backend crossref      "https://api.crossref.org/works?query.bibliographic=${Q}&rows=5"                                          json
  emit_backend dblp          "https://dblp.org/search/publ/api?q=${Q}&format=json&h=5"                                                 json
  emit_backend stackexchange "https://api.stackexchange.com/2.3/search/advanced?site=mathoverflow&q=${Q}&order=desc&sort=relevance&pagesize=5" json
  render
elif [[ -z "$ERDOS" ]]; then
  awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"
fi
