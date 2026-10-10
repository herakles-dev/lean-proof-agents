#!/usr/bin/env bash
# solve.sh — run a finite-computation SEARCH and record a witness under a uniform contract.
#
# One JSON witness contract for every solver backend. MVP ships `sweep` (numpy — no venv needed,
# just `python3 -m pip install numpy` if your python3 lacks it); sat/smt/cas/graphs need the deferred solver stack
# (`scripts/solver-env.sh install`; not installed by default). Every run writes
# `.search/<id>/{witness.json, run.log}` (gitignored) so a search is reproducible + auditable.
#
#   scripts/solve.sh sweep --py PRED.py --range A B [--jobs N] [--id ID] [--attempt AID --subgoal SG]
#   scripts/solve.sh sat|smt|cas|graphs ...     # stub → run solver-env.sh install first (deferred)
#   scripts/solve.sh where [ID]                 # print the .search dir (and witness) for a run
#   scripts/solve.sh list                       # list recorded searches
#
# A predicate file (PRED.py) is a runnable script exposing CLI `--a A --b B [--jobs N]` that prints
# ONE json object to stdout: {"witnesses":[...], "checked":INT, "notes":{...}}. solve.sh wraps it in
# the witness envelope {id, shape, predicate, python, seed, started, wall_s, range:[A,B], checked,
# witnesses, notes}. A non-empty `witnesses` is a POSITIVE (prize-relevant) result; an empty list is
# an honest "no witness in [A,B)" — NEVER a proof (that is the Certify bridge's job on the witness).
# Requires: bash, python3 (+ numpy for `sweep`), awk, date, nproc.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
SEARCH="$ROOT/.search"

# sweep needs only numpy → prefer the solver venv if present, else system python3.
PY="python3"
[[ -x "$ROOT/.venv-solvers/bin/python" ]] && PY="$ROOT/.venv-solvers/bin/python"

case "${1:-}" in
  ""|-h|--help) awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0 ;;
esac
cmd="$1"; shift || true

case "$cmd" in
  where)
    id="${1:-}"; [[ -z "$id" ]] && { ls -1 "$SEARCH" 2>/dev/null || echo "(no searches yet)"; exit 0; }
    echo "$SEARCH/$id"; [[ -f "$SEARCH/$id/witness.json" ]] && cat "$SEARCH/$id/witness.json"
    ;;
  list)
    [[ -d "$SEARCH" ]] || { echo "(no searches yet)"; exit 0; }
    for d in "$SEARCH"/*/; do [[ -f "$d/witness.json" ]] && "$PY" - "$d/witness.json" <<'PYEOF'
import json,sys
j=json.load(open(sys.argv[1]))
print(f"{j.get('id'):28s} shape={j.get('shape'):7s} checked={j.get('checked')} witnesses={len(j.get('witnesses',[]))} wall={j.get('wall_s')}s")
PYEOF
    done
    ;;
  sat|smt|cas|graphs)
    echo "❌ '$cmd' needs the solver stack (z3/pysat/cvc5/…), which is not installed by default." >&2
    echo "   Install it sudo-free with: scripts/solver-env.sh install   (then re-run)." >&2
    exit 2
    ;;
  sweep)
    "$PY" -c 'import numpy' 2>/dev/null || { echo "error: sweep needs numpy — install it: $PY -m pip install numpy" >&2; exit 2; }
    PRED=""; A=""; B=""; JOBS="$(nproc)"; ID=""; AID=""; SG=""
    while [[ $# -gt 0 ]]; do
      case "$1" in
        --py)      PRED="$2"; shift 2 ;;
        --range)   A="$2"; B="$3"; shift 3 ;;
        --jobs)    JOBS="$2"; shift 2 ;;
        --id)      ID="$2"; shift 2 ;;
        --attempt) AID="$2"; shift 2 ;;
        --subgoal) SG="$2"; shift 2 ;;
        *) echo "unknown sweep arg: $1" >&2; exit 1 ;;
      esac
    done
    [[ -f "$PRED" && -n "$A" && -n "$B" ]] || { echo "usage: solve.sh sweep --py PRED.py --range A B [--jobs N] [--id ID]" >&2; exit 1; }
    stem="$(basename "$PRED" .py)"
    ID="${ID:-${stem}_${A}_${B}}"
    dir="$SEARCH/$ID"; mkdir -p "$dir"
    log="$dir/run.log"
    echo "→ sweep: $PRED over [$A,$B) jobs=$JOBS → $dir" | tee "$log" >&2
    started="$(date -Iseconds)"
    t0="$(date +%s.%N)"
    # Run the predicate; capture its JSON on stdout, tee stderr to the log.
    raw="$("$PY" "$PRED" --a "$A" --b "$B" --jobs "$JOBS" 2> >(tee -a "$log" >&2))" || {
      echo "❌ predicate failed (see $log)" >&2; exit 1; }
    t1="$(date +%s.%N)"
    wall="$(awk "BEGIN{printf \"%.2f\", $t1-$t0}")"
    # Wrap the predicate output in the uniform witness envelope.
    # (Predicate JSON is passed via env var, NOT stdin — stdin is the heredoc program here.)
    ENV_ID="$ID" ENV_SHAPE="sweep" ENV_PRED="$PRED" ENV_PY="$PY" ENV_A="$A" ENV_B="$B" \
    ENV_STARTED="$started" ENV_WALL="$wall" ENV_RAW="$raw" "$PY" - "$dir/witness.json" <<'PYEOF'
import json, os, sys
inner = json.loads(os.environ["ENV_RAW"])
env = {
 "id": os.environ["ENV_ID"], "shape": os.environ["ENV_SHAPE"],
 "predicate": os.environ["ENV_PRED"], "python": os.environ["ENV_PY"],
 "seed": None, "started": os.environ["ENV_STARTED"], "wall_s": float(os.environ["ENV_WALL"]),
 "range": [int(os.environ["ENV_A"]), int(os.environ["ENV_B"])],
 "checked": inner.get("checked"), "witnesses": inner.get("witnesses", []),
 "notes": inner.get("notes", {}),
}
json.dump(env, open(sys.argv[1], "w"), indent=2)
print(json.dumps({"id": env["id"], "checked": env["checked"], "witnesses": env["witnesses"],
                  "wall_s": env["wall_s"], "notes": env["notes"]}, indent=2))
PYEOF
    # Best-effort ledger attempt (only when a DEPTH attempt id is supplied).
    if [[ -n "$AID" && -n "$SG" ]]; then
      nw="$("$PY" -c 'import json,sys;print(len(json.load(open(sys.argv[1]))["witnesses"]))' "$dir/witness.json")"
      res="fail"; [[ "$nw" != "0" ]] && res="ok"
      scripts/proof-ledger.sh attempt "$AID" "$SG" --tier solver --sketch "sweep $stem [$A,$B)" --result "$res" --delta 0 2>/dev/null || \
        echo "(ledger note skipped — no active attempt $AID)" >&2
    fi
    echo "✔ witness record: $dir/witness.json" >&2
    ;;
  *) echo "unknown subcommand: $cmd (see --help)" >&2; exit 1 ;;
esac
