#!/usr/bin/env bash
# putnam-harness.sh — compile-filter PutnamBench statements + track a solve-rate.
#
# Companion to putnam-fetch.sh. Two jobs:
#   1. FILTER — upstream pins Lean v4.27; we run v4.33. A statement is only *attemptable* here if
#      it still ELABORATES against our Mathlib (a `sorry` body is fine — we only ask that the
#      statement type-checks). API drift shows up as a hard error → NOT portable. The filter runs
#      each cached statement through `lake env lean` and splits them into attemptable / non-portable.
#   2. SCORE — a solve-rate ledger. The DEPTH loop records an outcome per target; `score` reports
#      solved / attempted (honest ABANDON counts against you), cross-referenced with the filter.
#
#   scripts/putnam-harness.sh filter [id...]        # compile-filter cached (or listed) problems (parallel)
#   scripts/putnam-harness.sh attemptable           # print the current compile-PASS set
#   scripts/putnam-harness.sh nonportable           # print compile-FAIL set with the drift reason
#   scripts/putnam-harness.sh show <id>             # print a cached statement (+ its answer comment)
#   scripts/putnam-harness.sh attempt <id> <solved|abandoned|blocked> [note]   # log an outcome
#   scripts/putnam-harness.sh score                 # solve-rate over logged attempts
#
# Filter is Lean's verdict, not ours: PASS = `lake env lean` exits 0 with no `error:` (sorry
# warnings allowed). NOT a proof of anything — just "this statement is well-formed under our toolchain".
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
. "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"

CACHE="$ROOT/.putnam-cache"
SRC="$CACHE/src"
PASS="$CACHE/compile-pass.txt"
FAIL="$CACHE/compile-fail.tsv"
ATTEMPTS="$CACHE/attempts.tsv"

norm_id() { local x="${1%.lean}"; [[ "$x" == putnam_* ]] || x="putnam_$x"; echo "$x"; }

# Internal: elaborate ONE cached statement, print "<id>\tPASS" or "<id>\tFAIL\t<reason>". Never exits nonzero.
_check1() {
  local id f tmp out rc reason
  id="$(norm_id "$1")"; f="$SRC/$id.lean"
  [[ -s "$f" ]] && : || { printf '%s\tFAIL\tnot-cached\n' "$id"; return 0; }
  tmp="$(mktemp --suffix=.lean)"
  # Elaborate as upstream authored it: Mathlib/PutnamBench use `autoImplicit false`, so a drifted
  # (renamed/removed) identifier ERRORS instead of being silently auto-bound as an implicit → a
  # false PASS. Inject the option right after the import block (it must follow `import`).
  awk 'ins==0 && $0 !~ /^import / {print "set_option autoImplicit false"; ins=1} {print}' "$f" > "$tmp"
  # Exit code is the authoritative verdict: `lean` returns 0 iff there are no errors (a `sorry` body
  # yields only a warning, rc still 0). Errors → nonzero. (Reason text is best-effort only — this
  # Lean tags diagnostics `error(lean.xxx):` as well as plain `error:`, so match both, never fatally.)
  if out="$(timeout 180 lake env lean "$tmp" 2>&1)"; then rc=0; else rc=$?; fi
  rm -f "$tmp"
  if [[ $rc -eq 0 ]]; then
    printf '%s\tPASS\n' "$id"
  else
    reason="$(grep -m1 -E 'error(\(|:)' <<<"$out" | sed -E 's#^/[^:]*:[0-9]+:[0-9]+: *##; s/\t/ /g' | cut -c1-140 || true)"
    [[ $rc -eq 124 ]] && reason="timeout (>180s)"
    printf '%s\tFAIL\t%s\n' "$id" "${reason:-elaboration-error (exit $rc)}"
  fi
}

case "${1:-}" in
  ""|-h|--help) awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0 ;;
esac
cmd="$1"; shift || true

case "$cmd" in
  _check1) _check1 "$1" ;;   # (internal, used by the parallel driver)

  filter)
    mkdir -p "$SRC"
    if [[ $# -ge 1 ]]; then ids=(); for a in "$@"; do ids+=("$(norm_id "$a")"); done
    else mapfile -t ids < <(ls "$SRC"/*.lean 2>/dev/null | xargs -r -n1 basename | sed 's/\.lean$//'); fi
    [[ ${#ids[@]} -ge 1 ]] || { echo "(nothing cached to filter — run putnam-fetch.sh sample N)" >&2; exit 1; }
    jobs="$(nproc 2>/dev/null || echo 4)"; (( jobs > 6 )) && jobs=6   # cap: concurrent Mathlib elab is RAM-heavy
    echo "→ compile-filtering ${#ids[@]} statement(s) at -P$jobs (our $(cat "$ROOT/lean-toolchain"); upstream v4.27)…" >&2
    results="$(printf '%s\n' "${ids[@]}" | xargs -P "$jobs" -I{} "$ROOT/scripts/putnam-harness.sh" _check1 {})"
    awk -F'\t' '$2=="PASS"{print $1}' <<<"$results" | sort > "$PASS"
    awk -F'\t' '$2=="FAIL"{print $1"\t"$3}' <<<"$results" | sort > "$FAIL"
    np="$(wc -l < "$PASS")"; nf="$(wc -l < "$FAIL")"
    echo "✅ attemptable (elaborates): $np   ⬜ non-portable (drift): $nf   → $PASS / $FAIL"
    [[ $nf -gt 0 ]] && { echo "  top drift reasons:"; cut -f2 "$FAIL" | sort | uniq -c | sort -rn | head -5 | sed 's/^/   /'; } || true ;;

  attemptable) [[ -f "$PASS" ]] || { echo "(no filter run yet — putnam-harness.sh filter)" >&2; exit 1; }
               [[ -s "$PASS" ]] && cat "$PASS" || echo "(0 attemptable — every cached statement drifted; see nonportable)" ;;
  nonportable) [[ -f "$FAIL" ]] || { echo "(no filter run yet — putnam-harness.sh filter)" >&2; exit 1; }
               [[ -s "$FAIL" ]] && column -t -s$'\t' "$FAIL" || echo "(0 non-portable — every cached statement elaborates)" ;;

  show)
    [[ -n "${1:-}" ]] || { echo "usage: putnam-harness.sh show <id>" >&2; exit 1; }
    f="$SRC/$(norm_id "$1").lean"; [[ -s "$f" ]] || { echo "(not cached: $(norm_id "$1"))" >&2; exit 1; }
    cat "$f" ;;

  attempt)
    [[ $# -ge 2 ]] || { echo "usage: putnam-harness.sh attempt <id> <solved|abandoned|blocked> [note]" >&2; exit 1; }
    id="$(norm_id "$1")"; status="$2"; shift 2; note="${*:-}"
    case "$status" in solved|abandoned|blocked) ;; *) echo "status must be solved|abandoned|blocked" >&2; exit 1 ;; esac
    printf '%s\t%s\t%s\t%s\n' "$(date -Iseconds)" "$id" "$status" "$note" >> "$ATTEMPTS"
    echo "logged: $id → $status" ;;

  score)
    [[ -s "$ATTEMPTS" ]] || { echo "(no attempts logged yet — putnam-harness.sh attempt <id> <status>)" >&2; exit 1; }
    # last status per id wins
    awk -F'\t' '{st[$2]=$3} END{
      s=0;a=0;b=0;n=0;
      for(id in st){n++; if(st[id]=="solved")s++; else if(st[id]=="abandoned")a++; else if(st[id]=="blocked")b++}
      printf "attempted: %d   solved: %d   abandoned: %d   blocked: %d\n", n,s,a,b;
      if(n>0) printf "attempted solve-rate: %.1f%% (%d/%d attempted)\n", 100*s/n, s, n;
    }' "$ATTEMPTS"
    if [[ -s "$PASS" ]]; then
      inpass="$(awk -F'\t' 'NR==FNR{p[$1]=1;next}{last[$2]=1} END{c=0;for(id in last) if(p[id])c++; print c}' "$PASS" "$ATTEMPTS")"
      echo "  ($inpass of the attempted ids are in the compile-PASS set)"
      # HONEST corpus denominator: solved ids over the full compile-PASS (attemptable) corpus,
      # not just over what we chose to attempt. Prevents a hand-picked 5/5 reading as "100%".
      awk -F'\t' '
        NR==FNR{ if($0!=""){p[$1]=1; tot++} ; next }
        { st[$2]=$3 }
        END{ c=0; for(id in st) if(st[id]=="solved" && p[id]) c++;
             if(tot>0) printf "corpus solve-rate: %.1f%% (%d/%d attemptable) — the honest denominator\n", 100*c/tot, c, tot }' "$PASS" "$ATTEMPTS"
    fi ;;

  *) echo "unknown command: $cmd (try --help)" >&2; exit 1 ;;
esac
