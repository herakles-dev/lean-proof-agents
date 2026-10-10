#!/usr/bin/env bash
# proof-ledger.sh — the subgoal ledger for DEPTH-controlled proof attempts.
#
# The trajectory-management layer (docs/PROOF_METHODOLOGY.md Part E) needs a durable, offline
# record of ONE hard proof attempt: its subgoal DAG (AND deps / OR approaches), per-attempt
# progress (goal_delta), dead-ends never to repeat, and the keeper's decisions. This script IS
# that record — the `proof-strategist` inits it, `lean-prover`(+opus) attempts against it, and the
# `proof-trajectory-keeper` reads `stall-check` to decide continue/escalate/re-plan/abandon.
#
# One JSON file per attempt under .proof-ledger/ (gitignored). No network. Requires jq.
#
#   scripts/proof-ledger.sh init  <attempt_id> <module> <thm> [--statement S] [--total N] [--cap N]
#   scripts/proof-ledger.sh add   <attempt_id> <sg_id> "<goal>" [--kind leaf|node] [--deps a,b]
#                                                       [--approaches "x;y"] [--tier T]
#   scripts/proof-ledger.sh attempt <attempt_id> <sg_id> --tier T --sketch "…" \
#                                       --result fail|ok --delta N [--error "…"]
#   scripts/proof-ledger.sh mark   <attempt_id> <sg_id> <open|in_progress|solved|dead|deferred>
#   scripts/proof-ledger.sh dead-end <attempt_id> <sg_id> "<why it failed>"
#   scripts/proof-ledger.sh decision <attempt_id> --trigger T --decision D [--subgoal id] [--why …]
#   scripts/proof-ledger.sh checkpoint <attempt_id> <sg_id> "<have/calc name>"
#   scripts/proof-ledger.sh stall-check <attempt_id> [<sg_id>]   # verdict JSON for the keeper
#   scripts/proof-ledger.sh status <attempt_id>                   # human-readable summary
#   scripts/proof-ledger.sh path   <attempt_id>                   # print the ledger file path
#   scripts/proof-ledger.sh list                                  # list all attempt ids
#
# `goal_delta` convention: change in (open goals + sorries) after the attempt. delta < 0 = PROGRESS.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEDGER_DIR="${PROOF_LEDGER_DIR:-$ROOT/.proof-ledger}"
command -v jq >/dev/null 2>&1 || { echo "proof-ledger: jq is required" >&2; exit 3; }

now() { date -u +%Y-%m-%dT%H:%M:%SZ; }
lpath() { printf '%s/%s.json' "$LEDGER_DIR" "$1"; }
die() { echo "proof-ledger: $*" >&2; exit 2; }
need_ledger() { [[ -f "$(lpath "$1")" ]] || die "no ledger for '$1' (run: proof-ledger.sh init $1 <module> <thm>)"; }

# In-place jq edit of a ledger file. Serialized per-ledger with flock (parallel-swarm race)
# and leak-free: the temp is always removed, including on a jq failure (e.g. a guard `error(...)`).
edit() { # edit <attempt_id> <jq-filter> [--arg k v ...]
  local id="$1"; shift
  local f; f="$(lpath "$id")"
  local tmp; tmp="$(mktemp)"
  local lock="${f}.lock"
  local rc=0
  {
    if flock 9; then
      if jq "$@" "$f" > "$tmp"; then mv "$tmp" "$f" || rc=$?; else rc=$?; fi
    else
      echo "proof-ledger: could not acquire lock on $lock" >&2; rc=4
    fi
    true   # keep the block's exit status 0 so `set -e` never pre-empts the cleanup below
  } 9>>"$lock"
  rm -f "$tmp"
  return $rc
}

sub="${1:-}"; shift || true
case "$sub" in

  init)
    id="${1:-}"; module="${2:-}"; thm="${3:-}"; shift 3 2>/dev/null || true
    [[ -n "$id" && -n "$module" && -n "$thm" ]] || die "usage: init <attempt_id> <module> <thm> [--statement S] [--total N] [--cap N]"
    statement=""; total=12; cap=4; wall=90
    while [[ $# -gt 0 ]]; do case "$1" in
      --statement) statement="$2"; shift 2;;
      --total) total="$2"; shift 2;;
      --cap) cap="$2"; shift 2;;
      --wall) wall="$2"; shift 2;;
      *) die "init: unknown flag $1";; esac; done
    mkdir -p "$LEDGER_DIR"
    f="$(lpath "$id")"
    [[ -f "$f" ]] && die "ledger already exists: $f (delete it to re-init)"
    jq -n --arg id "$id" --arg m "$module" --arg t "$thm" --arg s "$statement" \
          --arg created "$(now)" --argjson total "$total" --argjson cap "$cap" --argjson wall "$wall" '{
      attempt_id:$id,
      target:{module:$m, theorem:$t, statement:$s},
      created:$created,
      status:"active",
      budget:{total_attempts:$total, spent:0, per_subgoal_cap:$cap, wall_clock_min:$wall},
      plan_version:1,
      subgoals:[],
      decisions:[],
      dead_end_log:[]
    }' > "$f"
    echo "initialized ledger: $f"
    ;;

  add)
    id="${1:-}"; sg="${2:-}"; goal="${3:-}"; shift 3 2>/dev/null || true
    need_ledger "$id"; [[ -n "$sg" && -n "$goal" ]] || die "usage: add <attempt_id> <sg_id> \"<goal>\" [--kind leaf|node] [--deps a,b] [--approaches \"x;y\"] [--tier T]"
    kind="leaf"; deps=""; approaches=""; tier="sonnet"
    while [[ $# -gt 0 ]]; do case "$1" in
      --kind) kind="$2"; shift 2;;
      --deps) deps="$2"; shift 2;;
      --approaches) approaches="$2"; shift 2;;
      --tier) tier="$2"; shift 2;;
      *) die "add: unknown flag $1";; esac; done
    depsj="$(jq -Rc 'split(",")|map(select(length>0))' <<<"$deps")"
    apprj="$(jq -Rc 'split(";")|map(select(length>0))' <<<"$approaches")"
    edit "$id" --arg sg "$sg" --arg goal "$goal" --arg kind "$kind" --arg tier "$tier" \
               --argjson deps "$depsj" --argjson appr "$apprj" '
      if any(.subgoals[]; .id==$sg) then error("subgoal \($sg) already exists") else . end
      | .subgoals += [{
          id:$sg, goal:$goal, kind:$kind, deps:$deps, approaches:$appr,
          status:"open", tier:$tier, attempts:[], dead_ends:[], checkpoints:[], notes:""
        }]'
    echo "added subgoal $sg ($kind, tier=$tier) to $id"
    ;;

  attempt)
    id="${1:-}"; sg="${2:-}"; shift 2 2>/dev/null || true
    need_ledger "$id"; [[ -n "$sg" ]] || die "usage: attempt <attempt_id> <sg_id> --tier T --sketch \"…\" --result fail|ok --delta N [--error \"…\"]"
    tier=""; sketch=""; result=""; delta=""; error=""
    while [[ $# -gt 0 ]]; do case "$1" in
      --tier) tier="$2"; shift 2;;
      --sketch) sketch="$2"; shift 2;;
      --result) result="$2"; shift 2;;
      --delta) delta="$2"; shift 2;;
      --error) error="$2"; shift 2;;
      *) die "attempt: unknown flag $1";; esac; done
    [[ -n "$tier" && -n "$sketch" && -n "$result" && -n "$delta" ]] || die "attempt requires --tier --sketch --result --delta"
    edit "$id" --arg sg "$sg" --arg tier "$tier" --arg sketch "$sketch" \
               --arg result "$result" --argjson delta "$delta" --arg error "$error" '
      if any(.subgoals[]; .id==$sg) then . else error("no subgoal \($sg)") end
      | .budget.spent += 1
      | .subgoals |= map(
          if .id==$sg then
            .attempts += [{n:((.attempts|length)+1), tier:$tier, sketch:$sketch,
                           result:$result, error:$error, goal_delta:$delta}]
            | .tier=$tier
            | .status=(if $result=="ok" then "solved" else "in_progress" end)
          else . end)'
    echo "recorded attempt on $sg (result=$result, delta=$delta); budget spent now $(jq '.budget.spent' "$(lpath "$id")")/$(jq '.budget.total_attempts' "$(lpath "$id")")"
    ;;

  mark)
    id="${1:-}"; sg="${2:-}"; st="${3:-}"
    need_ledger "$id"; [[ -n "$sg" && -n "$st" ]] || die "usage: mark <attempt_id> <sg_id> <open|in_progress|solved|dead|deferred>"
    case "$st" in open|in_progress|solved|dead|deferred) ;; *) die "bad status: $st";; esac
    edit "$id" --arg sg "$sg" --arg st "$st" \
      'if any(.subgoals[]; .id==$sg) then (.subgoals |= map(if .id==$sg then .status=$st else . end))
       else error("no subgoal \($sg)") end'
    # If all subgoals solved, mark the attempt solved.
    edit "$id" '.status = (if (.subgoals|length>0) and all(.subgoals[]; .status=="solved") then "solved" else .status end)'
    echo "marked $sg = $st"
    ;;

  dead-end)
    id="${1:-}"; sg="${2:-}"; why="${3:-}"
    need_ledger "$id"; [[ -n "$sg" && -n "$why" ]] || die "usage: dead-end <attempt_id> <sg_id> \"<why>\""
    edit "$id" --arg sg "$sg" --arg why "$why" '
      if any(.subgoals[]; .id==$sg) then
        (.subgoals |= map(if .id==$sg then .dead_ends += [$why] else . end)
         | .dead_end_log += [{subgoal:$sg, why:$why}])
      else error("no subgoal \($sg)") end'
    echo "logged dead-end on $sg"
    ;;

  checkpoint)
    id="${1:-}"; sg="${2:-}"; cp="${3:-}"
    need_ledger "$id"; [[ -n "$sg" && -n "$cp" ]] || die "usage: checkpoint <attempt_id> <sg_id> \"<have/calc name>\""
    edit "$id" --arg sg "$sg" --arg cp "$cp" \
      'if any(.subgoals[]; .id==$sg) then (.subgoals |= map(if .id==$sg then .checkpoints += [$cp] else . end))
       else error("no subgoal \($sg)") end'
    echo "checkpoint on $sg: $cp"
    ;;

  decision)
    id="${1:-}"; shift 1 2>/dev/null || true
    need_ledger "$id"
    trigger=""; decision=""; subgoal=""; why=""
    while [[ $# -gt 0 ]]; do case "$1" in
      --trigger) trigger="$2"; shift 2;;
      --decision) decision="$2"; shift 2;;
      --subgoal) subgoal="$2"; shift 2;;
      --why|--rationale) why="$2"; shift 2;;
      *) die "decision: unknown flag $1";; esac; done
    [[ -n "$trigger" && -n "$decision" ]] || die "decision requires --trigger and --decision"
    edit "$id" --arg at "$(now)" --arg tr "$trigger" --arg d "$decision" --arg sg "$subgoal" --arg why "$why" \
      '.decisions += [{at:$at, trigger:$tr, decision:$d, subgoal:$sg, rationale:$why}]'
    echo "logged decision: $trigger → $decision${subgoal:+ (on $subgoal)}"
    ;;

  stall-check)
    id="${1:-}"; sg="${2:-}"
    need_ledger "$id"
    # Per-subgoal verdict; if no sg given, report the worst open subgoal + global budget.
    if [[ -n "$sg" ]]; then
      jq --arg sg "$sg" '
        .budget as $b
        | ((.subgoals[] | select(.id==$sg)) // error("no subgoal \($sg)")) as $s
        | ($s.attempts | length) as $n
        | [ $s.attempts[].goal_delta ] as $deltas
        | ( [ $s.attempts[].sketch | ascii_downcase | gsub("\\s+";" ") ]
            | group_by(.) | map(select(length>1)) | length > 0 ) as $thrash
        | ( ($deltas|length)>0 and ([ $deltas[] | select(. < 0) ]|length==0) ) as $noprog
        | { subgoal:$sg, status:$s.status, attempts:$n,
            per_subgoal_cap:$b.per_subgoal_cap, budget_spent:$b.spent, budget_total:$b.total_attempts,
            deltas:$deltas, thrash:$thrash, no_progress:$noprog,
            verdict:( if $b.spent >= $b.total_attempts then "BUDGET_EXHAUSTED"
                      elif $s.status=="solved" then "OK"
                      elif $n >= $b.per_subgoal_cap then "STALL"
                      elif $thrash then "THRASH"
                      elif ($n>0 and $noprog) then "STALL"
                      else "OK" end) }' "$(lpath "$id")"
    else
      jq '
        .budget as $b
        | [ .subgoals[] | select(.status!="solved" and .status!="dead" and .status!="deferred") ] as $open
        | { attempt:.attempt_id, plan_version:.plan_version, status:.status,
            budget_spent:$b.spent, budget_total:$b.total_attempts,
            budget_verdict:( if $b.spent >= $b.total_attempts then "BUDGET_EXHAUSTED"
                             elif ($b.total_attempts>0 and $b.spent*2 >= $b.total_attempts
                                   and ([.subgoals[]|select(.status=="solved")]|length)*2 < (.subgoals|length))
                                  then "REPLAN_SUGGESTED"
                             else "OK" end),
            open_subgoals:($open|length),
            stalled:[ $open[]
              | ((.attempts|length)) as $n
              | [ .attempts[].goal_delta ] as $d
              | select( $n >= $b.per_subgoal_cap
                        or ( ($d|length)>0 and ([$d[]|select(.<0)]|length==0) )
                        or ( [ .attempts[].sketch|ascii_downcase|gsub("\\s+";" ") ]|group_by(.)|map(select(length>1))|length>0 ) )
              | .id ] }' "$(lpath "$id")"
    fi
    ;;

  status)
    id="${1:-}"; need_ledger "$id"
    jq -r '
      "attempt: \(.attempt_id)   [\(.status)]   plan v\(.plan_version)",
      "target:  \(.target.module) :: \(.target.theorem)",
      "budget:  \(.budget.spent)/\(.budget.total_attempts) attempts spent   per-subgoal cap \(.budget.per_subgoal_cap)",
      "subgoals (\(.subgoals|length)):",
      ( .subgoals[]
        | "  [\(.status|.[0:1]|ascii_upcase)] \(.id) (\(.kind), \(.tier))  attempts=\(.attempts|length)"
          + (if (.attempts|length)>0 then "  lastΔ=\(.attempts[-1].goal_delta)" else "" end)
          + (if (.deps|length)>0 then "  deps=[\(.deps|join(","))]" else "" end)
          + (if (.dead_ends|length)>0 then "  dead-ends=\(.dead_ends|length)" else "" end)
        ),
      (if (.dead_end_log|length)>0 then "dead-end log: \(.dead_end_log|length) entr(y/ies)" else empty end),
      (if (.decisions|length)>0 then "decisions: \(.decisions|length) logged (last: \(.decisions[-1].trigger)→\(.decisions[-1].decision))" else empty end)
    ' "$(lpath "$id")"
    ;;

  path) id="${1:-}"; [[ -n "$id" ]] || die "usage: path <attempt_id>"; echo "$(lpath "$id")" ;;

  list) mkdir -p "$LEDGER_DIR"; ls -1 "$LEDGER_DIR"/*.json 2>/dev/null | sed 's|.*/||;s|\.json$||' || echo "(no ledgers)";;

  ""|-h|--help|help)
    awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "${BASH_SOURCE[0]}"
    ;;

  *) die "unknown subcommand: $sub (try --help)";;
esac
