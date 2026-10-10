#!/usr/bin/env bash
# zulip.sh — read-only Lean Zulip client (leanprover.zulipchat.com) for claim-status recon.
#
# Blueprint lemmas are claimed socially in project streams/topics. Before targeting a leaf
# lemma (from scripts/blueprint-leaves.sh), search Zulip to see if someone already claimed it.
# READ-ONLY by design — this script never posts. Creds (ZULIP_SITE / ZULIP_EMAIL / ZULIP_API_KEY)
# come from the environment or a local .env file (see .env.example); the key is never printed or committed,
# and is handed to curl on stdin (a config), not on its command line. ZULIP_SITE must be https://.
# Requires: bash, curl, jq (and network access).
#
#   scripts/zulip.sh me                              # auth check (whoami)
#   scripts/zulip.sh streams [filter]                # list streams (optional name filter)
#   scripts/zulip.sh search "<query>" [N]            # full-text search (default 20 msgs)
#   scripts/zulip.sh messages "<stream>" ["<topic>"] [N]   # recent messages in a stream/topic
#   scripts/zulip.sh claimed "<lemma-or-node-id>"    # search convenience for claim recon
set -euo pipefail

ENVFILE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/.env"
envget() {  # envget NAME -> value from the .env file (empty if absent)
  [[ -f "$ENVFILE" ]] || return 0
  grep -E "^(export )?$1=" "$ENVFILE" | head -1 | sed -E "s/^(export )?$1=//; s/^\"//; s/\"\$//" || true
}
for v in ZULIP_SITE ZULIP_EMAIL ZULIP_API_KEY; do
  [[ -z "${!v:-}" ]] && export "$v=$(envget "$v")"
done
: "${ZULIP_SITE:=https://leanprover.zulipchat.com}"
if [[ -z "${ZULIP_EMAIL:-}" || -z "${ZULIP_API_KEY:-}" ]]; then
  echo "error: no ZULIP_EMAIL / ZULIP_API_KEY found (checked env + .env)" >&2; exit 2
fi
if [[ "$ZULIP_SITE" != https://* ]]; then
  echo "error: ZULIP_SITE must be an https:// URL (got: $ZULIP_SITE)" >&2; exit 2
fi
API="$ZULIP_SITE/api/v1"
# Credentials go to curl as a config on stdin (printf is a builtin → never in any argv/ps).
zq() {
  local u="$ZULIP_EMAIL:$ZULIP_API_KEY"
  u="${u//\\/\\\\}"; u="${u//\"/\\\"}"      # escape \ and " for the curl config syntax
  printf 'user = "%s"\n' "$u" | curl -sS -K - "$@"
}

cmd="${1:-me}"; shift || true

case "$cmd" in
  me)
    zq "$API/users/me" | jq -r '"\(.full_name) <\(.email)> — user_id \(.user_id), role \(.role), bot=\(.is_bot)"'
    ;;
  streams)
    filter="${1:-}"
    zq "$API/streams" | jq -r '.streams[].name' | { [[ -n "$filter" ]] && grep -i "$filter" || cat; } | sort
    ;;
  search|claimed)
    q="${1:-}"; n="${2:-20}"
    [[ -z "$q" ]] && { echo "usage: zulip.sh $cmd \"<query>\" [N]" >&2; exit 1; }
    # search public channels too (not just subscribed): Zulip needs an explicit
    # channels:public operand, else full-text search only covers subscribed streams.
    narrow="$(jq -nc --arg q "$q" '[{operator:"channels",operand:"public"},{operator:"search",operand:$q}]')"
    zq -G "$API/messages" \
       --data-urlencode "anchor=newest" --data-urlencode "num_before=$n" --data-urlencode "num_after=0" \
       --data-urlencode "apply_markdown=false" --data-urlencode "narrow=$narrow" \
      | jq -r '.messages[]? | "[\(.timestamp|todate)] \(.sender_full_name)  #\(.display_recipient) › \(.subject)\n    \((.content|gsub("[\n]+";" "))[:240])"'
    ;;
  messages)
    stream="${1:-}"; topic="${2:-}"; n="${3:-20}"
    [[ -z "$stream" ]] && { echo "usage: zulip.sh messages \"<stream>\" [\"<topic>\"] [N]" >&2; exit 1; }
    narrow="$(jq -nc --arg s "$stream" --arg t "$topic" \
      '[{operator:"stream",operand:$s}] + (if $t=="" then [] else [{operator:"topic",operand:$t}] end)')"
    zq -G "$API/messages" \
       --data-urlencode "anchor=newest" --data-urlencode "num_before=$n" --data-urlencode "num_after=0" \
       --data-urlencode "apply_markdown=false" --data-urlencode "narrow=$narrow" \
      | jq -r '.messages[]? | "[\(.timestamp|todate)] \(.sender_full_name) › \(.subject)\n    \((.content|gsub("[\n]+";" "))[:240])"'
    ;;
  -h|--help|help)
    sed -n '2,15p' "$0" | sed 's/^# \{0,1\}//' ;;
  *) echo "unknown subcommand: $cmd (try: me | streams | search | messages | claimed)" >&2; exit 1 ;;
esac
