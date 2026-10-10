#!/usr/bin/env bash
# verify-all.sh — regression gate: certify challenge modules (no sorry, clean axioms, compiles).
#
#   scripts/verify-all.sh                 # audit ALL challenges (parallel), exit 1 if any fail
#   scripts/verify-all.sh --table         # also print a Markdown SOLVED table
#   scripts/verify-all.sh C0024 C0025     # audit only these modules: a `C####` number, a full
#                                         # module name, or a path — the pre-commit hook passes
#                                         # just the staged modules
#
# Re-elaborates each challenge with `lake env lean` (no cached olean) so a lingering `sorry`, a
# build error, or an axiom outside the trusted trio is caught. Template.lean is excluded. Audits
# run in parallel (min(nproc,6)-way; override with $VERIFY_JOBS); output is collected + sorted.
# The axiom check covers every constant each file declares, not only the theorems a text pattern
# finds (see run_audit below; its limits are spelled out in check-proof.sh's header).
#
# Exit: 0 all passed · 1 at least one module failed or returned no result · 2 nothing was run
# (unknown option, a requested module that does not exist, or Mathlib not built — run ./setup.sh).
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
. "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"
CH="$ROOT/MathProof/Challenges"
CERT="$ROOT/MathProof/Certify"   # the witness→Lean "moat" library (gated on full runs, see below)

TABLE=false
declare -a MODARGS=()
for a in "$@"; do
  case "$a" in
    --table) TABLE=true ;;
    -*)      echo "verify-all.sh: unknown option: $a (usage: verify-all.sh [--table] [C####|module|path …])" >&2; exit 2 ;;
    *)       MODARGS+=("$a") ;;
  esac
done

# Trusted axiom set — the ONLY axioms a completed proof may depend on. Anything else (sorryAx,
# native_decide's compiler axiom, a stray `axiom`) is a soundness escape. `sorry` alone is not
# the whole of "Lean is the only source of truth".
TRUSTED_AXIOMS='propext|Classical\.choice|Quot\.sound'

# last_lines <text> → the tail of Lean's output on ONE line, for a FAIL note: its last 3
# `error` lines if it has any (Lean keeps elaborating after an error, so the very last lines are
# usually the appended audit's), else its last 3 non-empty lines. Tabs and `|` would break the
# result line / the Markdown table, so they are replaced.
last_lines() {
  printf '%s\n' "$1" | tr '\t|' ' /' | awk 'NF { a[++n] = $0; if ($0 ~ /error/) e[++m] = $0 }
    END { if (m > 0) { n = m; for (i = 1; i <= m; i++) a[i] = e[i] }
          s = (n > 3 ? n - 2 : 1); for (i = s; i <= n; i++) printf "%s%s", (i > s ? " ⏎ " : ""), a[i] }' \
    | cut -c1-400
}

# run_audit <file> <decl-name...> — ONE from-scratch elaboration (no cached olean) of the source
# (+ trailing-newline guard) with, appended: a `#print axioms` per given name, and the SWEEP
# command (list-qualified-thms.sh --sweep) that walks every constant the file declares, straight
# from Lean's environment. Build errors, `sorry`, and axiom hygiene are all decided in this single
# pass. Sets AUDIT_OUT (Lean's output without the sweep's lines) and AUDIT_FAIL (the failure
# note; empty = it built, no sorry, every report came back, the sweep ran to its end, and no
# axiom outside the trusted trio turned up in either).
run_audit() {
  local file="$1"; shift
  local tmp out tag sw n nrep swept viol
  AUDIT_OUT=""; AUDIT_FAIL=""
  tag="AXSWEEP-$(od -An -N8 -tx1 /dev/urandom | tr -d ' \n')"   # unguessable by the module
  tmp="$(mktemp --suffix=.lean)"; cat "$file" > "$tmp"; printf '\n' >> "$tmp"
  for n in "$@"; do [[ -n "$n" ]] && printf '#print axioms %s\n' "$n" >> "$tmp"; done
  "$ROOT/scripts/list-qualified-thms.sh" --sweep "$tag" >> "$tmp"
  if ! out="$(lake env lean "$tmp" 2>&1)"; then
    AUDIT_FAIL="build error: $(last_lines "${out//"$tmp"/${file#"$ROOT"/}}")"; rm -f "$tmp"
    [[ -n "$out" ]] || AUDIT_FAIL="build error: lean exited non-zero with no output"
    return
  fi
  rm -f "$tmp"
  sw="$(printf '%s\n' "$out" | grep "^$tag"$'\t')"
  out="$(printf '%s\n' "$out" | grep -v "^$tag"$'\t')"; AUDIT_OUT="$out"
  if printf '%s' "$out" | grep -qiE "declaration uses .?sorry|sorryAx"; then AUDIT_FAIL="uses sorry"; return; fi
  nrep="$(printf '%s\n' "$out" | grep -cE "' (depends on axioms:|does not depend on any axioms)")"
  if (( nrep < $# )); then AUDIT_FAIL="axiom audit incomplete: $nrep report(s) for $# declaration(s)"; return; fi
  swept="$(printf '%s\n' "$sw" | awk -F'\t' '$2 == "swept" { print $3 }')"
  [[ "$swept" =~ ^[0-9]+$ ]] || { AUDIT_FAIL="axiom sweep did not run to its end"; return; }
  viol="$( { printf '%s' "$out" | tr '\n' ' ' | grep -oE "depends on axioms: \[[^]]*\]" \
             | grep -oE "\[[^]]*\]" | tr -d '[]' | tr ',' '\n' | sed 's/^ *//; s/ *$//'
             printf '%s\n' "$sw" | awk -F'\t' '$2 == "axiom" { print $3 }'; } \
          | grep -vE '^$' | grep -vxE "$TRUSTED_AXIOMS" | sort -u | tr '\n' ' ' | sed 's/ *$//')"
  [[ -n "$viol" ]] && AUDIT_FAIL="unsafe axioms: $(printf '%s' "$viol" | tr '|' '/')"
}

# audit_module <file> <mod> → echoes "STATUS|note" for a challenge: run_audit over the theorems
# list-qualified-thms.sh finds; a challenge in which it finds none is a FAIL.
audit_module() {
  local file="$1" mod="$2"; local -a thms
  mapfile -t thms < <("$ROOT/scripts/list-qualified-thms.sh" "$file")
  [[ ${#thms[@]} -eq 0 ]] && { echo "FAIL|no auditable theorem"; return; }
  run_audit "$file" "${thms[@]}"
  [[ -n "$AUDIT_FAIL" ]] && { echo "FAIL|$AUDIT_FAIL"; return; }
  # Deprecation gate: the from-scratch elaboration already surfaced any `… has been deprecated`
  # warnings in its output. Advisory by default (a solve is still a PASS); set VERIFY_STRICT=1 (e.g. CI)
  # to fail a module that carries any. Deprecation ≠ soundness, so it never overrides the gates above.
  local dep; dep="$(printf '%s' "$AUDIT_OUT" | grep -ciE 'deprecated')"
  if (( dep > 0 )); then
    [[ -n "${VERIFY_STRICT:-}" ]] && { echo "FAIL|$dep deprecation(s) [VERIFY_STRICT]"; return; }
    echo "PASS|dep=$dep"; return
  fi
  echo "PASS|"
}
export -f audit_module run_audit last_lines
export ROOT TRUSTED_AXIOMS VERIFY_STRICT

# names_of <file> → fully-qualified names of top-level theorem/lemma/def/abbrev/(named-)instance,
# comment-aware (skips /- … -/ and `--`), namespace-qualified. Broader than list-qualified-thms.sh
# (which is theorem/lemma only) because the Certify library has defs + instances (Graph.lean has NO
# `theorem`). Anonymous `instance : …` are skipped (no name → the whole-file elab still catches a
# `sorry` in them). Assumes a single top-level `namespace`, as the Certify modules use.
names_of() {
  awk -f /dev/stdin "$1" <<'AWK'
    function occ(s,t,  n,i,p){n=0;i=1;while((p=index(substr(s,i),t))>0){n++;i+=p+length(t)-1}return n}
    { c0=(cd==0); cd+=occ($0,"/-")-occ($0,"-/"); if(cd<0)cd=0
      if(!c0) next
      if($0 ~ /^[[:space:]]*--/) next
      if($0 ~ /^namespace[[:space:]]+/){ns=$2; next}
      if($0 ~ /^end[[:space:]]+[A-Za-z_]/){next}
      if($0 ~ /^(theorem|lemma|def|abbrev|instance)[[:space:]]+[A-Za-z0-9_]/){
        nm=""
        for(i=1;i<=NF;i++) if($i ~ /^(theorem|lemma|def|abbrev|instance)$/){nm=$(i+1); break}
        sub(/[^A-Za-z0-9_].*/,"",nm)
        if(nm!="" && ns!="") print ns "." nm
      } }
AWK
}

# certify_guard <file> → "STATUS|note" for a MathProof/Certify library module (the moat). ONE
# from-scratch elaboration (catches build errors + any `sorry` in ANY decl, incl. anonymous
# instances) + a `#print axioms` trusted-trio check on every NAMED decl + the sweep over every
# constant the file declares (so a non-trio axiom such as native_decide's is caught, named decl or
# not). `sorry` alone is only a warning under `lake build`, so the whole tree building is NOT
# enough to protect the moat — this is.
certify_guard() {
  local file="$1"; local -a names=()
  mapfile -t names < <(names_of "$file")
  run_audit "$file" "${names[@]}"
  if [[ -n "$AUDIT_FAIL" ]]; then echo "FAIL|$AUDIT_FAIL"; else echo "PASS|"; fi
}

# Resolve target files (explicit module list, or all challenges).
shopt -s nullglob
declare -a files=() cand=()
if (( ${#MODARGS[@]} )); then
  # A requested module that cannot be resolved stops the run: silently verifying fewer modules
  # than asked would read as a pass.
  bad=0
  for m in "${MODARGS[@]}"; do
    m="${m##*/}"; m="${m%.lean}"; cand=()
    if [[ -f "$CH/$m.lean" ]]; then cand=("$CH/$m.lean")
    elif [[ "$m" =~ ^C[0-9][0-9][0-9][0-9]$ ]]; then cand=("$CH/$m"*.lean)   # C#### → its module
    fi
    case ${#cand[@]} in
      1) [[ " ${files[*]} " == *" ${cand[0]} "* ]] || files+=("${cand[0]}") ;;
      0) echo "verify-all.sh: not a challenge module: $m (no such file under MathProof/Challenges/)" >&2; bad=1 ;;
      *) echo "verify-all.sh: ambiguous module: $m matches ${cand[*]##*/}" >&2; bad=1 ;;
    esac
  done
  (( bad )) && exit 2
else
  files=("$CH"/C[0-9][0-9][0-9][0-9]*.lean)
fi
(( ${#files[@]} )) || { echo "no challenge modules to verify"; exit 2; }

# Pre-flight, BEFORE any `lake` call: with no built Mathlib, `lake env lean` would clone every
# dependency (gigabytes) and then fail each module with an error that does not say why.
[[ -f "$ROOT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]] || {
  echo "Mathlib is not built in this checkout — run ./setup.sh (or: lake exe cache get && lake build) first." >&2
  exit 2; }

# Bounded parallelism: concurrent `lean` processes each load Mathlib, so cap to avoid OOM.
JOBS="${VERIFY_JOBS:-}"
[[ -z "$JOBS" ]] && { n="$(nproc 2>/dev/null || echo 4)"; JOBS=$(( n > 6 ? 6 : n )); }
echo "── verify-all: ${#files[@]} module(s), ${JOBS}-way parallel ──"

results="$(printf '%s\n' "${files[@]}" | xargs -r -P "$JOBS" -I{} bash -c '
  f="$1"; mod="$(basename "$f" .lean)"
  printf "%s\t%s\n" "$mod" "$(audit_module "$f" "$mod")"
' _ {} | sort)"
xrc=$?   # pipefail: non-zero when the worker pool itself failed

# Walk the modules we STARTED, not the lines that came back: a module with no result line (its
# worker was killed, e.g. out of memory) is a failure, never a silent omission.
declare -A got=()
while IFS=$'\t' read -r mod res; do
  [[ -n "$mod" ]] && got["$mod"]="$res"
done <<< "$results"

pass=0; fail=0; dep_total=0; declare -a md_rows=()
while IFS= read -r mod; do
  res="${got[$mod]:-}"
  status="${res%%|*}"; note="${res#*|}"
  [[ "$status" == PASS || "$status" == FAIL ]] || { status=FAIL; note="no result: the audit worker died or its output was lost"; }
  if [[ "$status" == "PASS" ]]; then
    pass=$((pass+1))
    if [[ "$note" == dep=* ]]; then
      d="${note#dep=}"; dep_total=$((dep_total + d))
      printf "  \033[32m✔\033[0m %-30s SOLVED  \033[33m⚠ %s deprecated\033[0m\n" "$mod" "$d"
    else
      printf "  \033[32m✔\033[0m %-30s SOLVED\n" "$mod"
    fi
    md_rows+=("| \`$mod\` | ✅ SOLVED |")
  else
    fail=$((fail+1)); printf "  \033[31m✗\033[0m %-30s FAIL (%s)\n" "$mod" "$note"
    md_rows+=("| \`$mod\` | ⬜ $note |")
  fi
done < <(for f in "${files[@]}"; do basename "$f" .lean; done | sort)
if (( xrc != 0 )); then
  fail=$((fail+1)); printf "  \033[31m✗\033[0m %-30s FAIL (exit %d)\n" "worker pool (xargs)" "$xrc"
fi

# --- Certify library gate (the moat): full runs only (a filtered module run is a subset by design;
# the pre-commit hook runs a FULL verify-all when a non-challenge MathProof/ file is staged).
if (( ${#MODARGS[@]} == 0 )); then
  shopt -s nullglob
  declare -a cert_files=()
  [[ -f "$ROOT/MathProof/Certify.lean" ]] && cert_files+=("$ROOT/MathProof/Certify.lean")
  cert_files+=("$CERT"/*.lean)
  if (( ${#cert_files[@]} )); then
    echo "── Certify library (moat): ${#cert_files[@]} module(s) ──"
    for cf in "${cert_files[@]}"; do
      cname="Certify/$(basename "$cf" .lean)"
      [[ "$cf" == "$ROOT/MathProof/Certify.lean" ]] && cname="Certify (aggregator)"
      cres="$(certify_guard "$cf")"; cstat="${cres%%|*}"; cnote="${cres#*|}"
      [[ "$cstat" == PASS || "$cstat" == FAIL ]] || { cstat=FAIL; cnote="no result"; }
      if [[ "$cstat" == PASS ]]; then
        pass=$((pass+1)); printf "  \033[32m✔\033[0m %-30s CLEAN\n" "$cname"
        md_rows+=("| \`$cname\` | ✅ CLEAN |")
      else
        fail=$((fail+1)); printf "  \033[31m✗\033[0m %-30s FAIL (%s)\n" "$cname" "$cnote"
        md_rows+=("| \`$cname\` | ⬜ $cnote |")
      fi
    done
  fi
fi

echo "──────────────────────────────"
printf "  %d passed, %d failed\n" "$pass" "$fail"
if (( dep_total > 0 )); then
  hint=""; [[ -z "${VERIFY_STRICT:-}" ]] && hint=" (set VERIFY_STRICT=1 to fail on these)"
  printf "  \033[33m⚠ %d deprecation warning(s) across passing modules%s\033[0m\n" "$dep_total" "$hint"
fi

# README drift check (advisory) — only on a full run; a filtered run is a subset by design.
if (( ${#MODARGS[@]} == 0 )); then
  missing=()
  for f in "$CH"/C[0-9][0-9][0-9][0-9]*.lean; do
    mod="$(basename "$f" .lean)"; num="${mod:1:4}"
    grep -qE "^\| *$num " "$ROOT/README.md" 2>/dev/null || missing+=("$mod")
  done
  if ((${#missing[@]})); then
    printf "  \033[33m⚠ README SOLVED table missing %d row(s): %s\033[0m\n" "${#missing[@]}" "${missing[*]}"
    printf "    (add a row to README.md — the table is hand-curated; new-challenge.sh does not add it)\n"
  fi
fi

if $TABLE; then
  echo; echo "| Module | Status |"; echo "|--------|--------|"
  printf '%s\n' "${md_rows[@]}"
fi

[[ $fail -eq 0 ]]
