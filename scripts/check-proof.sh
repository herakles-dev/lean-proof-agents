#!/usr/bin/env bash
# check-proof.sh — proof-completeness gate for a challenge.
#
#   scripts/check-proof.sh C0001Warmup                          # bare name → Challenges/
#   scripts/check-proof.sh C0001                                # number alone → the module with that number
#   scripts/check-proof.sh MathProof.Challenges.C0001Warmup     # dotted module
#   scripts/check-proof.sh MathProof/Challenges/C0001Warmup.lean # path
#   scripts/check-proof.sh MathProof.Certify.Reflect --all      # any MathProof/ subdir (the moat)
#
# PASS (exit 0) only when the module compiles with NO `sorry` AND every audited declaration
# depends only on the trusted axioms (propext, Classical.choice, Quot.sound) — a proof using
# `native_decide` or a stray `axiom` is a soundness escape and FAILS here too, not just at commit.
# Uses `lake env lean` so the file is re-elaborated from scratch every run (a cached `lake build`
# would stay silent and hide a lingering warning); the axiom audit re-elaborates the SOURCE, never
# a cached .olean. Exit 2 = usage error, module not found, or Mathlib not built yet (run ./setup.sh).
#
# Axiom scope:  no 2nd arg → audit ALL declarations (default); `--all` → explicit all;
# `<theoremName>` → just that one theorem (the rest of the file is then NOT axiom-audited, only
# checked for `sorry`). A bare no-arg call never skips the axiom check.
# "ALL" is two layers in one elaboration: a `#print axioms` report per theorem/lemma that
# list-qualified-thms.sh finds in the source text, plus a SWEEP over every constant the file
# declares, taken from Lean's environment (list-qualified-thms.sh --sweep) — so a theorem cannot
# escape the audit by how its line is written (`@[simp] theorem`, a one-line doc comment, …), and
# a stray `axiom` FAILS even when nothing uses it.
#
# Limits: the audit runs inside the module's own elaboration and trusts it. It is a gate for
# honest mistakes, not for hostile input — a `sorry` in an `example` whose warning the file itself
# swallows (`#guard_msgs`) leaves no trace, a module that redefines `#eval` can forge the sweep's
# result, and `set_option debug.skipKernelTC` is not rejected. Review such constructs by eye.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
. "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"

arg="${1:-}"
[[ -z "$arg" ]] && { echo "usage: check-proof.sh <ChallengeModule | path> [theoremName | --all]" >&2; exit 2; }
thm="${2:-}"

# Normalize any accepted form to (source file, dotted module namespace). Supports both the
# Challenges/ layout and any other MathProof/ subdir (e.g. Certify/) so the moat is auditable too.
arg_noext="${arg%.lean}"
name="${arg_noext##*/}"; name="${name##*.}"   # short basename, for messages only
if [[ "$arg_noext" == *"/"* ]]; then          # path form:   MathProof/Sub/Mod(.lean)
  file="${arg_noext}.lean"; modpath="${arg_noext//\//.}"
elif [[ "$arg_noext" == *"."* ]]; then        # dotted form: MathProof.Sub.Mod
  modpath="$arg_noext"; file="${arg_noext//.//}.lean"
else                                           # bare name → default to Challenges/
  if [[ "$arg_noext" =~ ^C[0-9]{4}$ ]]; then  # number alone → the one module with that number
    shopt -s nullglob; cand=(MathProof/Challenges/"${arg_noext}"[!0-9]*.lean); shopt -u nullglob
    [[ ${#cand[@]} -eq 1 ]] && { arg_noext="$(basename "${cand[0]}" .lean)"; name="$arg_noext"; }
  fi
  modpath="MathProof.Challenges.${arg_noext}"; file="MathProof/Challenges/${arg_noext}.lean"
fi
[[ -f "$file" ]] || { echo "not found: $file" >&2; exit 2; }

# Pre-flight, BEFORE any `lake` call: with no built Mathlib, `lake env lean` would clone every
# dependency (gigabytes) and then fail with an error that does not say why.
[[ -f "$ROOT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]] || {
  echo "Mathlib is not built in this checkout — run ./setup.sh (or: lake exe cache get && lake build) first." >&2
  exit 2; }

echo "Checking $file ..."
if out="$(lake env lean "$file" 2>&1)"; then status=0; else status=$?; fi
[[ -n "$out" ]] && echo "$out"

if [[ $status -ne 0 ]]; then
  echo "❌ FAIL — $name does not compile (lean exit $status)"
  exit 1
fi
if echo "$out" | grep -qiE "declaration uses .?sorry|sorryAx"; then
  echo "❌ FAIL — $name is INCOMPLETE (uses sorry)"
  exit 1
fi

# The ONLY axioms a completed proof may depend on. Anything else (sorryAx, native_decide's
# compiler axiom, a stray `axiom`) is a soundness escape. Shared with verify-all.sh.
TRUSTED_AXIOMS='propext|Classical\.choice|Quot\.sound'

# audit_axioms <sweep|nosweep> <full-name...> — append `#print axioms` for each name (and, with
# `sweep`, the environment-level sweep command) to a COPY of the SOURCE (so we audit the code we
# just re-elaborated, NOT a cached .olean), elaborate once, and FAIL on any axiom outside the
# trusted trio, on a report that did not come back for every name, or on a sweep that did not run
# to its end. A trailing newline is forced first so the appended commands never glue onto a last
# source line lacking `\n`. Sets SWEPT to the number of constants the sweep walked.
SWEPT=""
audit_axioms() {
  local sweep="$1"; shift
  local tmp ax arc=0 viol t tag="" sw="" nrep
  tmp="$(mktemp --suffix=.lean)"; cat "$file" > "$tmp"; printf '\n' >> "$tmp"
  for t in "$@"; do echo "#print axioms $t" >> "$tmp"; done
  if [[ "$sweep" == sweep ]]; then
    tag="AXSWEEP-$(od -An -N8 -tx1 /dev/urandom | tr -d ' \n')"   # unguessable by the module
    "$ROOT/scripts/list-qualified-thms.sh" --sweep "$tag" >> "$tmp"
  fi
  ax="$(lake env lean "$tmp" 2>&1)" || arc=$?; rm -f "$tmp"
  if [[ -n "$tag" ]]; then
    sw="$(printf '%s\n' "$ax" | grep "^$tag"$'\t' || true)"
    ax="$(printf '%s\n' "$ax" | grep -v "^$tag"$'\t' || true)"
  fi
  [[ -n "$ax" ]] && echo "$ax"
  if [[ $arc -ne 0 ]]; then echo "❌ FAIL — axiom audit did not elaborate (lean exit $arc)"; return 1; fi
  nrep="$(printf '%s\n' "$ax" | grep -cE "' (depends on axioms:|does not depend on any axioms)" || true)"
  if (( nrep < $# )); then
    echo "❌ FAIL — axiom audit incomplete: $nrep report(s) for $# declaration(s)"; return 1
  fi
  viol="$(printf '%s' "$ax" | tr '\n' ' ' | grep -oE "depends on axioms: \[[^]]*\]" \
          | grep -oE "\[[^]]*\]" | tr -d '[]' | tr ',' '\n' | sed 's/^ *//; s/ *$//')"
  if [[ -n "$tag" ]]; then
    SWEPT="$(printf '%s\n' "$sw" | awk -F'\t' '$2 == "swept" { print $3 }')"
    if ! [[ "$SWEPT" =~ ^[0-9]+$ ]]; then
      echo "❌ FAIL — axiom sweep did not run to its end (elaboration stopped early, or the module interferes with the audit)"
      return 1
    fi
    echo "--- axiom sweep ($SWEPT constant(s) declared in $name) ---"
    printf '%s\n' "$sw" | awk -F'\t' '$2 == "axiom" { printf "%s  (first seen in %s)\n", $3, $4 }'
    viol+=$'\n'"$(printf '%s\n' "$sw" | awk -F'\t' '$2 == "axiom" { print $3 }')"
  fi
  viol="$(printf '%s\n' "$viol" | grep -vE '^$' | grep -vxE "$TRUSTED_AXIOMS" | sort -u | tr '\n' ' ' | sed 's/ *$//')"
  if [[ -n "$viol" ]]; then echo "❌ FAIL — unsafe axioms: $viol"; return 1; fi
  return 0
}

# Resolve targets. No 2nd arg → audit ALL (a bare call must not silently skip the axiom check).
declare -a targets=()
if [[ "$thm" == "--all" || -z "$thm" ]]; then
  mapfile -t targets < <("$ROOT/scripts/list-qualified-thms.sh" "$file")
  echo "--- #print axioms (${#targets[@]} decl) ---"
  audit_axioms sweep "${targets[@]}" || exit 1
  # The sweep reads Lean's environment, so 0 here means the file really declares nothing.
  [[ "$SWEPT" -eq 0 ]] && echo "⚠ no declaration to axiom-audit in $name (no-sorry check passed)"
else
  # A CLI theorem name is relative to the module namespace unless already fully qualified.
  case "$thm" in
    MathProof.*) targets=("$thm") ;;
    *)           targets=("${modpath}.${thm}") ;;
  esac
  echo "--- #print axioms (${#targets[@]} decl) ---"
  audit_axioms nosweep "${targets[@]}" || exit 1
fi

echo "✅ SOLVED — $name compiles with no sorry"
exit 0
