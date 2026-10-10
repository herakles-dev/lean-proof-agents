#!/usr/bin/env bash
# list-qualified-thms.sh <file.lean> — print the FULLY-QUALIFIED name of every top-level
# `theorem`/`lemma` in a challenge module, one per line, tracking the `namespace` stack.
# list-qualified-thms.sh --sweep <tag> — print the Lean command for the axiom SWEEP (below).
#
# Why: the axiom audits (check-proof.sh, verify-all.sh) must hand `#print axioms` the real name
# of each declaration. A theorem inside a nested `namespace` (a helper lemma) is NOT
# `MathProof.Challenges.<mod>.<thm>` — guessing that flat name makes `lean` error and the gate
# report a FALSE "build error" (hit on C0023's ported Vieta-jumping infra lemma). This resolves
# each name against the actual enclosing namespaces instead.
#
# Comment-aware (skips `/- … -/` block comments/docstrings and `--` lines, so a theorem-shaped
# line inside prose is not mistaken for a declaration) and accepts, before `theorem`/`lemma` on
# the same line, a one-line doc comment, `@[…]` attributes and the modifiers
# `private`/`protected`/`nonrec`/`noncomputable`/`unsafe`. Assumes namespaces close with a *named*
# `end <Name>` (Lean requires it) and no named `section`s interleave — both hold for this repo's
# challenges.
#
# This list is SOURCE-TEXT matching, so it is only the per-theorem REPORT: a declaration written
# in a shape the pattern does not know (`theorem «odd name»`, an attribute holding a `]`, a
# macro-generated theorem, …) is simply not listed. What makes the audit complete is the sweep:
# `--sweep <tag>` prints a Lean command which, appended to a copy of the module, runs
# `Lean.collectAxioms` on EVERY constant the file declares (the environment's `constants.map₂` —
# theorems, defs, instances, auxiliary proofs; no text matching) and prints, tab-separated,
#   <tag> axiom <axiom> <first declaring constant that depends on it>     (one line per axiom)
#   <tag> swept <number of constants walked>                               (always, last)
# The caller decides what is trusted, and treats a missing `swept` line as a failure (so a module
# that stops elaboration early, e.g. with `#exit`, cannot skip it). <tag> should be unguessable.
# The command names everything from `_root_`, so a namespace the module leaves open cannot shadow
# `Lean.collectAxioms` by accident; a module that deliberately redefines `#eval` still can lie.
set -euo pipefail
if [[ "${1:-}" == --sweep ]]; then
  [[ "${2:-}" =~ ^[A-Za-z0-9_-]+$ ]] || { echo "usage: list-qualified-thms.sh --sweep <tag>" >&2; exit 2; }
  cat <<LEAN
#eval show _root_.Lean.Elab.Command.CommandElabM _root_.Unit from do
  let env ← _root_.Lean.MonadEnv.getEnv
  let mut n : _root_.Nat := 0
  let mut found : _root_.Array (_root_.Lean.Name × _root_.Lean.Name) := #[]
  for (c, _) in env.constants.map₂.toList do
    n := n + 1
    for a in (← _root_.Lean.collectAxioms c) do
      unless found.any (·.1 == a) do found := found.push (a, c)
  for (a, c) in found do _root_.IO.println s!"$2\taxiom\t{a}\t{c}"
  _root_.IO.println s!"$2\tswept\t{n}"
LEAN
  exit 0
fi
[[ -n "${1:-}" && -f "$1" ]] || { echo "usage: list-qualified-thms.sh <file.lean> | --sweep <tag>" >&2; exit 2; }

awk -f /dev/stdin "$1" <<'AWK'
  # count non-overlapping occurrences of literal `t` in `s`
  function occ(s, t,   n, i, p) { n = 0; i = 1
    while ((p = index(substr(s, i), t)) > 0) { n++; i += p + length(t) - 1 }
    return n }
  {
    code_at_start = (cdepth == 0)                 # were we in code (not a block comment) here?
    cdepth += occ($0, "/-") - occ($0, "-/")       # update block-comment depth for this line
    if (cdepth < 0) cdepth = 0
    line = $0
    if (!code_at_start) {                          # line began inside a block comment → only what
      if (cdepth > 0) next                         # follows its close can be a declaration
      line = substr(line, index(line, "-/") + 2)
    } else {
      if ($0 ~ /^[[:space:]]*--/) next               # line comment
      if ($0 ~ /^[[:space:]]*namespace[[:space:]]+/)     { ns[++d] = $2; next }
      if ($0 ~ /^[[:space:]]*end[[:space:]]+[A-Za-z_]/)  { if (d > 0) d--; next }
    }
    # strip what may precede the keyword on its line: one-line comments, attributes, modifiers
    do {
      before = line
      sub(/^[[:space:]]+/, "", line)
      if (substr(line, 1, 2) == "/-" && (p = index(line, "-/")) > 0) line = substr(line, p + 2)
      sub(/^@\[[^]]*\]/, "", line)
      sub(/^(private|protected|nonrec|noncomputable|unsafe)[[:space:]]+/, "", line)
    } while (line != before)
    if (line ~ /^(theorem|lemma)[[:space:]]+/) {
      split(line, w, /[[:space:]]+/); name = w[2]
      sub(/[^[:alnum:]_.'].*/, "", name)           # strip anything after the identifier
      path = ""
      for (i = 1; i <= d; i++) path = path ns[i] "."
      if (name != "") print path name
    }
  }
AWK
