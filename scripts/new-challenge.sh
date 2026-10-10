#!/usr/bin/env bash
# new-challenge.sh — scaffold a new lean-proof-agents challenge from Template.lean.
#
#   scripts/new-challenge.sh "Putnam 1988 B2"
#
# Creates:
#   MathProof/Challenges/C<NNNN><CamelSlug>.lean   (from Template.lean)
#   challenges/<NNNN>-<kebab-slug>.md              (statement stub)
# and wires `import MathProof.Challenges.C<NNNN><CamelSlug>` into MathProof.lean.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CH_DIR="$ROOT/MathProof/Challenges"
STMT_DIR="$ROOT/challenges"
TEMPLATE="$CH_DIR/Template.lean"
AGG="$ROOT/MathProof.lean"

raw="${*:-}"
if [[ -z "$raw" ]]; then
  echo "usage: new-challenge.sh \"<title / slug>\"" >&2
  exit 1
fi
[[ -f "$TEMPLATE" ]] || { echo "missing template: $TEMPLATE" >&2; exit 1; }

# Next challenge number (max existing C#### + 1).
max=0
shopt -s nullglob
for f in "$CH_DIR"/C[0-9][0-9][0-9][0-9]*.lean; do
  n=$(basename "$f" | sed -E 's/^C([0-9]{4}).*/\1/')
  n=$((10#$n))
  (( n > max )) && max=$n
done
shopt -u nullglob
num=$(printf "%04d" $((max + 1)))

# CamelCase module suffix (letters/digits only) and kebab-case doc slug.
camel=$(echo "$raw" | sed -E 's/[^a-zA-Z0-9]+/ /g' \
        | awk '{for(i=1;i<=NF;i++){$i=toupper(substr($i,1,1)) substr($i,2)}; print}' \
        | tr -d ' ')
kebab=$(echo "$raw" | tr '[:upper:]' '[:lower:]' | sed -E 's/[^a-z0-9]+/-/g; s/^-+//; s/-+$//')
[[ -z "$kebab" ]] && kebab="challenge"

mod="C${num}${camel}"
lean_file="$CH_DIR/${mod}.lean"
md_file="$STMT_DIR/${num}-${kebab}.md"
import_line="import MathProof.Challenges.${mod}"
close_marker="-- <<< challenges <<<"

[[ -e "$lean_file" ]] && { echo "already exists: $lean_file" >&2; exit 1; }

mkdir -p "$STMT_DIR"
sed "s/CTEMPLATE/${mod}/g" "$TEMPLATE" > "$lean_file"

cat > "$md_file" <<EOF
# Challenge ${num} — ${raw}

- **Module:** \`MathProof/Challenges/${mod}.lean\`
- **Theorem:** \`MathProof.Challenges.${mod}.challenge_statement\`
- **Status:** ⬜ UNSOLVED

## Problem

<state the problem here>

## Formal statement

\`\`\`lean
theorem challenge_statement : <prop>
\`\`\`

## Notes

Explore with the Wolfram oracle before formalizing (exploration only, not proof):
\`scripts/wolfram.sh "<atomic query>"\`
EOF

# Wire the import into the aggregator, just above the close marker.
if grep -qF "$import_line" "$AGG"; then
  :
else
  sed -i "s|^${close_marker}\$|${import_line}\n${close_marker}|" "$AGG"
fi

echo "Created challenge ${mod}:"
echo "  $lean_file"
echo "  $md_file"
echo "  + wired import into MathProof.lean"
echo
echo "Next:"
echo "  1. edit $lean_file — replace the statement + sorry"
echo "  2. lake build MathProof.Challenges.${mod}"
echo "  3. scripts/check-proof.sh ${mod}"
