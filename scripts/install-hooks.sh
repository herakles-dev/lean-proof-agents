#!/usr/bin/env bash
# install-hooks.sh — install the lean-proof-agents pre-commit regression gate.
#
# CI (`.github/workflows/lean_action_ci.yml`) runs the full `scripts/verify-all.sh` gate (no
# sorry + clean axioms). This pre-commit hook runs the same gate LOCALLY but only on the staged
# challenge modules, so the common case is fast; a change to shared code (Basic.lean, lake config,
# toolchain) still triggers a full run. Doc-only commits skip it entirely.
#
#   scripts/install-hooks.sh          # install / refresh the hook
#   git commit --no-verify ...        # bypass in a pinch
#
# Uses the pre-commit hook point only. Resolves the hooks dir the way git does (worktrees,
# core.hooksPath) and REFUSES to overwrite a pre-commit hook it did not install (re-running over
# its own hook just refreshes it). Requires: git; the hook itself needs bash + the Lean toolchain.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
git -C "$ROOT" rev-parse --git-dir >/dev/null 2>&1 || { echo "not a git repo: $ROOT" >&2; exit 1; }
HOOK="$(git -C "$ROOT" rev-parse --git-path hooks/pre-commit)"
[[ "$HOOK" == /* ]] || HOOK="$ROOT/$HOOK"
MARKER="Installed by scripts/install-hooks.sh"
if [[ -e "$HOOK" ]] && ! grep -qF "$MARKER" "$HOOK"; then
  echo "refusing to overwrite an existing pre-commit hook that this script did not install:" >&2
  echo "  $HOOK" >&2
  echo "Move it aside (or call scripts/verify-all.sh from it yourself), then re-run." >&2
  exit 1
fi
mkdir -p "$(dirname "$HOOK")"

cat > "$HOOK" <<'HOOK_EOF'
#!/usr/bin/env bash
# lean-proof-agents pre-commit — regression gate on the STAGED challenge modules (no sorry, clean
# axioms, compiles). Installed by scripts/install-hooks.sh; bypass with: git commit --no-verify.
# Note: audits the WORKING-TREE content of the staged modules, so stage whole files (a partially
# staged file is checked as it sits on disk, not exactly as it will be committed).
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
staged="$(git diff --cached --name-only --diff-filter=ACM || true)"

# Nothing under MathProof/ changed → nothing to gate.
printf '%s\n' "$staged" | grep -qE '^MathProof/' || exit 0
# shellcheck disable=SC1091
source "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"

# A change to shared code affects every module → full run; else audit just the staged modules.
if printf '%s\n' "$staged" | grep -qE '^(MathProof/Basic\.lean|lakefile\.(toml|lean)|lean-toolchain|lake-manifest\.json)$'; then
  echo "[pre-commit] shared code staged → full verify-all…"
  set --
else
  mapfile -t mods < <(printf '%s\n' "$staged" | sed -n -E 's#^MathProof/Challenges/(C[0-9]{4}[^/]*)\.lean$#\1#p')
  if ((${#mods[@]} == 0)); then
    echo "[pre-commit] MathProof/ change staged but no challenge module → full verify-all…"
    set --
  else
    echo "[pre-commit] staged module(s): ${mods[*]} → verify-all (subset)…"
    set -- "${mods[@]}"
  fi
fi

log="$(mktemp)"
trap 'rm -f "$log"' EXIT
if ! "$ROOT/scripts/verify-all.sh" "$@" >"$log" 2>&1; then
  echo "[pre-commit] ❌ verify-all FAILED — a challenge has a sorry, a build error, or an unsafe axiom:"
  tail -20 "$log"
  echo "[pre-commit] fix it, or bypass with 'git commit --no-verify'."
  exit 1
fi
echo "[pre-commit] ✅ verify-all green."
HOOK_EOF

chmod +x "$HOOK"
echo "Installed pre-commit regression gate → $HOOK"
echo "  (audits only staged challenge modules; full run when shared code changes; bypass --no-verify)"
