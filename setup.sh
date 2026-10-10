#!/usr/bin/env bash
set -euo pipefail

# lean-proof-agents - first-time setup for a fresh clone. Safe to re-run.
# Usage: ./setup.sh

cd "$(dirname "${BASH_SOURCE[0]}")"

echo "=== lean-proof-agents setup ==="

# Make elan visible if it is installed but not yet on PATH.
if ! command -v lake >/dev/null 2>&1 && [ -f "$HOME/.elan/env" ]; then
  # shellcheck disable=SC1091
  source "$HOME/.elan/env"
fi

if ! command -v lake >/dev/null 2>&1 || ! command -v elan >/dev/null 2>&1; then
  cat >&2 <<'MSG'
Error: elan / lake not found.

Install the Lean toolchain manager yourself, then re-run this script:
  https://github.com/leanprover/elan#installation
  (the usual command is: curl -sSf https://elan.lean-lang.org/elan-init.sh | sh)
  then: source "$HOME/.elan/env"

This script does not install anything for you.
MSG
  exit 1
fi

echo "Toolchain: $(cat lean-toolchain)"

# Environment file (never overwrite an existing one).
if [ ! -f .env ]; then
  if [ -f .env.example ]; then
    cp .env.example .env
    echo "Created .env from .env.example (only needed for scripts/wolfram.sh and scripts/zulip.sh)."
  fi
else
  echo ".env already exists, leaving it alone."
fi

# Prebuilt Mathlib cache. If this fails we stop: a build without the cache would compile
# Mathlib from source, which takes hours.
echo "Fetching prebuilt Mathlib cache..."
if ! lake exe cache get; then
  echo "Error: could not fetch the Mathlib cache. Not building, to avoid a Mathlib source build." >&2
  echo "Check your network, and that lean-toolchain matches the Mathlib version in lake-manifest.json." >&2
  exit 1
fi

echo "Building..."
lake build

echo ""
echo "=== Setup complete ==="
echo ""
echo "Next steps:"
echo "  1. Check every challenge:   scripts/verify-all.sh"
echo "  2. Add a challenge:         scripts/new-challenge.sh \"Putnam 1988 B2\""
echo "  3. Using Claude Code?       run 'claude' here; CLAUDE.md has the context."
