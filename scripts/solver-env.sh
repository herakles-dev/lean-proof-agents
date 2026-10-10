#!/usr/bin/env bash
# solver-env.sh — provision a sudo-free finite-computation SOLVER stack for the Tier-1 layer.
#
# Creates a repo-local Python venv (.venv-solvers/, gitignored) with SAT/SMT/CAS/graph solvers,
# and builds the two source-only tools (kissat, nauty `geng`). No sudo, no apt.
# NOTE: the #647 sweep needs only numpy; this stack is for #64's SAT/SMT search, so the install
# is optional and deferred until then — nothing here runs until you call `install`.
#
# `install` DOWNLOADS, BUILDS and WRITES (it prints this plan again before starting):
#   * PyPI wheels (UNPINNED, latest) into <repo>/.venv-solvers/   (pip, or uv if present)
#   * kissat: `git clone --depth 1 https://github.com/arminbiere/kissat` (default-branch HEAD,
#     NOT pinned to a tag/commit) into $SOLVER_SRC/kissat (default ~/src), then ./configure && make
#     (runs that repo's build scripts), installed as $SOLVER_BIN/kissat (default ~/.local/bin)
#   * nauty `geng`: tarball nauty2_8_9 from https://pallini.di.uniroma1.it (version-pinned, no
#     checksum) into $SOLVER_SRC, built, installed as $SOLVER_BIN/geng
# So it writes OUTSIDE the repo (~/src, ~/.local/bin) unless you override SOLVER_SRC / SOLVER_BIN.
# Review the sources if that matters to you. Requires: bash, python3, git, curl, tar, make + a C compiler.
#
#   scripts/solver-env.sh install     # create venv + install wheels + build kissat/geng (idempotent)
#   scripts/solver-env.sh --check     # print versions of everything (pre-flight for solve.sh)
#   scripts/solver-env.sh where       # print venv path + solver bin locations
#
# Wheels (no sudo): z3-solver, python-sat (bundles CaDiCaL/Glucose/MiniSat/Lingeling), cvc5,
# python-flint (FLINT number-theory CAS), pynauty (canonical forms), + numpy numba networkx sympy.
# Source builds: kissat (github.com/arminbiere/kissat) and nauty `geng` → ~/.local/bin.
# Sage/PARI/GAP need a system package manager → not provided; python-flint + sympy are the CAS.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

VENV="$ROOT/.venv-solvers"
PY="$VENV/bin/python"
WHEELS=(z3-solver python-sat cvc5 python-flint pynauty numpy numba networkx sympy)
BIN="${SOLVER_BIN:-$HOME/.local/bin}"
SRC="${SOLVER_SRC:-$HOME/src}"
NAUTY_VER="nauty2_8_9"

case "${1:-}" in
  ""|-h|--help) awk 'NR==1{next} /^#/{sub(/^# ?/,"");print;next} /^[[:space:]]*$/{next} {exit}' "$0"; exit 0 ;;
esac
cmd="$1"; shift || true

have() { command -v "$1" >/dev/null 2>&1; }
_uv()  { command -v uv >/dev/null 2>&1 && { echo uv; return; }; [[ -x "$HOME/.local/bin/uv" ]] && echo "$HOME/.local/bin/uv"; }

make_venv() {
  [[ -x "$PY" ]] && { echo "→ venv exists: $VENV" >&2; return; }
  local uv; uv="$(_uv)"
  if [[ -n "$uv" ]]; then
    echo "→ creating venv via uv" >&2
    "$uv" venv "$VENV" --python "$(command -v python3)"
  else
    echo "→ creating venv via python3 -m venv (uv not found)" >&2
    python3 -m venv "$VENV"
  fi
}

install_wheels() {
  local uv; uv="$(_uv)"
  if [[ -n "$uv" ]]; then
    "$uv" pip install --python "$PY" "${WHEELS[@]}"
  else
    "$PY" -m pip install --upgrade pip
    "$PY" -m pip install "${WHEELS[@]}"
  fi
}

build_kissat() {
  { have kissat || [[ -x "$BIN/kissat" ]]; } && { echo "→ kissat present" >&2; return; }
  mkdir -p "$SRC" "$BIN"
  echo "→ building kissat from source" >&2
  [[ -d "$SRC/kissat" ]] || git clone --depth 1 https://github.com/arminbiere/kissat "$SRC/kissat"
  ( cd "$SRC/kissat" && ./configure && make -j"$(nproc)" )
  install -m755 "$SRC/kissat/build/kissat" "$BIN/kissat"
}

build_geng() {
  { have geng || [[ -x "$BIN/geng" ]]; } && { echo "→ nauty geng present" >&2; return; }
  mkdir -p "$SRC" "$BIN"
  echo "→ building nauty geng from source" >&2
  if [[ ! -d "$SRC/$NAUTY_VER" ]]; then
    curl -fsSL "https://pallini.di.uniroma1.it/${NAUTY_VER}.tar.gz" -o "$SRC/${NAUTY_VER}.tar.gz"
    tar -xzf "$SRC/${NAUTY_VER}.tar.gz" -C "$SRC"
  fi
  ( cd "$SRC/$NAUTY_VER" && ./configure && make geng )
  install -m755 "$SRC/$NAUTY_VER/geng" "$BIN/geng"
}

case "$cmd" in
  install)
    {
      echo "solver-env install will:"
      echo "  - pip-install UNPINNED wheels (${WHEELS[*]}) into $VENV"
      echo "  - git clone https://github.com/arminbiere/kissat (HEAD, unpinned) into $SRC/kissat, build it, install $BIN/kissat"
      echo "  - download https://pallini.di.uniroma1.it/${NAUTY_VER}.tar.gz (no checksum) into $SRC, build geng, install $BIN/geng"
      echo "  (skips kissat/geng if already on PATH or in $BIN; override dirs with SOLVER_SRC / SOLVER_BIN)"
    } >&2
    make_venv; install_wheels; build_kissat; build_geng
    echo "✅ solver stack ready — verify with: scripts/solver-env.sh --check" >&2
    ;;
  --check|check)
    [[ -x "$PY" ]] || { echo "❌ venv not installed — run: scripts/solver-env.sh install" >&2; exit 1; }
    "$PY" - <<'PYEOF'
import importlib
for m in ["z3","pysat","cvc5","flint","pynauty","numpy","numba","networkx","sympy"]:
    try:
        mod = importlib.import_module(m)
        v = getattr(mod, "__version__", None) or (mod.get_version_string() if hasattr(mod, "get_version_string") else "?")
        print(f"{m:10s} {v}")
    except Exception as e:
        print(f"{m:10s} MISSING ({e.__class__.__name__})")
PYEOF
    for b in kissat geng; do
      if have "$b" || [[ -x "$BIN/$b" ]]; then echo "$b       OK"; else echo "$b       MISSING (source build)"; fi
    done
    ;;
  where)
    echo "venv:   $VENV"
    echo "python: $PY"
    echo "solver bins: $BIN (kissat, geng)"
    echo "nauty src:   $SRC/$NAUTY_VER"
    ;;
  *) echo "unknown subcommand: $cmd (see --help)" >&2; exit 1 ;;
esac
