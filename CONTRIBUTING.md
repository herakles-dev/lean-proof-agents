# Contributing

Thanks for your interest. This repo has one rule that everything else follows from: a proof counts
only when Lean's kernel accepts it with no `sorry` and clean axioms.

## Setup

```bash
git clone https://github.com/herakles-dev/lean-proof-agents.git
cd lean-proof-agents
./setup.sh
```

This needs `elan` (Lean's toolchain manager). Mathlib comes from its prebuilt cache; do not build
Mathlib from source.

Building and checking proofs needs only `elan` (and `git`, which `lake` uses). Some helper scripts
need more, and fail with an ordinary command-not-found error if it is missing:

| Tool | Needed by |
|---|---|
| `curl` and network access | `wolfram.sh`, `mathlib-search.sh`, `lit-search.sh`, `erdos-fetch.sh`, `putnam-fetch.sh`, `blueprint-leaves.sh`, `zulip.sh`, `solver-env.sh`, and the prebuilt-cache download in `setup.sh` |
| `jq` | `proof-ledger.sh`, `mathlib-search.sh`, `zulip.sh` |
| `python3` | `lit-search.sh`, `erdos-fetch.sh`, `putnam-fetch.sh`, `blueprint-leaves.sh`, `solve.sh`, `witness-to-lean.sh`, `solver-env.sh` |
| `numpy` (`python3 -m pip install numpy`) | `solve.sh sweep` |

Optional credentials (`WOLFRAM_LLM_APP_ID`, Zulip settings) are listed in `.env.example`.

## Adding a challenge

```bash
scripts/new-challenge.sh "Putnam 1988 B2"
```

The script creates the module under `MathProof/Challenges/`, a statement doc under `challenges/`,
and the import in `MathProof.lean`. Use it rather than creating files by hand, since it keeps
numbering and imports consistent. Then:

1. Write the real statement in the module and the statement doc.
2. Prove it. Iterate with `lake build MathProof.Challenges.C####Slug`.
3. Add a row to the "Solved challenges" table in `README.md`.
4. Append any reusable recipe to `PROOF_PATTERNS.md` (`scripts/log-pattern.sh`).

## The bar for a merged proof

- The module builds: `lake build MathProof.Challenges.C####Slug`.
- No `sorry`, and axioms are clean: `scripts/check-proof.sh C####Slug` passes (with no theorem
  name it audits every declaration in the file). Only `propext`, `Classical.choice` and
  `Quot.sound` are allowed. No `native_decide`, no new `axiom`.
- No Lean meta-code that touches the audit itself (`#guard_msgs` around a `sorry`, redefining
  `#eval` or `#print`, `set_option debug.skipKernelTC`). The gate runs inside the module's own
  elaboration and is built for honest mistakes; the header of `scripts/check-proof.sh` lists what
  it cannot catch. A change containing such code is reviewed by hand.
- The statement is faithful to the intended theorem. Reviewers will check that it is not vacuous
  (for example, hypotheses that cannot hold) and not a weaker variant. State in the statement doc
  where the source of the problem is.
- `scripts/verify-all.sh` passes for the whole repo, not only your module.

## Do not

- Weaken or alter a statement to make it pass. If the statement is wrong, fix it openly and say so
  in the pull request.
- Treat Wolfram Alpha output (or any model output) as evidence of a proof. `scripts/wolfram.sh` is
  for exploring conjectures only.
- Commit secrets. Keys such as `WOLFRAM_LLM_APP_ID` go in your environment or an untracked `.env`
  (see `.env.example`).

## Pull requests

Keep a pull request to one challenge or one tooling change. Say which commands you ran. CI runs
`lake build` and `scripts/verify-all.sh`.

## Working with Claude Code

`CLAUDE.md` gives Claude Code the repo's workflow and conventions. The `/prove` skill runs the
proving loop, and the `proof-auditor` agent reviews a finished proof for statement fidelity. The
same bar applies to AI-assisted proofs: the kernel decides.

## Reporting issues

Use the issue templates in `.github/ISSUE_TEMPLATE/`. Include the toolchain version
(`cat lean-toolchain`), the module, the command you ran and the output.
