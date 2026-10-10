# lean-proof-agents — project instructions

Lean 4 + Mathlib monorepo for **math proof challenges**, with Claude Code subagents, skills and
scripts built around it. See [`README.md`](README.md) for the overview.

## The one rule

**Lean is the only source of proof truth.** A challenge is SOLVED *only* when its module
compiles with no `sorry` and clean axioms (`scripts/check-proof.sh`). **Wolfram Alpha is a
scratchpad** for exploring conjectures — never evidence of a proof.

## Environment

- Fresh clone: run `./setup.sh` first (installs the toolchain and fetches the prebuilt Mathlib cache).
- Lean/Lake via `elan`: `source "$HOME/.elan/env"` before `lake`/`lean` if not on PATH.
- Mathlib is pinned to the exact Lean version → `lake build` uses the **prebuilt cache** (fast).
  Never trigger a full Mathlib source build; if the cache misses, align `lean-toolchain` to
  Mathlib's and run `lake exe cache get`.

## Workflow

```bash
lake build                                   # build all (cache-backed)
scripts/new-challenge.sh "Putnam 1988 B2"    # scaffold a challenge (adds import automatically)
lake build MathProof.Challenges.C####Slug    # iterate on one proof
scripts/check-proof.sh C####Slug [thmName]   # completeness gate: fails on any sorry
scripts/wolfram.sh "simplify sin(x)^2 + cos(x)^2"   # exploration oracle (atomic queries only)
```

## Conventions

- One challenge = one module `MathProof/Challenges/C####Slug.lean` + one statement doc
  `challenges/####-slug.md`. Add via the script, not by hand (it keeps numbering + imports in sync).
- `MathProof/Basic.lean` imports all of Mathlib and holds shared helpers; every challenge imports it.
- `Template.lean` is never imported by the aggregator — it's the copy source.
- Secrets (incl. `WOLFRAM_LLM_APP_ID`) come from the environment or a `.env` file at the repo root (see `.env.example`). Never hardcode or commit them.

## Meta-system — skills, subagents, automation

Domain-mastery tooling, all in-repo and version-controlled.

### Scripts (`scripts/`)
| Script | Does |
|---|---|
| `new-challenge.sh "<name>"` | scaffold a challenge module + statement doc + wired import |
| `mathlib-search.sh "<q>"` | find Mathlib lemmas by NAME — loogle→(opt-in semantic)→local grep; flags any-position: `--type`, `--local`, `--nl` |
| `lean-suggest.sh "<binders> : <goal>"` | find lemmas by GOAL — runs Lean's `exact?`/`apply?`/`hint`/`simp?` |
| `check-proof.sh <mod> [thm\|--all]` | completeness gate: fail on any `sorry`; audits `#print axioms` for every declaration by default (or just `[thm]`; `--all` is explicit) |
| `verify-all.sh [--table] [mod…]` | regression gate (parallel; optional module filter); `--table` prints a 2-col status table (the 4-col README table is hand-curated) |
| `list-qualified-thms.sh <file>` | list fully-qualified theorem names in a module (namespace-aware); feeds the axiom audits |
| `log-pattern.sh "<goal>" "<recipe>" [C####]` | append a recipe row to `PROOF_PATTERNS.md` (deduped) — the flywheel |
| `lean-eval.sh "<expr>" [--decide]` | offline numeric oracle — Lean's own `#eval`/`decide`, no network (reliable vs. blocked OEIS) |
| `lean-goals.sh <mod> [--count\|--json]` | objective open-goal + sorry counter → the ledger's `goal_delta` (measure before/after an attempt; negative = progress) |
| `blueprint-leaves.sh [url\|--file] [--colors]` | list proof-ready leaf lemmas from a Lean blueprint dep-graph → recognition-win targets (feeds `blueprint-scout`) |
| `zulip.sh {me\|streams\|search\|messages\|claimed}` | read-only Lean Zulip client for claim-status recon (creds from the environment or `.env`) |
| `bank.sh {init\|add\|blackboard\|list\|verify\|race\|assemble\|clean} <Attempt> …` | shared lemma bank for parallel leaf proving (`/swarm`): publish proven leaves, race candidates, assemble into one challenge module (`docs/SWARM_SPEC.md`) |
| `install-hooks.sh` | install the pre-commit regression gate (runs `verify-all.sh` on staged challenge modules) |
| `wolfram.sh "<atomic query>"` | Wolfram Alpha oracle (scratchpad only) |
| `putnam-fetch.sh {list\|get\|year\|sample\|cached\|where}` | fetch + cache PutnamBench Lean statements (trishullab, Apache-2.0) into gitignored `.putnam-cache/`; pins one upstream commit → a corpus of no-Archive competition targets |
| `putnam-harness.sh {filter\|attemptable\|nonportable\|show\|attempt\|score}` | compile-filter cached statements against OUR toolchain (upstream pins v4.27, we run v4.33; `autoImplicit false` faithful, exit-code verdict) → attemptable set; + a solve-rate ledger |
| `proof-ledger.sh {init\|add\|attempt\|mark\|dead-end\|decision\|stall-check\|status}` | subgoal ledger for a DEPTH attempt: budget + goal_delta progress + stall/thrash detection (`docs/PROOF_METHODOLOGY.md` Part E) |
| `lit-search.sh "<q>" [--erdos N]` | literature pre-pass — arXiv/OpenAlex/zbMATH/Crossref/MathOverflow + the erdos DB row → OPEN-CONFIRMED\|LIKELY-SOLVED\|UNCERTAIN; feeds `docs/LIT_LOG.md` |
| `erdos-fetch.sh {where\|cached\|list\|get\|cat-a}` | pinned snapshot of `teorth/erdosproblems`; `cat-a` lists its unformalized finite-computation problems (falsifiable/decidable/verifiable) and flags which have a formal-conjectures Lean statement |
| `solver-env.sh {install\|--check\|where}` | sudo-free `.venv-solvers` SAT/SMT/CAS/graph stack (z3/pysat/cvc5/flint/pynauty; kissat+geng from source). Not installed by default; `sat`/`smt`/`cas`/`graphs` need it |
| `solve.sh {sweep\|sat\|smt\|cas\|graphs\|where\|list}` | finite-computation search harness → uniform `.search/<id>/witness.json`; `sweep` MVP (numpy, no venv) live, other modes need solver-env |
| `witness-to-lean.sh --shape … --witness …` | witness→Lean **certificate** generator: a solver witness → a `decide +kernel` module bridged by a `MathProof.Certify` lemma (the moat). Implements only the `forall-bounded-nat` shape (#647); see its header |

### Skills (`.claude/skills/`)
- **`/prove`** — the proving loop (scaffold → search → draft → build → certify → iterate), a tactic
  cheat-sheet, and the Lean-is-truth discipline. Load it when tackling any theorem.
- **`/climb`** — autonomous batch loop: pick targets → parallel `lean-prover` swarm → `proof-auditor`
  → log + `verify-all` → repeat one rung harder. The orchestrator's proof force-multiplier (WIDTH).
- **`/swarm`** — shared-blackboard parallel proving of the *independent leaves of ONE proof*:
  `proof-strategist` DAG → `bank.sh init` → a `lean-prover` per leaf → `bank.sh assemble` → check-proof +
  `proof-auditor` + `verify-all` gate (manual loop; best-of-N race for a crux). Phase ③ automates it as
  the `swarm-prove` Workflow, `.claude/workflows/swarm-prove.js`, which needs a Claude Code build with
  the `Workflow` tool; otherwise use the manual loop. Spec: `docs/SWARM_SPEC.md`.
- **DEPTH control** — for a *hard/BLOCKED* proof, both skills now invoke the trajectory loop
  (`proof-strategist` plan + ledger → attack leaves → `proof-trajectory-keeper` budget/stall →
  decision). Methodology: `docs/PROOF_METHODOLOGY.md` (Part E). Width = many proofs dispatched;
  depth = one proof *managed*.

### Learning
- `PROOF_PATTERNS.md` — goal-shape → winning tactic/lemma; **append after every solve** (the flywheel).
- `docs/LEAN_PRIMER.md` — how Lean works, for newcomers.
- `docs/PROOF_METHODOLOGY.md` — how hard proofs get solved (evidence-cited) + the trajectory-management
  methodology (subgoal ledger, budget, stall/thrash detection, decision ladder). The DEPTH playbook.
- `MathProof/Certify.lean` + `MathProof/Certify/` — the finite-computation solver layer's witness→Lean
  certificate lemmas (the *moat*), driven by `solve.sh` / `witness-to-lean.sh` and the research scouts.
  `docs/LIT_LOG.md` — the literature pre-pass log.

### Subagents (`.claude/agents/`) — dispatched by the orchestrating session
| Agent | Role | Tier |
|---|---|---|
| `mathlib-scout` | read-only lemma finder → pinpoint report (anchor pre-pass) | Haiku · explore |
| `blueprint-scout` | read-only: unclaimed blueprint leaf lemmas → recognition wins | Haiku · explore |
| `conjecture-scout` | read-only: Wolfram/OEIS go/no-go + closed form before formalizing | Haiku · explore |
| `proof-strategist` | read-only PLAN: decompose a hard goal → leaf-first subgoal DAG + init ledger; truth-gate, WLOG, anchor pre-pass | Opus · plan |
| `proof-trajectory-keeper` | advisory MANAGE: reads ledger → budget + stall/thrash → ONE critic decision (escalate/decompose/generalize/…); orchestrator executes | Opus · manage |
| `lean-prover` | writes/repairs a proof; search-first, 2-attempt cap, self-verifies | Sonnet · edit |
| `proof-auditor` | adversarial: statement fidelity + no-`sorry` + axiom hygiene | Sonnet · review |
| `lean-prover-opus` | escalation prover: dispatched on BLOCKED; deeper search, decompose | Opus · escalate |
| `meta-scoper` | read-only: surveys meta-system → ROI-ranked upgrade slate | Fable · scope |
| `lit-scout` | read-only: "already solved in the literature?" gate (sibling of `conjecture-scout`) → OPEN-CONFIRMED/LIKELY-SOLVED | Haiku · explore |
| `problem-scout` | read-only: cat-(a) Erdős target board → ROI-ranked attemptable finite-computation shortlist | Haiku · explore |
| `search-reducer` | read-only/advisory: reduce a finite/decidable statement → a solver search spec + `Certify` certificate shape | Opus · plan |

> **Models:** the `model` fields in `.claude/agents/*.md` name the models the author used. If you lack
> access to a pinned model, substitute one of the same tier (Haiku-class for explore, Sonnet-class
> for edit/review, Opus-class for plan/escalate, the top tier for `meta-scoper`).

> **Model ladder (escalate only on failure):** `mathlib-scout` (Haiku) → `lean-prover` (Sonnet)
> → `lean-prover-opus` (Opus) → the orchestrating session itself takes the goal, isolating a
> `sorry`-sub-lemma. `meta-scoper` scopes *what to build next*. Cheapest tier that works; **Lean is the sole arbiter** at
> every tier. For a **hard/BLOCKED** target, `proof-strategist` (plan) + `proof-trajectory-keeper`
> (manage) sit *above* the ladder as the DEPTH-control layer (`docs/PROOF_METHODOLOGY.md` Part E);
> both are advisory, the orchestrator executes their decisions.

> **Activation timing:** Claude Code registers project agents at session start; an agent file added
> mid-session is dispatchable only from the next session. Until then, follow `/prove` directly.

### Routing
- Proof → `lean-prover` (Sonnet); on BLOCKED escalate the SAME goal to `lean-prover-opus` (Opus).
- Hard / BLOCKED proof that needs *decomposition* → the DEPTH loop: `proof-strategist` (plan +
  ledger) → attack leaves → `proof-trajectory-keeper` (budget/stall → one decision) → execute up
  the ladder. See `/prove` §"When it's hard" + `docs/PROOF_METHODOLOGY.md`.
- Lemma hunt / anchor pre-pass → `mathlib-scout` (Haiku, Explore). Recognition-win target hunt →
  `blueprint-scout`; conjecture go/no-go before formalizing → `conjecture-scout`.
- Literature gate before investing in an open/Erdős/competition target → `lit-scout`
  (OPEN-CONFIRMED / LIKELY-SOLVED / UNCERTAIN). Finite/decidable goal → `problem-scout` (pick an
  attemptable cat-(a) Erdős target) and `search-reducer` (statement → solver search spec + `Certify`
  certificate shape; only shapes present in `MathProof/Certify/`).
- Many independent leaves of ONE hard proof → `/swarm` (or its `swarm-prove` Workflow); many separate
  targets → `/climb`.
- A proof marked SOLVED → run `proof-auditor` before treating it as done (catches wrong/vacuous statements).
- Batch/regression → `verify-all.sh` at CLOSE and as a pre-commit gate.
- "What should we build next?" (meta-improvement scoping) → `meta-scoper`.
