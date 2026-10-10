# lean-proof-agents

A Lean 4 + Mathlib repository of machine-checked proofs, plus the tooling I built around
[Claude Code](https://claude.ai/code) to produce and audit them. Each challenge is one Lean
module under `MathProof/Challenges/` with a statement document under `challenges/`. The
challenges range from textbook identities to Putnam problems and a few Erdős-problem
formalizations.

**What you can verify.** A challenge counts as solved only when Lean's kernel accepts the module
with no `sorry` and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
`scripts/verify-all.sh` re-elaborates every challenge and fails otherwise; the same gate runs in CI
(`.github/workflows/lean_action_ci.yml`). Nothing else, including Wolfram Alpha output or a model's
say-so, is treated as evidence of a proof. Anyone may say they brushed their teeth; the kernel
checks whether the toothbrush is wet.

**Merged upstream.** Two pull requests from this work were merged into
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures):

| PR | Merged | What it is | From |
|----|--------|------------|------|
| [#5425](https://github.com/google-deepmind/formal-conjectures/pull/5425) | 2026-09-18 | The proof of `erdos_399.variants.cambie` (Erdős #399, Cambie's variant) | C0037 |
| [#5481](https://github.com/google-deepmind/formal-conjectures/pull/5481) | 2026-09-18 | A `formal_proof` link from `erdos_672.variants.euler` (Erdős #672, Euler's case) to the proof published at [erdos672-four-squares-lean](https://github.com/herakles-dev/erdos672-four-squares-lean) | C0040, C0041 |

The first is a proof that now lives upstream. The second is a link: the proof stays in its own
repository and upstream points at it.

If you only have a few minutes:

- Browse the [solved challenges](#solved-challenges) table, then open one module, for example
  `MathProof/Challenges/C0040Erdos672EulerFourTermAPProductNotSquare.lean` (a descent proof
  written from scratch) or `MathProof/Challenges/C0031Putnam1962A1.lean`.
- Read [How the tooling works](#how-the-tooling-works) for the engineering side.
- Read `PROOF_PATTERNS.md` for the log of goal shapes and the tactics that closed them.

---

## Prerequisites

Lean 4 via [`elan`](https://github.com/leanprover/elan). The pinned toolchain is in
`lean-toolchain` (currently `leanprover/lean4:v4.33.1`); `elan` installs it on first use. If you
do not have `elan`, follow the instructions at <https://github.com/leanprover/elan#installation>,
then:

```bash
source "$HOME/.elan/env"
```

Mathlib is pinned to the same Lean version, so builds download Mathlib's prebuilt cache instead
of compiling it from source. Do not trigger a full Mathlib source build.

The Lean package builds wherever Lean does. The shell scripts have only been run on Linux and use
GNU-only options (`mktemp --suffix`, `sed -i`, `nproc`, `stat -c`), so on macOS they need GNU
coreutils and GNU sed first on `PATH`, and on Windows they need WSL. Several also use `curl`, `jq`
or `python3`; `CONTRIBUTING.md` has a table of which script needs what.

---

## Quick start

```bash
git clone https://github.com/herakles-dev/lean-proof-agents.git
cd lean-proof-agents
./setup.sh                      # checks for elan, fetches the Mathlib cache, builds, creates .env
```

Or by hand:

```bash
lake exe cache get              # download prebuilt Mathlib
lake build                      # build everything
scripts/verify-all.sh           # confirm every challenge is sorry-free with clean axioms
```

### Add a challenge

```bash
scripts/new-challenge.sh "Putnam 1988 B2"
```

This creates `MathProof/Challenges/C####Putnam1988B2.lean` (from `Template.lean`), a
statement stub in `challenges/####-putnam-1988-b2.md`, and wires the import into
`MathProof.lean`. The new module starts unsolved (a `sorry` placeholder).

### Prove it

Edit the generated module: replace the placeholder statement with the real theorem, then
replace `sorry` with a proof. Build just that module while you iterate (`####` is the number
`new-challenge.sh` assigned and printed; on a fresh clone it is `0049`):

```bash
lake build MathProof.Challenges.C####Putnam1988B2
```

### Verify it is actually done

```bash
scripts/check-proof.sh C####Putnam1988B2                      # no sorry, and audit every declaration's axioms
scripts/check-proof.sh C####Putnam1988B2 challenge_statement  # or audit one theorem's axioms
```

`check-proof.sh` re-elaborates the file from scratch and **fails on any `sorry`**, however
sincere. It also fails on any axiom outside the standard three, checked for every constant the
file declares. Green means solved. The gate is built to catch honest mistakes: it runs inside
the module's own elaboration, so deliberately hostile Lean meta-code can still interfere with it.
The header of `scripts/check-proof.sh` lists the known cases, and a contribution containing such
code needs a human read. Then record the status in the challenge's `challenges/*.md` and add a row to the table
below.

### Explore with the Wolfram oracle (optional, exploration only)

Needs `WOLFRAM_LLM_APP_ID` in your environment or in a `.env` file (see `.env.example`).

```bash
scripts/wolfram.sh "simplify sin(x)^2 + cos(x)^2"     # -> 1
scripts/wolfram.sh --help                              # atomic-query patterns
```

Atomic computational queries only (concrete numbers or `simplify ...`); the engine rejects
narrative prose. Never treat a Wolfram result as a proof.

---

## How the tooling works

Most of the engineering in this repo is the system that produces and checks the proofs; the
proofs are how that system gets exercised. It is built from Claude Code subagents, skills and
shell scripts, all in the repo.
Where a Claude session is mentioned below, it is the orchestrating session that dispatches the
subagents and is the only thing that commits.

**A single proof attempt.** The `/prove` skill (`.claude/skills/prove/SKILL.md`) runs the loop:
scaffold, search for lemmas, draft, build, certify, iterate.

- Search: `scripts/mathlib-search.sh` finds Mathlib lemmas by name; `scripts/lean-suggest.sh` runs
  Lean's `exact?`/`apply?` against a goal; `scripts/lean-eval.sh` gives an offline numeric check.
  The read-only `mathlib-scout` agent wraps this.
- Draft and build: the `lean-prover` agent writes the proof, with a two-attempt cap per goal.
- Completeness gate: `scripts/check-proof.sh` fails on any `sorry` and audits `#print axioms`.
  The provers here are language models. They are not allowed to say `sorry`.
- Adversarial audit: the `proof-auditor` agent (read-only) checks that the statement actually
  captures the intended theorem (not vacuous, not weakened), then re-checks axioms.
- Regression: `scripts/verify-all.sh` over every challenge in CI, and the same gate on the staged
  modules as a pre-commit hook (`scripts/install-hooks.sh`).

**Model-tier escalation.** Start with the cheapest tier that can do the job and move up only on
failure: `mathlib-scout` (Haiku) for search, `lean-prover` (Sonnet) for proofs, then
`lean-prover-opus` (Opus) when the Sonnet prover reports it is blocked. Lean is the arbiter at every
tier. The agent definitions are in `.claude/agents/`, and the routing rules are in `CLAUDE.md`.
`challenges/0030-putnam-1990-b3.md` records one escalation that worked (C0030). `lean-prover` gets
two attempts and "never weakens a statement to pass". There is no third attempt; there is a second
prover, which gets up to three.

**Hard proofs: plan, ledger, stall detection.** For a proof that does not fall to a direct
attempt, `proof-strategist` decomposes the goal into a dependency graph of subgoals and opens a
ledger with `scripts/proof-ledger.sh`. The ledger records each attempt, the change in open goals
and `sorry` count (`scripts/lean-goals.sh` measures it), dead ends not to repeat, and a budget.
That change is scored as `goal_delta`, where negative is progress. A positive number means the
prover worked on the problem and now there is more of it.
`proof-ledger.sh stall-check` flags attempts that are not making progress, and
`proof-trajectory-keeper` turns that into one recommended decision (escalate, decompose, generalize,
abandon the subgoal, and so on). The keeper is advisory; the orchestrator executes. Its own
definition calls it "the *project manager* of a single hard proof attempt", and the decisions it can
hand down include `abandon-subgoal` and `abandon-target`. Mathematics held out against project
management longer than most fields. The method and its sources are written up in `docs/PROOF_METHODOLOGY.md` (Part E).

**Parallel leaf swarm.** When a plan has several independent leaves (subgoals that depend on
nothing still unproved), `/swarm`
(`.claude/skills/swarm/SKILL.md`) proves them in parallel. Each prover owns one file and publishes
a finished lemma through `scripts/bank.sh`, which maintains a shared importable "blackboard" that
later leaves can build on. `bank.sh race` runs several candidate proofs for one hard leaf and keeps
the first that passes the kernel gate; `bank.sh assemble` inlines the leaves into one challenge
module for the normal gates. `.claude/workflows/swarm-prove.js` automates the wave scheduling.
The design is in `docs/SWARM_SPEC.md`. C0046, C0047 and C0048 in the table below were built this
way. The spec's own rule is that the swarm "changes *coordination*, never *trust*": any number of
agents agreeing that a proof is correct carries exactly as much weight as one agent saying so,
which is none.

**Batch mode.** `/climb` (`.claude/skills/climb/SKILL.md`) picks a batch of targets, runs a parallel
prover swarm, audits each result, logs recipes to `PROOF_PATTERNS.md` and runs `verify-all.sh`.

**Solver witness to Lean certificate.** For statements that are finite computations (for example
"no counterexample below N"), `scripts/solve.sh` runs a search and writes a witness file (the concrete data the search
produced), and
`scripts/witness-to-lean.sh` turns it into a Lean module that the kernel checks with
`decide +kernel`. The bridge lemmas live in `MathProof/Certify.lean` and `MathProof/Certify/`
(`Sup`, `Graph`, `Finset`, `Reflect`). The rule there is no `native_decide` and no extra axioms, so
a solver result is only as trusted as the kernel proof that checks it. `Reflect` replaces a `Finset`
scan with a `Nat` checker and a soundness theorem: C0042's `Finset` scan certifies the Erdős #647
no-witness fact on `[25, 60)`, and C0044 uses `Reflect` to certify it on `[25, 3000)`. The
`search-reducer` agent proposes the search spec. Only the `sweep` mode of
`solve.sh` runs without the extra solver environment (`scripts/solver-env.sh`).

**Scouting.** Read-only agents check a target before any proof effort: `conjecture-scout`
(is it true, and what is the closed form?), `lit-scout` with `scripts/lit-search.sh` (is it already
solved in the literature? see `docs/LIT_LOG.md`), `problem-scout` with `scripts/erdos-fetch.sh`,
and `blueprint-scout` with `scripts/blueprint-leaves.sh`. `scripts/putnam-fetch.sh` and
`scripts/putnam-harness.sh` fetch PutnamBench statements and test which compile with this
toolchain.

The full script and agent inventory, with one-line descriptions, is in [`CLAUDE.md`](CLAUDE.md).
`docs/LEAN_PRIMER.md` is a short introduction to Lean for readers new to it.

---

## Using it without Claude Code

I have only run this system with Claude Code, so read this section as a map of what would carry
over to another agent framework or another model provider, not as a tested port.

**Carries over unchanged.** Everything that decides whether a proof counts is ordinary Lean and
shell: the Lean package, `scripts/check-proof.sh`, `scripts/verify-all.sh`, the pre-commit hook and
the CI workflow. None of the scripts calls a model. Anything that can run a shell command and read
an exit code can use the same gate, and so can a person working by hand.

**Carries over as text.** The twelve agent definitions in `.claude/agents/` are Markdown files: a
short YAML header (`name`, `description`, `tools`, `model` and a few display fields) followed by the
agent's instructions, which work as a system prompt anywhere. The tools they ask for are generic: a
shell and file reading and searching for all of them, file editing for the two provers, and web
access for the four scouts that look things up. The `model` field names Claude models, but what the
design depends on is the tiering: a cheap model for search, a mid-size one for writing proofs, a
strong one for escalation and planning. The three skills in `.claude/skills/` are Markdown
procedures and read the same way. `PROOF_PATTERNS.md` and `docs/PROOF_METHODOLOGY.md` do not depend
on any model.

**Needs rewriting.** `.claude/workflows/swarm-prove.js` is written against Claude Code's workflow
runtime (`agent()`, `parallel()`, `phase()`). The schedule it implements, one wave of independent
leaves at a time with a barrier between waves, is specified in `docs/SWARM_SPEC.md`. `CLAUDE.md`
and the `.claude/` layout are what Claude Code loads on its own; another tool needs the same
content handed to it in whatever form it reads instructions.

**The contract to keep.** Whatever runs the agents, three things hold the system together: one
orchestrator commits, agents share results through files (`scripts/bank.sh`,
`scripts/proof-ledger.sh`) instead of through each other's say-so, and nothing is called solved
until `scripts/check-proof.sh` passes. That last rule is what keeps any model's confidence, from any
vendor, out of the definition of "proved".

---

## Layout

```
lean-toolchain               pinned Lean version (matches Mathlib)
lakefile.toml                Lake package, requires Mathlib
MathProof.lean               root aggregator (imports Basic, Certify and all challenges)
MathProof/
  Basic.lean                 imports all of Mathlib + shared helpers
  Certify.lean, Certify/     witness -> Lean certificate bridge lemmas
  Challenges/
    Template.lean            copy-me starting point (statement + sorry)
    C0001Warmup.lean ...     one module per challenge
challenges/                  human-readable problem statements (one .md per challenge)
scripts/                     shell tooling (inventory in CLAUDE.md); predicates/ holds a Python predicate
.claude/
  agents/                    subagent definitions
  skills/                    prove, climb, swarm
  workflows/swarm-prove.js   wave-scheduled parallel proving workflow
docs/                        LEAN_PRIMER, PROOF_METHODOLOGY, SWARM_SPEC, LIT_LOG
PROOF_PATTERNS.md            goal shape -> tactic log, appended after each solve
.github/workflows/           CI (build + verify-all gate)
CLAUDE.md                    instructions file Claude Code loads in this repo
```

## Solved challenges

The table starts easy and gets harder. The first rows are warm-ups from when the tooling was
being built, and nine of them (0001, 0002, 0008 to 0011, 0013, 0014, 0025) are one-line appeals
to an existing Mathlib lemma. Row 0023 is a port and says so. Remarks about what Mathlib or
formal-conjectures did not yet contain ("Mathlib gap", "open upstream `sorry`") describe those
projects in September 2026, when these modules were written.

The rows keep the shorthand they were written in. Haiku, Sonnet, Opus and Fable are the Claude
model tiers the agents run on, and a row may say which tier closed the proof ("apex" is the
strongest one available; a "cold" solve had no lemma-search pre-pass). "Trusted trio" means the
three standard axioms. The "moat" is the witness-to-Lean certificate layer in `MathProof/Certify/`.
"Dogfood" means the tooling was being tested on that problem, and Phases ①, ② and ③ are the
stages of the swarm design in `docs/SWARM_SPEC.md`. "`proof-auditor` PASS" records that the
auditing agent reviewed the statement at the time. Those verdicts were not saved in the repo,
so read them as history; the kernel gate is the only evidence here.

Rows 0042 and 0044 are bounded partial results on Erdős problem #647, which carries a £25 prize.
Row 0042 ends "**NOT** the £25 prize". Most things are not the £25 prize; this one says so in bold.

| # | Challenge | Theorem | Status |
|---|-----------|---------|--------|
| 0001 | Warmup: √2 is irrational | `sqrt_two_irrational` | ✅ SOLVED |
| 0002 | Infinitude of primes (Euclid) | `euclid`, `infinitude_of_primes` | ✅ SOLVED |
| 0003 | Gauss's sum (by induction) | `gauss_sum` | ✅ SOLVED |
| 0004 | Sum of first n odds = n² | `sum_odds` | ✅ SOLVED |
| 0005 | Sum of first n squares | `sum_squares` | ✅ SOLVED |
| 0006 | AM–GM, squares form (`2ab ≤ a²+b²` over ℝ) | `two_mul_le_add_sq` | ✅ SOLVED |
| 0007 | Sum of first n cubes | `sum_cubes` | ✅ SOLVED |
| 0008 | Bernoulli's inequality | `bernoulli` | ✅ SOLVED |
| 0009 | √p irrational for prime p | `sqrt_prime_irrational` | ✅ SOLVED |
| 0010 | Product of consecutive naturals is even | `consecutive_product_even` | ✅ SOLVED |
| 0011 | Fermat's Little Theorem (`a^p = a` in `ZMod p`) | `fermat_little` | ✅ SOLVED |
| 0012 | Fibonacci partial sum (`∑ fib i + 1 = fib(n+1)`) | `fib_sum` | ✅ SOLVED |
| 0013 | Sum of binomial coefficients = 2ⁿ | `sum_choose` | ✅ SOLVED |
| 0014 | Wilson's theorem (`(p-1)! ≡ -1 mod p`) | `wilson` | ✅ SOLVED |
| 0015 | Sum of squares of Fibonacci (`∑ fib i² = fib n·fib(n+1)`) | `fib_sq_sum` | ✅ SOLVED |
| 0016 | Factorial telescoping (`(∑ i·i!)+1 = n!`) | `factorial_telescope` | ✅ SOLVED |
| 0017 | Telescoping reciprocals over ℚ (`∑ 1/((k+1)(k+2)) = n/(n+1)`) | `recip_telescope` | ✅ SOLVED |
| 0018 | Fibonacci sub-exponential (`fib n < 2ⁿ`) | `fib_lt_two_pow` | ✅ SOLVED |
| 0019 | Telescoping product over ℝ (`∏ (1 - 1/(k+2)²) = (n+2)/(2(n+1))`) | `telescoping_product` | ✅ SOLVED |
| 0020 | Nesbitt's inequality (`a/(b+c)+b/(a+c)+c/(a+b) ≥ 3/2`) | `nesbitt` | ✅ SOLVED |
| 0021 | Basel partial sums bounded (`∑ 1/k² < 2`, via strengthened IH) | `sum_inv_sq_lt_two` | ✅ SOLVED |
| 0022 | Pell orbit never hits (1,1) (`x²−2y²` invariant) | `orbit_ne` | ✅ SOLVED |
| 0023 | IMO 1988 Q6: `ab+1 ∣ a²+b²` ⇒ quotient is a perfect square (Vieta jumping). **A port, not an original proof:** statement and proof are from Mathlib's `Archive/Imo/Imo1988Q6.lean` (Johan Commelin), which cannot be imported as a library; used as a ceiling test for the hard-proof loop | `imo1988_q6` | ✅ SOLVED |
| 0024 | √2 + √3 is irrational (rationality-transfer decomposition) | `sqrt2_add_sqrt3_irrational` | ✅ SOLVED |
| 0025 | Euler's theorem `a^φ(n) ≡ 1 (mod n)` (unfolded `% n` form) | `euler` | ✅ SOLVED |
| 0026 | Putnam 1988 B2: `y≥0 ∧ y(y+1)≤(x+1)² ⇒ y(y-1)≤x²` (real inequality, hidden case split) | `putnam_1988_b2` | ✅ SOLVED |
| 0027 | Putnam 1971 A1: 9 lattice points in ℤ³ ⇒ some open segment has an interior lattice point (parity pigeonhole) | `putnam_1971_a1` | ✅ SOLVED |
| 0028 | Putnam 2004 B1: rational root of `P ∈ ℤ[X]` ⇒ each Horner partial sum `∑ cₙ₋ⱼ rⁱ⁺¹⁻ʲ` is an integer (clear denominators + reindex + coprimality) | `putnam_2004_b1` | ✅ SOLVED |
| 0029 | Putnam 1999 A6: division-defined recurrence `aₙ=(6aₙ₋₁²aₙ₋₃−8aₙ₋₁aₙ₋₂²)/(aₙ₋₂aₙ₋₃)` ⇒ `n ∣ aₙ` (hidden linear recurrence `bₙ=6bₙ₋₁−8bₙ₋₂` → closed form `∏2ᵏ(2ᵏ−1)`; per-prime order-of-2/Euler divisibility) | `putnam_1999_a6` | ✅ SOLVED |
| 0030 | Putnam 1990 B3: >50387 square-entry `2×2` ℕ-matrices ⇒ two distinct commute (encard pigeonhole via always-commuting cliques — diagonal + `aI+bE₁₂` pencils — no tight extremal count needed; **first validated Sonnet→Opus escalation**) | `putnam_1990_b3` | ✅ SOLVED |
| 0031 | Putnam 1962 A1: 5 points no-3-collinear ⇒ some 4 form a convex quadrilateral (Erdős–Szekeres "Happy Ending", the bound g(4) ≤ 5; extreme-point trichotomy + **finite Krein–Milman infra lemma C0036** + linear-functional sign-pigeonhole; from-scratch; no Mathlib Archive proof, and none found elsewhere at the time) | `putnam_1962_a1` | ✅ SOLVED |
| 0032 | Putnam 1969 B1: `24 ∣ n+1 ⇒ 24 ∣ σ(n)` (divisor-pairing involution `d↦n/d` in `ZMod 24`; `unit²=1` and `1≠-1` by `decide`; **cold Sonnet solve**) | `putnam_1969_b1` | ✅ SOLVED |
| 0033 | Putnam 1983 A1: count of positive integers dividing `10⁴⁰` or `20³⁰` `= 2301` (coprime prime-power divisor counts + inclusion–exclusion; ℤ↔ℕ via `natAbs` image; **cold Sonnet solve**) | `putnam_1983_a1` | ✅ SOLVED |
| 0034 | Putnam 1994 B1: positive integers within 250 of exactly 15 perfect squares `= [315,325]∪[332,350]` (`Nat.sqrt` sandwich → `Finset.Icc` → pin `k∈{8,9}` via `nlinarith`+`interval_cases`; **cold Sonnet solve**) | `putnam_1994_b1` | ✅ SOLVED |
| 0035 | Putnam 2001 A3: when `x⁴−(2m+4)x²+(m−2)²` factors over ℤ `⟺ m=k² ∨ 2k²=m` (degree-2 coeff extraction + infinite-descent lemmas over ℤ; **cold Sonnet solve**) | `putnam_2001_a3` | ✅ SOLVED |
| 0036 | Finite Krein–Milman in ℝ²: `convexHull` of a **finite** set = `convexHull` of its extreme points (drop the `closure` in `closure_convexHull_extremePoints` via `Set.Finite.isClosed_convexHull`) — infra lemma unblocking C0031 | `finite_convexHull_eq_convexHull_extremePoints` | ✅ SOLVED |
| 0037 | **Erdős #399** (Cambie's variant): `n! ≠ x⁴+y⁴` for coprime `x,y`, `xy>1` (mod-8: `z⁴%8 = z%2`, coprimality ⇒ not both even ⇒ sum `∈{1,2}` mod 8, but `8∣n!` for `n≥4`) — an open `sorry` in google-deepmind/formal-conjectures when this was written; the proof was merged upstream as [#5425](https://github.com/google-deepmind/formal-conjectures/pull/5425) | `erdos_399_cambie` | ✅ SOLVED |
| 0038 | **Erdős #493** (Schinzel): every sufficiently large integer `n = ∏aᵢ − ∑aᵢ` for some integers `aᵢ≥2` (constructive, `k=2`: `n=2(n+2)−(2+(n+2))`) — solved in the literature; an independent re-proof (upstream already links an external Lean proof) | `erdos_493` | ✅ SOLVED |
| 0039 | **Erdős #349** (side-lemma): every `k:ℕ` is a sum of distinct powers of two (binary expansion; one-line Mathlib match `Finset.sum_toFinset_bitIndices_two_pow`) | `exists_finsetSum_two_pow` | ✅ SOLVED |
| 0040 | **Erdős #672, Euler's case (`k=4`, `l=2`)**: the product of a 4-term AP of positive integers with coprime common difference is never a perfect square (`n(n+d)(n+2d)(n+3d) ≠ q²`). Full multi-agent descent: `d=1` sandwich + `d≥2` reduces (both parities) via concordant forms to **Fermat's "no four squares in AP" (1640)** — a genuine **Mathlib gap** (no four-squares-in-AP / `x⁴−y⁴=z²` / congruent-number theorem exists) closed **from scratch**: equal-area Pythagorean pair → Euler four-number factorisation → `(1,4)` concordant descent on `\|X\|·\|Y\|` via `PythagoreanTriple.coprime_classification'`; apex-Fable close | `ap4_prod_ne_sq` | ✅ SOLVED |
| 0041 | **Erdős #672 bridge**: proves `Erdos672With 4 2` — the exact `formal-conjectures` `erdos_672.variants.euler` statement (abstract `Set.IsAPOfLengthWith` AP over a `Finset ℕ`) — by unfolding the AP predicate to `{n,n+d,n+2d,n+3d}` and reducing to C0040's `ap4_prod_ne_sq`. Definitions replicated verbatim (same Mathlib pin) so the proof transfers into their repo; the target was an open upstream `sorry` when this was written, and upstream now links this proof ([#5481](https://github.com/google-deepmind/formal-conjectures/pull/5481)) | `erdos_672_variants_euler` | ✅ SOLVED |
| 0042 | **Erdős #647** (bounded partial): no `n∈[25,60)` has `max_{m<n}(m+τ(m))≤n+2` — the finite-computation solver layer's `decide+kernel` core bridged to the ⨆-form via `Certify.Sup.lt_ciSup_of_exists_range` (the witness→Lean moat). Honest partial (sweep no-witness ≤2·10⁶, min excess 1 at n=35), **NOT** the £25 prize; first end-to-end solver-layer dogfood | `no_witness_below_60` | ✅ SOLVED |
| 0043 | **Fermat's "no four squares in AP" (1640)** — a standalone, minimal, upstream-portable extraction of C0040's descent kernel: four perfect squares can never form a *nonconstant* arithmetic progression. A genuine **Mathlib gap** (no four-squares-in-AP / `x⁴−y⁴=z²` / congruent-number theorem exists; only the parallel `not_fermat_42`, `a⁴+b⁴≠c²`, is present) → **Mathlib-PR candidate**. Byte-identical lift of the 17-decl transitive closure + a clean AP-form wrapper; proof-auditor PASS. The right-triangle form `x⁴−y⁴=z²` needs its own descent and is C0045 | `no_four_squares_in_ap`, `four_squares_not_in_ap` | ✅ SOLVED |
| 0044 | **Erdős #647, reflection-certified** (Certify **v2**): the `MathProof.Certify.Reflect` moat — a fast pure-`Nat` divisor count `tauS` proven `= σ 0` (`tauS_eq`) inside a structural Bool prefix-max sweep (`sweepS_sound`), run under `decide +kernel` with GMP `Nat` arithmetic instead of unfolding `Finset.divisors` — certifies the no-witness fact on **`[25, 3000)`**, **50× the v1 window** of C0042. `sweep_ok_3000` depends on **no axioms**; the bridge on the trusted trio. Honest partial (sweep found no witness ≤2·10⁶), **not** the £25 prize | `no_witness_below_3000` | ✅ SOLVED |
| 0045 | **Fermat's right-triangle theorem, quartic `−` form**: `x⁴ − y⁴ = z²` has only trivial solutions (nonzero `a,b` ⟹ `c=0`) — the `−` mirror of Mathlib's `not_fermat_42` (`a⁴+b⁴≠c²`) and a genuine **Mathlib gap**; completes the right-triangle family with C0043. Infinite descent (minimal counterexample on `a.natAbs` → `PythagoreanTriple.coprime_classification'` → two parity forks, `c`-odd via a four-way `Int.sq_of_gcd_eq_one` split → strictly smaller solution), a structural clone of `Fermat42.not_minimal`. Trusted-trio axioms | `fermat_sub_four`, `no_nontrivial_fermat_sub_four` | ✅ SOLVED |
| 0046 | **`30 ∣ n⁵ − n`** for all `n : ℤ` — the classic independent-leaf theorem (`30 = 2·3·5` pairwise coprime; `nᵖ ≡ n` mod each of 2,3,5). First **`/swarm` dogfood** (shared-blackboard, Phase ① end-to-end): 3 independent modular leaves (`2∣`, `3∣`, `5∣`, each `ZMod k` + `decide`) proven **in parallel** by three `lean-prover`s on a shared blackboard, combined by `IsCoprime.mul_dvd` (`Int.isCoprime_iff_gcd_eq_one` + `decide`) and kernel-gated. Surfaced & fixed two `bank.sh` bugs in-session (in-place `add` self-copy abort; `assemble` dependency-order). Trusted-trio axioms | `challenge_statement`, `dvd_two`, `dvd_three`, `dvd_five` | ✅ SOLVED |
| 0047 | **Erdős #97, the 3-equidistant variant**: a machine check of Danzer's counterexample, an explicit convex 9-gon in which every vertex has 3 other vertices equidistant from it. The construction is Danzer's, not a new result; the definitions and the witness are replicated from google-deepmind/formal-conjectures, where `erdos_97.variants.three_equidistant` was an open `sorry` at the time. Second **`/swarm` dogfood** and first **Phase ② best-of-N crux racing**: the hard `ConvexIndep` leaf (9 points in convex position, √3 coordinates) was won by an explicit per-vertex separating functional (`⟪uᵢ,·⟫` pure-rational since `√3·√3=3`, strict at each vertex via `convex_halfSpace_lt`+`convexHull_min`) racing 2 diverse strategies — first kernel-clean wins, losers cancelled; `Equidistant` via rational squared distances; assembled (topo-order) + proof-auditor PASS. Trusted-trio axioms | `erdos_97_variants_three_equidistant` | ✅ SOLVED |
| 0048 | **`210 ∣ n¹³ − n`** for all `n : ℤ` — the depth-3 sibling of C0046 (`210 = 2·3·5·7`; `n¹³ ≡ n` mod each prime since `(p−1) ∣ 12`). First **Workflow-driven `/swarm` (Phase ③)**: `proof-strategist` derived the 3-level DAG `{2,3,5,7} → {6,35} → 210` (7 leaves), `.claude/workflows/swarm-prove.js` wave-scheduled the parallel `lean-prover`s (automating the F3 async-keeper — deps land on the blackboard, next wave dispatches), integrator assembled + `check-proof`ed, orchestrator gated (`proof-auditor` PASS) + committed. Each prime leaf `ZMod p` + `decide`; combiners `IsCoprime.mul_dvd` with explicit Bézout witnesses. Trusted-trio axioms | `dvd210` (+ `dvd2/3/5/7`, `dvd6`, `dvd35`) | ✅ SOLVED |

Check for drift with `scripts/verify-all.sh` (it warns on any module missing a row); the 4-column
table above is hand-curated (`--table` prints only a 2-column status list). C0007–C0010, C0011–C0014, and
C0015–C0018 were each proved as one batch by parallel `lean-prover` agents and reviewed by
`proof-auditor` (the `/climb` loop in `.claude/skills/climb`). C0015–C0018 are multi-step
inductions.

## Using with Claude Code

`CLAUDE.md` gives Claude Code the context it needs in this repo: the workflow, the conventions, the
script and subagent inventory, and the routing rules. Open the repo in Claude Code and start with
`/prove` for a single theorem or `/climb` for a batch.

Claude Code registers agents when a session starts, so a new agent is dispatchable from the next
session, not the one that writes it. The session that writes it goes without, and the one after it
has staff.

```bash
claude    # Start Claude Code in this directory; it reads CLAUDE.md automatically
```

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Apache-2.0. See [LICENSE](LICENSE). Third-party material (theorem statements from PutnamBench
and Formal Conjectures, and the one module ported from Mathlib) is credited in
[NOTICE](NOTICE) and in each module's header.

## Author

D. Michael Piscitelli

---

*The toothbrush is wet. Anyone may check.*
