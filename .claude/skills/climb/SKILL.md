---
name: climb
description: "Autonomous climbing loop for lean-proof-agents: pick a batch of targets, verify anchors, scaffold, fan out a parallel lean-prover swarm with model-tier escalation, verify each with proof-auditor, log + regression-check, repeat at higher difficulty. The orchestrator's proof force-multiplier. Triggers: '/climb', 'keep climbing', 'prove a batch', 'run a proof swarm', 'harder proofs'."
model: inherit
color: gold
version: "1.2"
---

# climb — parallel prove → audit → log loop

The orchestrator superpower: proving becomes **width-limited, not depth-limited**. Verify anchors,
fan independent lemmas out to a `lean-prover` swarm, escalate the stuck ones up the model ladder,
verify with `proof-auditor`, bank the wins, climb.

> Requires the project subagents to be registered (Claude Code loads them at session start; see
> CLAUDE.md §Meta-system). Roster: `mathlib-scout` (Haiku, anchors), `lean-prover` (Sonnet, default),
> `lean-prover-opus` (Opus, escalation), `proof-auditor` (Sonnet, review), plus research scouts
> `blueprint-scout` / `conjecture-scout` (Haiku). If unregistered, prove directly via `/prove`.

## Model ladder (escalate only on failure — cost tracks difficulty)
`mathlib-scout` (Haiku, find anchors) → `lean-prover` (Sonnet, 2 attempts) →
`lean-prover-opus` (Opus, 3 attempts, decompose) → isolate a `sorry`-sub-lemma + surface to the
user — the orchestrating session itself takes the goal from there. Never skip upward without a
reason; never leave a silent `sorry`. **Lean is the sole arbiter at every tier.**

## The loop

0. **(optional) De-risk novel targets** — for a conjecture you're unsure is even *true*, dispatch
   `conjecture-scout` (Wolfram/OEIS) for a GO/NO-GO + closed form + suggested statement. Skip for
   well-known theorems.
1. **Pick a batch** (3–5 *independent* targets — no shared unproved lemma, so they parallelize).
   Source: the difficulty ladder below, `PROOF_PATTERNS.md`, or a blueprint leaf lemma (rung 6).
2. **Anchor pre-pass** ⭐ — dispatch `mathlib-scout` on the batch to confirm each target's anchor
   lemma (exact name + signature + module) BEFORE proving. This is the biggest throughput lever:
   a prover handed a verified anchor cites it in one line instead of burning its attempt cap on a
   blind search.
   Verify names yourself too — grep `.lake/packages/mathlib/Mathlib` when in doubt.
3. **Scaffold** each: `scripts/new-challenge.sh "<name>"` → one `sorry`-stub module + statement doc.
4. **Fan out** — in ONE message, dispatch a `lean-prover` per target (concurrent). Each prompt is a
   runbook: module, exact theorem statement, the **verified anchor** from step 2, verify command,
   2-attempt cap, "do not weaken the statement". Separate modules → no edit collisions.
5. **Collect + escalate.** For any BLOCKED target, don't blindly re-swarm the same goal — switch
   it to the **depth loop** (see below): `proof-strategist` plans + inits a ledger, then
   `proof-trajectory-keeper` drives escalate/decompose/generalize decisions up the ladder so the
   next move is *structurally different*, not the same tactic one tier higher. Finish or re-route;
   **never mark SOLVED on an agent's say-so** — read the module yourself and run `verify-all`.
6. **Audit** — dispatch `proof-auditor` on the batch (statement fidelity + no-`sorry` + axioms;
   `check-proof.sh <mod> --all` audits every theorem). A passing build is necessary, not
   sufficient: a proof of the *wrong* statement is worthless.
7. **Bank** — `scripts/verify-all.sh --table` (must be N/N); update README + challenge `.md`
   statuses; record each recipe with `scripts/log-pattern.sh "<goal shape>" "<recipe>" "<C####>"`
   (the self-populating flywheel); commit.
8. **Climb** — next batch, one rung harder. For rung 6, dispatch `blueprint-scout` first to pick an
   unclaimed leaf lemma from an active project.

## Depth control — when width isn't enough

`/climb` is width-first (many independent targets). Two cases need **depth** instead — the
project-management loop from `docs/PROOF_METHODOLOGY.md` Part E, driven by `proof-strategist`
(plan + ledger) and `proof-trajectory-keeper` (budget / stall / decisions). See `/prove`
§"When it's hard" for the step-by-step.

- **A hard target up front** (rung 5+, a blueprint leaf, a from-scratch multi-lemma proof): route
  it straight to the depth loop instead of the swarm — plan → decompose → attack leaves against a
  budgeted ledger → escalate/generalize/specialize on stall.
- **A target the swarm returns BLOCKED**: hand it to the depth loop so the ledger remembers what
  failed (dead-ends) and the keeper picks a *different* move, not the same tactic at a higher tier.

Easy/medium targets (rungs 1–4) stay on the fast width swarm — a ledger is overhead there. **Use
depth when a single proof needs *managing*, width when many proofs need *dispatching*.** The two
compose: a width batch can spawn a depth attempt for its one stubborn member without stalling the
rest.

## Difficulty ladder (rough)

1. cite a Mathlib lemma (√2 irrational, infinitude of primes)
2. one induction + `ring` (Gauss sum, sum of odds/squares/cubes)
3. inequalities via `nlinarith`/`gcongr` (AM-GM, Bernoulli)
4. hypotheses + case analysis (√p irrational for prime p, divisibility); named theorems that are
   a one-line Mathlib citation (Fermat's Little, Wilson, Σ binomial = 2ⁿ)
5. multi-lemma proofs; strong induction; `Finset`/`Nat` API depth; genuine from-scratch induction
6. a **blueprint leaf lemma** from an active project → real recognition win (`blueprint-scout`)
7. formalize a statement from a paper/Erdős problem

## Discipline

- Batch only **independent** targets; a dependency chain is sequential, not a swarm.
- Cap the swarm width to what you can audit well (≈5). Bigger → run waves.
- Escalate up the model ladder only on BLOCKED — cheapest tier that works.
- Every SOLVED passes `proof-auditor` before the task closes.
- Log the pattern that worked (`log-pattern.sh`) — that is the flywheel.
