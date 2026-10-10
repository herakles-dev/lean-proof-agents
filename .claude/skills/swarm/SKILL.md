---
name: swarm
description: "Shared-blackboard proof swarm for lean-proof-agents: attack the INDEPENDENT LEAVES of ONE hard proof in parallel/async. proof-strategist DAG → bank.sh init → a lean-prover per independent leaf (each owns its bank file) → later leaves import the growing blackboard to build on completed results → assemble into one self-contained challenge module → check-proof + proof-auditor + verify-all gate. The orchestrator stays the sole assembler + gate; Lean's kernel is the only arbiter. DEPTH-parallel sibling of /climb (which parallelizes many TARGETS). Triggers: '/swarm', 'swarm this proof', 'prove the leaves in parallel', 'parallel leaf proving', 'run a proof swarm on one theorem'."
model: inherit
color: teal
version: "1.0"
---

# swarm — shared-blackboard parallel-leaf proving (DEPTH, one proof)

Turn one hard proof's serial DEPTH loop into a **team**: multiple `lean-prover`s work its
**independent leaves at once**, each owning its own file (no edit contention), building on each
other's *completed* leaves through a live **shared blackboard** (an importable lemma bank). The
orchestrator alone assembles + kernel-gates. Spec: `docs/SWARM_SPEC.md`.

**`/swarm` vs `/climb`:** `/climb` is WIDTH — many *challenges* proven in parallel. `/swarm` is
DEPTH-parallel — the *leaves of ONE theorem* proven in parallel. Use `/swarm` when a
`proof-strategist` DAG has ≥2 independent leaves.

## The loop

1. **Plan.** Ensure a `proof-strategist` subgoal DAG + ledger exist (else dispatch it first).
   A leaf is *independent* when its `deps` are empty or already on the blackboard.
2. **Init the bank.** `scripts/bank.sh init <Attempt>` (CamelCase id, e.g. `C0046Foo`). Prints the
   blackboard import line.
3. **Fan out.** Dispatch a `lean-prover` on **every currently-independent leaf in ONE message**
   (parallel), each with the leaf-prover contract below. Escalate a BLOCKED leaf to `lean-prover-opus`.
4. **Collect + grow the blackboard (async).** As each leaf reports SOLVED, verify it, then
   `scripts/bank.sh add <Attempt> <LeafName> <its bank file>` (regenerates the blackboard). Now
   dispatch any leaves whose deps just landed. Repeat until all leaves are solved.
   *(This is the keeper's async-dispatch role — the orchestrator executes it.)*
5. **Crux racing (Phase ② — best-of-N).** For the single hardest leaf, race 2–3
   provers running *genuinely different* strategies; the first kernel-clean one wins, cancel the rest.
   - **Get the strategies from `proof-strategist`** — a good race needs *diverse* attacks, not the same
     tactic thrice (e.g. explicit-separating-functional+`norm_num` vs. same-skeleton+`nlinarith` vs. a
     different Mathlib API route). Same skeleton / different discharge is cheap diversity; a different
     API is the real hedge.
   - **Each racer writes to its OWN candidate file OUTSIDE the leaf dir** — use a sibling staging dir
     `MathProof/Bank/<Attempt>Race/<Leaf><Tag>.lean` (still gitignored under `MathProof/Bank/`, still a
     buildable module, but NOT globbed into the blackboard). Each candidate declares
     `namespace MathProof.Bank.<Attempt>`, imports the deps, and proves the SAME lemma name. Each
     self-verifies with `lake build MathProof.Bank.<Attempt>Race.<Leaf><Tag>`.
   - **Adjudicate deterministically:** `scripts/bank.sh race <Attempt> <Leaf> <cand1> <cand2> …` installs
     each candidate as the canonical leaf in turn, gates it (build + no-sorry + trusted axioms), and
     keeps the FIRST that passes (exits non-zero if none do → escalate/re-strategize). Then TaskStop the
     other racers and `rm -rf MathProof/Bank/<Attempt>Race`.
   - Crux-only (N× token cost) — never race every leaf.
6. **Verify the bank.** `scripts/bank.sh verify <Attempt>` — every leaf builds, no sorry, trusted trio.
7. **Assemble.** `scripts/bank.sh assemble <Attempt> C00NN` → one self-contained challenge module.
8. **GATE (non-negotiable).** `scripts/check-proof.sh C00NN --all` + `proof-auditor` + `verify-all.sh`.
   Only on all-green: commit, `scripts/log-pattern.sh`, then `scripts/bank.sh clean <Attempt>`.

## Automated: the `swarm-prove` Workflow (Phase ③)

**Requirement:** this phase needs a Claude Code build that provides the `Workflow` tool (a
multi-agent orchestration runtime that runs scripts like `.claude/workflows/swarm-prove.js`); this
repo does not define it. Without it, use the manual loop above (steps 1–8), which needs only the
subagents and `scripts/bank.sh`.

The loop above can be driven **manually** (the orchestrator hand-runs each step) or **automatically**
via the reusable Workflow at `.claude/workflows/swarm-prove.js` — the F3 async-keeper is encoded as a
DAG-wave schedule (sequential over topological waves, parallel within each). Launch it (explicit
multi-agent-orchestration opt-in) with:

```
Workflow({ scriptPath: ".claude/workflows/swarm-prove.js", args: {
  attempt: "C00NNSlug",            // CamelCase bank id (must be pre-inited: bank.sh init <attempt>)
  target:  "C00NNSlug",            // challenge module for assemble
  // EITHER supply the DAG directly …
  leaves: [{name, statement, deps:[names], exact?}],
  // … OR let proof-strategist derive it:
  strategistPrompt: "…the goal + recommended decomposition…",
  auditLeaves: false,              // per-leaf proof-auditor pass (default true)
}})
```

It runs `plan → wave-scheduled parallel prove (Sonnet→Opus escalation) → audit → assemble+check-proof`,
in the background with cache/resume (`resumeFromRunId`), and returns `{waves, leaves, blocked, assembled,
gate_ready}`. **Hub-and-gate is preserved:** the Workflow only produces a `check-proof --all`-clean
assembled candidate — the **orchestrator** still pre-inits the bank, runs the authoritative
`proof-auditor` + `verify-all`, wires the import into `MathProof.lean`, and is the **sole committer**.
The Workflow never edits `MathProof.lean`, never runs `verify-all`, never commits. Prefer the Workflow
for a DAG with ≥2 real dependency levels; use the manual loop for a quick 1-wave+combiner shape or when
racing a crux (Phase ②). Worked example: C0048 (`210 ∣ n¹³ − n`, 4→2→1).

## Leaf-prover spawn contract (runbook, not a treasure hunt)

Each dispatched `lean-prover` gets:
- **Goal:** the exact leaf statement + its `sg` id.
- **Write target:** `MathProof/Bank/<Attempt>/<LeafName>.lean`, structured as
  `import MathProof.Basic` + one `import MathProof.Bank.<Attempt>.<Dep>` per dependency leaf (import
  the SPECIFIC deps from the DAG — **never** the `<Attempt>` aggregator, which cycles once this leaf
  is added) + `namespace MathProof.Bank.<Attempt>` + the lemma + `end`. `bank.sh blackboard <Attempt>`
  prints the import lines currently available.
- **Rules:** the lemma (and anything other leaves depend on) must be **PUBLIC** (Lean `private` is
  module-scoped, invisible across bank modules); cross-leaf references use **bare names**.
- **Self-verify:** `lake build MathProof.Bank.<Attempt>.<LeafName>` clean; then report the path +
  SOLVED/BLOCKED + `#print axioms` (must be ⊆ `[propext, Classical.choice, Quot.sound]`).
- **Constraints:** NO `native_decide`; no `sorry`; 2-attempt cap then stop-and-report. This is
  `lean-prover`'s "Bank-leaf mode": no `challenges/*.md` statement doc, and it does not touch the ledger
  (the orchestrator records attempts with `proof-ledger.sh`).

## Invariants (the trust model — never relax)

- **Lean's kernel is the only arbiter.** No result is committed without `check-proof` + `proof-auditor`
  + `verify-all`. `TRUSTED_AXIOMS` is never widened; `native_decide` never enters.
- **Hub-and-gate topology.** Agents share *state* (the blackboard); the orchestrator alone assembles
  and commits. No autonomous agent-to-agent merge to `master`.
- **Parallelism follows the DAG.** A serial critical path stays serial — the win is on independent
  leaves, not by speeding one linear descent.

## Commands

`scripts/bank.sh {init|add|blackboard|list|verify|race|assemble|clean|selftest} <Attempt> [...]` — see
the script header for the leaf-file conventions. `race` is the Phase ② best-of-N adjudicator; `selftest`
runs the adversarial regression (topo order · cycle reject · race winner/all-fail) — run it before
trusting `assemble`/`race` on a new DAG shape. Bank lives under gitignored `MathProof/Bank/`.
