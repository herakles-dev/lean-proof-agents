# SWARM_SPEC.md — swarm-collaboration improvement spec

> **KIND:** A multi-agent **collaboration layer** for lean-proof-agents's proof orchestration — turn the
> serial DEPTH loop (strategist → prover → auditor, one at a time) into a coordinated **team of
> provers** working the leaves of one proof **in parallel/async**.
>
> **Differentiator:** a **shared-blackboard** topology — agents build on each other's *completed*
> leaves through an importable lemma bank — **without weakening the trust model**: every result
> still passes `check-proof` + `proof-auditor` + the Lean kernel; the orchestrator stays the sole
> assembler + gate. Lean is the only arbiter, always.

**Status:** Phases ①②③ implemented; each was exercised on a real proof (C0046, C0047, C0048)
· **Author:** D. Michael Piscitelli · **Created:** 2026-09-16
**Aim:** the proofs are the verified artifact; the orchestration tooling around them is a reusable
workflow, and each real proof doubles as a test of that tooling.

## 1. Purpose & scope

Before this layer the orchestrator dispatched one subagent at a time and serialized provers that touch
the same file (observed 2026-09-16: two provers on `Certify/Reflect.lean` had to run back-to-back). The
layer lets N provers attack **independent leaves of one proof at once**, share completed lemmas live, and
be assembled + kernel-gated into one self-contained challenge module.

**In scope:** ① shared-blackboard lemma bank (`scripts/bank.sh` + convention); ② best-of-N crux
racing; ③ a deterministic `Workflow` swarm template. Parallel-leaf dispatch is driven by the
`proof-strategist` subgoal DAG.
**Out of scope:** full agent-to-agent autonomy with no verification hub (rejected — see §6); GPU /
compute scaling (a separate, parked workstream).

## 2. Architecture

```
proof-strategist → subgoal DAG + ledger
        │
orchestrator: bank.sh init <Attempt>
        │  dispatch a prover on EVERY currently-independent leaf at once
        ├─ prover(sg_i) ─► MathProof/Bank/<Attempt>/Sg_i.lean   (owns its file; no contention)
        │                    imports MathProof.Basic + MathProof.Bank.<Attempt> (the blackboard)
        └─ blackboard MathProof/Bank/<Attempt>.lean  ── auto-regen on each `bank.sh add` (grows async)
        │
   as leaves land → dispatch newly-unblocked leaves (deps now on the blackboard)
   crux leaf → best-of-N: 2–3 diverse-strategy provers race, first kernel-clean wins, cancel rest
        │
orchestrator: bank.sh assemble <Attempt> C00NN  ─► one self-contained challenge module
        │  (leaves inlined under one namespace; bare-name cross-refs preserved)
        └─ GATE: check-proof --all + proof-auditor + verify-all  → commit → log-pattern
```

## 3. Phases (lifecycle)

- **Phase ① Shared-blackboard lemma bank** *(✅ done — exercised end-to-end 2026-09-16)* —
  `scripts/bank.sh` (`init/add/blackboard/list/verify/assemble/clean`); leaves are public, importable,
  gitignored under `MathProof/Bank/`, driven by a **dedicated `/swarm` skill** (its own skill, NOT
  folded into `/climb`). **Validated on C0046** (`30 ∣ n⁵−n`): 3 independent
  modular leaves proven **in parallel** by 3 `lean-prover`s on a live blackboard, combiner built on
  them, assembled module passed `check-proof --all`, `proof-auditor` and `verify-all` (the whole-repo
  regression run; see `challenges/0046-thirty-divides-n-pow5-minus-n.md`). Two
  bugs surfaced by that run and were fixed (see "Friction log" below).

  **Friction log from the C0046 run (2026-09-16):**
  - **F1 — `add` self-copy abort (fixed).** The leaf-prover contract writes straight INTO
    `MathProof/Bank/<Attempt>/<Leaf>.lean`, but `add` did `cp src dest`; the documented in-place case
    (`src == dest`) errored `cp: are the same file`, and under `set -e` aborted **before**
    `regen_blackboard` — the blackboard was silently left empty. Fix: guard the copy with the bash
    same-file test `[[ ! "$src" -ef "$dest" ]]` → `add` is idempotent for in-place leaves.
  - **F2 — `assemble` inlined in glob (alphabetical) order, not DAG order (fixed).** Lean has no
    forward references within a file, so a combiner inlined before its deps → "unknown identifier".
    Alphabetical names bite (`Combiner`/`DvdThirty` sort before `DvdTwo`/`DvdThree`). Fix: `assemble`
    now **topologically sorts** leaves by the dep graph encoded in each leaf's `import <ns>.<Dep>`
    lines (Kahn, alphabetical tie-break, aborts on an import cycle) — correct for any leaf naming.
  - **F3 — async-keeper dispatch is still manual (noted, not blocking).** The orchestrator hand-runs
    verify→`add`→dispatch-next-wave. Trivial for a 1-wave+combiner DAG; a deeper DAG wants a driver
    (Phase ③ `Workflow`, or a keeper loop).
- **Phase ② Best-of-N crux racing** *(✅ exercised on C0047 — see `challenges/0047-erdos-97-three-equidistant-9gon.md`)* —
  race 2–3 diverse strategies on the single hardest leaf; first kernel-clean wins; cancel losers.
  Crux-only (N× token cost).
- **Phase ③ Workflow swarm template** *(✅ built and validated 2026-09-16 — `.claude/workflows/swarm-prove.js`)* —
  encodes `plan → parallel-prove-leaves → parallel-audit → assemble+check` as a reusable `Workflow`
  script (background, cache/resume via `resumeFromRunId`). Multi-agent orchestration is opt-in: it runs
  only when explicitly requested.
  - **F3 fixed (the async-keeper is now automatic).** The manual verify→add→dispatch-next-wave loop is
    encoded as a sequential `for`-loop over the DAG's topological **waves**, `parallel()` within each
    wave. A wave-N+1 leaf imports wave-N leaf *files* (which exist on disk the moment the wave-N prover
    writes+self-verifies them — `bank.sh add` is **not** needed for dependency resolution, only to regen
    the aggregator for `verify`/`assemble`), so the per-wave barrier is the correct, race-free schedule.
    No prover runs `bank.sh add` (that would race on the aggregator); a single integrator agent runs all
    `add`+`verify`+`assemble` sequentially at the end.
  - **Hub-and-gate preserved.** The Workflow produces an *assembled, `check-proof --all`-clean candidate*;
    the orchestrator (the main Claude Code session, supervised by a human) runs the **authoritative `proof-auditor` +
    `verify-all`**, wires the import into `MathProof.lean`, and is the **sole committer**. The Workflow
    never edits `MathProof.lean`, never runs `verify-all`, never commits.
  - **Validation (F1/F2 discipline — prove the tooling on a controlled input first).** Synthetic 4-leaf /
    3-wave DAG (`A,B` independent → `C`←{A,B} → `D`←C, trivial lemmas, Haiku): waves scheduled correctly,
    cross-leaf disk imports resolved, assembled module independently re-gated `check-proof --all` SOLVED.
  - **Exercised on a real 3-level target — C0048 `210 ∣ n¹³ − n`** (2026-09-16). `proof-strategist`
    derived the 4→2→1 DAG (`{2,3,5,7} → {6,35} → 210`, 7 leaves, 3 waves); the Workflow wave-scheduled
    the parallel provers (9 agent runs, none errored, about 6 minutes; the run artifacts are gitignored and not in this
    tree); the orchestrator gated with `check-proof --all`, `proof-auditor` (passed) and `verify-all`, and committed. This was the first Workflow-driven swarm proof, and the
    first swarm proof to exercise the Plan phase + a genuine 3rd dependency level.

## 4. Agents

Reuses the existing ladder — `proof-strategist` (plan/DAG), `lean-prover`(+`-opus`) (leaf edit),
`proof-auditor` (review), `proof-trajectory-keeper` (manage). **New role, no new agent type:** the
keeper drives **async leaf dispatch** (reads ledger + bank, dispatches leaves whose deps are on the
blackboard). Phase ③ wraps the whole flow as a `Workflow`.

## 5. Gates (Definition of Done)

- **①** `bank.sh` all subcommands work; a dependent leaf imports the blackboard and builds; assembled
  module passes `check-proof --all` + `verify-all`; ≥1 real multi-leaf proof run through it (C0046); the `/swarm`
  skill drives parallel-leaf dispatch + the async keeper loop.
- **②** racing harness dispatches N, takes first kernel-clean, cancels rest; exercised on a crux (C0047).
- **③** ✅ `Workflow` script (`.claude/workflows/swarm-prove.js`) runs the full pipeline in background
  with cache/resume; the DAG-wave scheduler automates the F3 async-keeper (no manual dispatch loop); the
  orchestrator retains the authoritative `proof-auditor` + `verify-all` gate + sole commit. Validated
  on a synthetic 4-leaf/3-wave DAG and on a real 3-level proof (C0048).
- **INVARIANT (all phases):** no result reaches a commit without `check-proof` + `proof-auditor` +
  kernel; `TRUSTED_AXIOMS` never widened; no `native_decide`; orchestrator assembles + gates.

## 6. Risk & guardrails

| Risk | Handling |
|---|---|
| Bank collision / stale blackboard | each prover owns a file; blackboard = *completed* leaves only; `add` after prove |
| Assembly re-namespacing bug | assembled module MUST pass `check-proof` (bare-name cross-refs in a shared namespace) |
| Racing token blowout | crux-only, not every leaf |
| Parallelism doesn't help a serial critical path | dispatch follows the DAG — WIDTH win, not a serial speedup |
| **Trust erosion (the real danger)** | **hub-and-gate topology: agents share state, orchestrator alone assembles + kernel-gates. NO full agent-to-agent autonomy.** |

## 7. Non-goals

- Lean's kernel is never bypassed or its axiom set widened — the swarm changes *coordination*, never *trust*.
- No autonomous agent-to-agent merge to `master`; the orchestrator commits.
- No GPU / compute scaling in this spec (separate, parked workstream).
