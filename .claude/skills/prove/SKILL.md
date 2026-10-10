---
name: prove
description: "Prove a theorem in this Lean 4 + Mathlib repo — the end-to-end loop (scaffold → search → draft → build → certify → iterate), a tactic cheat-sheet, and the Lean-is-truth discipline. Triggers: '/prove', 'prove this theorem', 'formalize and prove', 'close this challenge', 'write the Lean proof', 'finish the sorry'."
model: inherit
color: green
version: "1.1"
---

# prove — Lean 4 proving loop for lean-proof-agents

> **Lean is the only proof authority.** A challenge is SOLVED only when its module builds with
> **no `sorry`** and clean axioms. Wolfram is a scratchpad, never evidence. Never weaken a
> statement to make it pass — the statement *is* the spec.

On a fresh clone run `./setup.sh` first (installs the toolchain and fetches the prebuilt Mathlib
cache). Then always `source "$HOME/.elan/env"` (or have `~/.elan/bin` on PATH) before `lake`/`lean`.

## Stage 0 — literature pre-pass (research-open / Erdős / competition targets)

Before investing a proof in a `research open` Erdős problem or a paper/competition target, run the
**literature gate** — the DB lags the papers (#593/#707 were quietly "solved" by an existing result):
- `scripts/lit-search.sh "<problem in 2–3 phrasings>" [--erdos N]` (or dispatch `lit-scout`) →
  OPEN-CONFIRMED / LIKELY-SOLVED(ref) / UNCERTAIN; append the row to `docs/LIT_LOG.md` so it is
  never re-searched. Skip for a self-contained warm-up or a known Mathlib gap.

**Finite / decidable goal?** (a bounded ∀/∃ search; an Erdős `falsifiable`/`decidable`/`verifiable`
target) — reach for the **solver layer**, not hand-tactics: `search-reducer` → `scripts/solve.sh`
(search) → `scripts/witness-to-lean.sh` emits a `decide +kernel` certificate bridged by a
`MathProof.Certify` lemma (the witness→Lean *moat*; lemmas in `MathProof/Certify/`, generator
usage in the header of `scripts/witness-to-lean.sh`). Only some certificate shapes exist yet — see
`search-reducer`. The certified range
is a documented subset of the searched range — an empty search is an honest partial result, never a
prize claim without a real witness.

## The loop

1. **Scaffold** — `scripts/new-challenge.sh "<name>"` → new module + statement doc + wired import.
   (Skip if editing an existing challenge.)
2. **State** — write the theorem precisely. Prefer division-free / cast-free forms in ℕ
   (e.g. `s * 2 = n * (n+1)` over `s = n*(n+1)/2`). Keep the body `sorry` while working.
3. **Search FIRST** — proving is mostly "does this lemma already exist?"
   - By NAME: `scripts/mathlib-search.sh "<name-or-fragment>"` (loogle + local grep); type pattern
     via `--type "(n : ℕ) → n ∣ n !"`.
   - By GOAL: `scripts/lean-suggest.sh "(a b : ℝ) : 2*a*b ≤ a^2 + b^2"` → Lean's `exact?`/`apply?`.
   - In a Lean buffer: `exact?`, `apply?`, `rw?`, `simp?`, `hint`.
   - Check `PROOF_PATTERNS.md` for a recipe matching the goal shape before improvising.
4. **Draft** — write the proof (see cheat-sheet + patterns below).
5. **Build** — `lake build MathProof.Challenges.C####Name` (cache-backed, ~5s).
   Read the FIRST error; fix top-down. Lean errors cascade — one real error spawns many.
6. **Certify** — `scripts/check-proof.sh C####Name [theoremName]` → must report SOLVED
   (no `sorry`, and no axioms beyond `propext`, `Classical.choice`, `Quot.sound` — any other axiom
   is a failure, not a note).
7. **Log** — set the `challenges/####-*.md` status to SOLVED; run `scripts/verify-all.sh`.

**Iteration cap:** 2 serious attempts on a stuck goal, then stop and report the exact goal state
+ what you tried — don't thrash. Consider `sorry`-ing a sub-lemma to isolate the hard part.

## When it's hard — the trajectory (DEPTH) loop

The loop above is width-first: search, draft, build. When a goal is genuinely hard — it survives
2 attempts, needs decomposition, or comes back BLOCKED — switch from "try again" to **managed
depth** (`docs/PROOF_METHODOLOGY.md` Part E). Don't thrash; run the project-management loop:

1. **Plan.** Dispatch `proof-strategist` on the goal → it runs the small-case truth gate, an
   anchor pre-pass, a WLOG check, decomposes into a leaf-first subgoal DAG, and **initializes the
   ledger** (`scripts/proof-ledger.sh`). You get an `attempt_id` + a per-subgoal attack + tier (`sonnet` → `lean-prover`,
   `opus` → `lean-prover-opus`).
   (NO-GO ⇒ the statement is false/vacuous — fix the *statement*, never fake the proof.)
2. **Attack a leaf.** Take the next open leaf whose `deps` are all solved; dispatch the planned
   tier's prover (`lean-prover` or `lean-prover-opus`) with its verified anchor. The prover does not
   touch the ledger — *you* record the outcome. Measure the delta objectively:
   `b=$(scripts/lean-goals.sh <mod> --count)` before and `a=$(...)` after the attempt, then
   `scripts/proof-ledger.sh attempt <id> <sg> --tier T --sketch "…" --result fail|ok --delta $((a-b))`
   (`--delta` = change in open-goals + sorries; **negative = progress**).
3. **Check the trajectory.** `scripts/proof-ledger.sh stall-check <id> <sg>`. On STALL / THRASH /
   BUDGET, dispatch `proof-trajectory-keeper` → it returns ONE decision (anchor / penultimate /
   escalate-tier / invariant / generalize / specialize / decompose / guilty-lemma / abandon).
4. **Execute the decision** — *you*, the orchestrator (the keeper is advisory and cannot dispatch):
   escalate to `lean-prover-opus`, re-invoke `proof-strategist` to DECOMPOSE / RE-PLAN, run the
   anchor search, etc. **Never repeat a logged dead-end.**
5. **Propagate.** When a node's `deps` are all `solved`, attack the node. When every subgoal is
   `solved`, assemble the proof, `check-proof.sh`, then `proof-auditor`.
6. **Look back (mandatory).** After a clean audit, `scripts/log-pattern.sh` the winning recipe (and
   note the dead-ends). The flywheel — don't skip it.

> **No subagents available?** (e.g. the agents are not registered in this Claude Code session —
> project agents load at session start.) Play every role yourself: run `proof-ledger.sh` directly and
> follow Part E's decision ladder. The ledger discipline works with zero subagents.

## Tactic cheat-sheet (the workhorses)

| Tactic | Use when |
|---|---|
| `simp` / `simp only [lemmas]` | simplify; discharge routine goals. `simp?` shows the lemma set used. |
| `ring` / `ring_nf` | commutative-(semi)ring equalities (ℕ, ℤ, ℝ, polynomials). |
| `omega` | linear arithmetic over ℕ/ℤ (incl. `∣` by small constants, `min/max`). First reach for ℕ goals. |
| `linarith` / `nlinarith` | linear / nonlinear arithmetic over ordered fields (ℝ, ℚ). `nlinarith` tries products. |
| `norm_num` | concrete numeric goals & `≠`/`<` on literals; extensions for primality etc. |
| `positivity` | goals `0 < e` / `0 ≤ e` from structure. |
| `gcongr` | monotonicity: reduce `f a ≤ f b` to `a ≤ b`. |
| `decide` | decidable propositions on concrete data (small). |
| `induction n with \| zero => \| succ k ih =>` | ℕ induction; `Nat.rec`. |
| `obtain ⟨x, hx⟩ := h` / `rcases` | destructure ∃ / ∧ / ∨. |
| `intro x` / `refine` / `exact` | introduce, build terms with holes, finish. |
| `push_cast` / `exact_mod_cast` / `Nat.cast_*` | move casts (ℕ→ℤ→ℝ) out of the way. |
| `field_simp` | clear denominators before `ring` in fields. |
| `calc` | multi-step (in)equalities, readable chains. |

Discovery tactics: `exact?`, `apply?`, `rw?`, `simp?`, `hint` — run them, then paste the concrete
lemma they suggest (don't leave `exact?` in committed code).

## Patterns

- **Induction skeleton**
  ```lean
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  ```
- **∀ … ∃ …** — `intro n; obtain ⟨p, hp⟩ := <lemma> ...; exact ⟨p, ...⟩`.
- **Divisibility / mod** — try `omega` first for constants; else `Nat.dvd_*`, `Nat.mod_*`.
- **Reformulate to avoid ℕ subtraction/division** — they truncate; multiply through instead.
- **Existence of primes** — `Nat.exists_infinite_primes`, `Nat.infinite_setOfPred_prime`.

## Discipline & anti-cheating

- **Statement fidelity:** the Lean statement must capture the real claim. Beware vacuous or
  trivially-true restatements (`True`, hypotheses that are `False`, `∀ x ∈ ∅`). Have `proof-auditor`
  check intent for anything non-trivial.
- **Axiom hygiene:** `check-proof.sh <mod> <thm>` prints `#print axioms`. Flag anything beyond the
  standard trio (`propext, Classical.choice, Quot.sound`) — especially `sorryAx`.
- **No cache-busting:** never trigger a full Mathlib source build. If the cache misses, align
  `lean-toolchain` to Mathlib's and `lake exe cache get`.
- **Wolfram** (`scripts/wolfram.sh "<atomic query>"`) only to sanity-check a value/identity before
  investing — it is never proof.

## Routing
Hard proofs → dispatch the `lean-prover` subagent. Lemma hunts → `mathlib-scout`. Finished proofs →
`proof-auditor`. See CLAUDE.md §Meta-system.
