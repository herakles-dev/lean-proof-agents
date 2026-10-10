# PROOF_METHODOLOGY.md — how hard proofs actually get solved

Synthesizes two parallel research briefs — **human
problem-solving discipline** (Pólya → Schoenfeld) and **machine/Lean-tactics practice**
(Mathlib workflow + AlphaProof/DeepSeek-Prover/LeanDojo/HTPS) — into one evidence-cited
reference, with every technique mapped to a concrete mechanism in *this* system: the orchestrating agent's task list,
the model-tier ladder (a small fast model for scouting → a mid-size model for proving → a larger
model for hard cases → the strongest available model as the last rung; "apex" below means that last rung), the
Lean-is-sole-arbiter discipline, `/prove`/`/climb`, and the agents/scripts already on disk.

> **Note (2026-10-10).** This document is the research and design basis, written *before* the
> trajectory layer was built. The layer has since been built; the "Status", "NEW" and "None"
> entries in Parts D and E describe the state before that build and are kept as a record of the
> design. What now exists in the tree: the subgoal ledger tool `scripts/proof-ledger.sh`
> (`init/add/attempt/mark/dead-end/decision/stall-check/status`; ledgers are written to a gitignored
> `.proof-ledger/<attempt_id>.json`, so none is committed), the open-goal counter
> `scripts/lean-goals.sh`, and the agents `.claude/agents/proof-strategist.md` (plan) and
> `.claude/agents/proof-trajectory-keeper.md` (manage). Dead ends are recorded in the ledger via
> `proof-ledger.sh dead-end`; a separate dead-ends file proposed below was never built.

**Feeds:** Part E (trajectory-management methodology + subgoal-ledger schema) and the
components built from it (proof-strategist agent, proof-trajectory-keeper agent, `scripts/proof-ledger.sh`,
`/prove`+`/climb` upgrades). Parts A–C are the evidence base; **Part D** is the deduplicated
mechanism inventory (D1–D20); **Part E** is the synthesis — the trajectory-management
methodology and the concrete subgoal-ledger schema that `scripts/proof-ledger.sh` implements.

---

## Part A — Human problem-solving discipline

### A1. Pólya — understand / plan / execute / **look back**
**Idea.** Four phases, with "look back" the most skipped and most valuable: it catches errors,
extracts the reusable method, and spots generalizations. Heuristics live in the plan phase,
triggered by a fixed question-list: analogy, auxiliary/sub-problem, decomposition, specialize,
generalize (→ A5), work backwards, restate/vary.
**Mechanism.** A mandatory post-SOLVED "look-back" step, distinct from correctness auditing
(`proof-auditor` already does that): "is this method reusable/generalizable?" — force-write to
`PROOF_PATTERNS.md`, not optional the way `log-pattern.sh` was when this was written. A named plan-phase checklist
(analogy/auxiliary/decompose/specialize/generalize/backwards) a prover consults *before* free
tactic search, not just after getting stuck.
**Citation.** G. Pólya, *How to Solve It* (1945): https://www.hlevkin.com/hlevkin/90MathPhysBioBooks/Math/Polya/George_Polya_How%20to%20Solve%20It.pdf ; overview: https://en.wikipedia.org/wiki/How_to_Solve_It

### A2. Bundy — proof planning, methods + critics, rippling
**Idea.** Treats proof attempts as AI planning: "methods" are meta-level specs of tactics
(preconditions + effects on proof state), so the planner searches over methods, not raw
inference rules. **Rippling** is a rewriting heuristic for induction that annotates syntactic
differences between goal and IH, then rewrites to move them outward until the IH applies.
Subgoals from method decomposition sometimes *interact* and must be interleaved, not solved in a
fixed order (Sussman anomaly: naive independent-subgoal ordering fails when subgoals interfere).
**Mechanism.** Represent tactics as preconditioned methods (this repo's tactic decision table,
B3, is already close); on failure, invoke a **critic** — a pattern-matched failure diagnosis
("IH too weak") that proposes a concrete patch (generalize, restructure) instead of blind retry.
Treat subgoal ordering in a decomposition as provisional — re-check for interaction before
assuming one `have` doesn't disturb another.
**Citations.** Bundy, "Proof Planning," AIPS 1996: https://cdn.aaai.org/AIPS/1996/AIPS96-033.pdf ;
Bundy/Basin/Hutter/Ireland, *Rippling*, CUP 2005: https://www.research.ed.ac.uk/en/publications/rippling-meta-level-guidance-for-mathematical-reasoning/ ;
Ireland & Bundy on critics: https://link.springer.com/content/pdf/10.1007/978-3-540-30210-0_4.pdf ;
Sussman anomaly: https://en.wikipedia.org/wiki/Sussman_anomaly

### A3. Blueprint decomposition — leaf-first proving
**Idea.** A blueprint (Massot's `leanblueprint`) is a human-authored DAG of statements linked by
`\uses` dependency tags, rendered as a status-colored graph. It converts one unapproachable
theorem into many small, independently attackable, parallelizable leaf tasks.
**Mechanism.** A node is provable only once every `\uses` parent is green — the DAG *is* the
subgoal ledger (id, statement, dependency edges, status enum, assigned agent). This is exactly
what `scripts/blueprint-leaves.sh` / `blueprint-scout` already exploit for *externally-sourced*
blueprints; the generalization is applying the same DAG-with-status-gate pattern to a theorem
we decompose ourselves (→ D1, the subgoal-ledger schema in Part E).
**Citations.** https://github.com/PatrickMassot/leanblueprint ; Tao, "Formalizing the proof of
PFR in Lean4 using Blueprint": https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/ ;
automation of this pattern: "Goedel-Architect": https://arxiv.org/html/2606.06468v1

### A4. Invariants and monovariants
**Idea.** An invariant is preserved by every allowed move; a monovariant changes monotonically
toward a bound. The right one turns "search over an unbounded process" into "compute one
algebraic fact" — structurally identical to loop invariants/termination measures.
**Mechanism.** For any goal with recursive/iterative structure, run an explicit
invariant-search sub-step *before* attacking the induction step: compute the quantity on small
cases → find something preserved/monotone → verify one-step preservation → use as the (possibly
strengthened) IH. Lean's own well-founded-recursion machinery already forces monovariant
discovery for termination; a prover agent can reuse that same search for ordinary induction, not
just termination proofs.
**Citations.** Engel, *Problem-Solving Strategies*, Springer 1998, "Invariance Principle":
https://www.goodreads.com/en/book/show/187041.Problem_Solving_Strategies ;
https://brilliant.org/wiki/invariant-principle-definition/ ;
MIT IMO notes: https://web.mit.edu/yufeiz/www/wc08/invariants.pdf

### A5. Generalize vs. specialize — the inventor's paradox
**Idea.** Pólya's inventor's paradox: a *more general* claim can be easier to prove because its
stronger IH carries more information into the inductive step. Specialization is the mirror
move — cheap orientation/falsification before committing effort.
**Mechanism.** When induction stalls on "the IH isn't strong enough," don't grind the same
statement — auto-retry with a deliberately generalized version (add a parameter, drop a
hypothesis, prove a family at once) as a distinct, checkable move, *before* tier-escalating.
Conversely, require a small-case specialization pass (n=0,1,2, degenerate cases) before
formalizing at all — `conjecture-scout` gestures at this; make it a required gate (→ D10), not
optional.
**Citation.** https://en.wikipedia.org/wiki/Inventor's_paradox (ties to Bundy's generalization
critics in A2).

### A6. Backtracking and dead-end recovery
**Idea.** Two disciplines: (i) algorithmic backtracking — undo the *most recent* choice point on
failure, escalate to earlier choice points only when all alternatives there are exhausted; (ii)
Lakatos's *Proofs and Refutations* — when a counterexample kills a proof, localize the specific
"guilty lemma" it violates and repair that lemma rather than discarding the whole proof.
**Mechanism.** Model a proof attempt as a choice-point stack (tactic tried / lemma tried /
decomposition chosen) so failure retries at the *right* granularity instead of restarting from
scratch. Maintain a durable per-goal "attempted-and-failed" log (a negative-result extension of
`PROOF_PATTERNS.md`) read *before* the next attempt or tier escalation is dispatched — at the time of
writing, `lean-prover`'s BLOCKED report carried this info only transiently (it went back to the
orchestrator once, not persisted for reuse; the ledger's dead-end log now persists it). When `proof-auditor` finds a vacuous/false
statement, run a guilty-lemma localization pass and repair the specific leaf rather than
abandoning the whole subgoal tree.
**Citations.** Lakatos, *Proofs and Refutations*, CUP 1976: https://classes.matthewjbrown.net/teaching-files/hps/lakatos.pdf ;
on preserving failed explorations as durable records in agentic math research: "AI
Co-Mathematician" (2026): https://arxiv.org/html/2605.06651v1

### A7. Get-unstuck playbooks (Tao, Zeitz)
**Idea.** Tao: if you can't solve a problem, find an easier one you *still* can't solve — value
partial progress (special cases, weakened conclusions, extra hypotheses) as measurable stepping
stones; when truly stuck, write up how far you got and switch problems instead of grinding.
Zeitz: Strategy → Tactics → Tools, with two named moves — **penultimate step** (work backward:
what's the single last deduction before the goal, and what would make it possible?) and
**wishful thinking** (assume the hard part is done; see what's left).
**Mechanism.** Bake a literal penultimate-step query into the prover's search-first phase —
"what single lemma would close this if the rest were established?" — as a deliberate first move
(adjacent to `exact?`/`apply?` but intentional, not last-resort). Add a hard stuck-detection
trigger: after N failed attempts *on the same decomposition* with no measurable progress, force
a mode switch (tier-escalate, or re-decompose) rather than cosmetic variations of the same
approach.
**Citations.** Tao: https://terrytao.wordpress.com/career-advice/solving-mathematical-problems/ ,
https://terrytao.wordpress.com/career-advice/ ; Zeitz, *The Art and Craft of Problem Solving*
(3rd ed., 2017): https://www.wiley.com/en-us/The+Art+and+Craft+of+Problem+Solving,+3rd+Edition-p-9781119239901
(secondary summary used for exact penultimate-step/wishful-thinking wording — **flagged
unverified** against the primary text: https://medium.com/@millingaboutblog/notes-from-the-art-and-craft-of-problem-solving-chapters-1-and-2-c0198890b7fe)

### A8. Metacognition — Schoenfeld
**Idea.** Splits competence into Resources (domain knowledge), Heuristics (Pólya-style
strategies), **Control/monitoring** (deciding when to apply what, whether to keep going or
change course), and Beliefs. Videotaped protocols showed experts spend a large share of
solving-time on monitoring checkpoints ("is this getting me anywhere?"), while novices pick one
strategy and grind it regardless of evidence it's failing — monitoring, not raw heuristic
knowledge, is the main expert/novice gap.
**Mechanism.** Instrument every attempt with periodic progress self-reports, not just terminal
success/fail — e.g. "is the goal term smaller / more specific / closer to a known lemma than at
the last checkpoint?" If no measurable progress across a fixed step count, force an explicit
control decision (continue / replan / escalate / abandon). This was the gap between the
**fixed** attempt cap (2 for `lean-prover`, 3 for `lean-prover-opus` — a resource budget) and a
true **progress-sensitive** budget (→ D2).
**Citations.** Schoenfeld, *Mathematical Problem Solving*, Academic Press 1985; summary:
https://www.instructionaldesign.org/theories/mathematical/ ,
https://serc.carleton.edu/quantskills/methods/schoenfeld.html ; on control specifically:
https://link.springer.com/chapter/10.1007/978-94-6209-299-0_6

---

## Part B — Lean/Mathlib formalization practice

### B1. `sorry`-driven top-down development
**Idea.** State the top theorem first, wrap unproved pieces in `sorry`/`have h : P := sorry` so
the file type-checks end-to-end while sub-lemmas are filled in later, in any order. One big
unknown becomes a checklist of small, independently-attackable holes, and the skeleton itself
documents the decomposition.
**Mechanism.** A "stub-and-fill" scaffolder: given a target theorem, generate a skeleton of
named `have` sub-goals from a decomposition plan, each a `sorry`; track them as a todo-ledger
keyed by goal signature; discharge leaves first, propagate closure upward. `check-proof.sh`
already enforces that no `sorry` survives to SOLVED — the gap is that the *intermediate*
stub-tracking is currently all in the prover's head, not a durable ledger (→ D1).
**Citation.** "LeanFlow" describes the pattern precisely — formalization "stops at a proof
skeleton with source-backed sorry bodies," repair treats those as fixed targets it may not
weaken: https://arxiv.org/html/2607.20503v1 ; Mathlib contributing docs:
https://leanprover-community.github.io/contribute/index.html
**Uncertainty:** no single canonical essay codifies this as "sorry-driven development" — it's
tooling-supported folklore, attested at scale by the FLT project (B2).

### B2. Blueprint methodology (`leanblueprint` tool)
Same mechanism as **A3** — cross-reference rather than duplicate. What B adds beyond A3 is scale
evidence: the FLT project's blueprint "breaks the proof into many small lemmas… if you can
formalise just one, contributors are eagerly awaited," coordinated live on Zulip
(`scripts/zulip.sh` already gives us read-only claim-status recon on exactly this kind of
channel).
**Citations.** FLT announcement: https://leanprover-community.github.io/blog/posts/FLT-announcement/ ;
blueprint PDF: https://imperialcollegelondon.github.io/FLT/blueprint.pdf ; Anthropic's
collaboration write-up: https://www.anthropic.com/research/formalizing-fermats-last-theorem ;
`\uses`/`\notready` semantics: https://leanprover-community.github.io/archive/stream/113488-general/topic/lean.20blueprint.20dependency.20graph.html

### B3. Lean search/automation tactics — when each is right

| Tool | Use when | Notes |
|---|---|---|
| `exact?` | goal closable by one known lemma | metaprogramming search over all of Mathlib |
| `apply?` | goal matches a lemma up to further subgoals | same engine, partial match |
| `hint` | quick triage of what might work | tries a battery of tactics |
| `aesop` | goal discharged by chained rule application | **white-box best-first search** over a *rule set* — predictable, extensible; Mathlib builds `measurability`/`continuity` solvers on it |
| `simp?`/`simp` | goal reduces by rewriting | shows which lemmas fired |
| `omega` | linear arithmetic over ℤ/ℕ | decision procedure, always terminates |
| `decide` | small `Decidable` goal | brute-force kernel eval — cheap but can time out |
| `nlinarith`/`linear_combination` | polynomial (in)equalities | `polyrith`'s Sage backend is **defunct**; `grobner`/`linear_combination` cover it locally now |
| `field_simp` | clear denominators first | preprocessing, not goal-closing |
| `gcongr` | monotonicity/relational goals | reduces `f(a)≤f(b)` to `a≤b` via a congruence-lemma library, discharges side-conditions via `positivity` |
| LeanSearch / Moogle | natural-language search for a remembered-but-unnamed lemma | neural, approximate |
| Loogle | search by type-signature/sub-expression | exact structural match |

**Mechanism.** This table *is* the "methods" library for A2's method+critic architecture — keep
it explicit and inspectable (Aesop's white-box philosophy) so a trajectory-keeper can diagnose
*which* tool almost fired, rather than treating tactic search as an opaque hammer call (→ D13).
**Citations.** Cheat sheet: https://leanprover-community.github.io/papers/lean-tactics.pdf ,
https://lean4.dev/tactics/cheat-sheet ; search comparison:
https://leanprover-community.github.io/blog/posts/searching-for-theorems-in-mathlib/ ,
https://github.com/leanprover-community/LeanSearchClient ; **Aesop** — Limperg & From,
"White-Box Best-First Proof Search for Lean," CPP 2023: https://people.compute.dtu.dk/ahfrom/aesop-camera-ready.pdf ,
https://github.com/leanprover-community/aesop ; `polyrith` status:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Polyrith.html ; `gcongr`:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GCongr.html ; **LeanSearch
v2** (2026, reasoning-mode retrieval that drafts a sketch, retrieves per-step candidates,
iterates until a coherent lemma set emerges — very recent preprint, not yet peer-reviewed):
https://arxiv.org/abs/2605.13137

### B4. Proof-structuring idioms
**Idea.** Beyond closing goals, Mathlib style favors tactics that keep long-proof *state*
legible: `have`/`suffices` name and isolate a sub-goal (`suffices` flips direction — "it's enough
to show X" — the natural encoding of top-down decomposition); `calc` chains a relation through
explicit intermediate terms, each line independently checkable/replaceable; `obtain`/`rcases`
destructure with a pattern (preferred over manual `cases` for structured proofs); `induction`
for recursion-shaped goals; `wlog` formally discharges a symmetry reduction, splitting into a
`hypothesisGoal` + `reductionGoal`.
**Mechanism.** Treat `calc` steps and named `have`s as **checkpoints** — a re-plan after a stall
only needs to back up to the nearest named checkpoint, not the theorem root (→ D14, and matches
A6's choice-point stack). Check for a `wlog`-style symmetry reduction *before* decomposing —
cheap win that halves the subsequent search tree (→ D16).
**Citations.** Mathematics in Lean: https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html ,
.../C03_Logic.html ; `rcases`: https://leanprover-community.github.io/mathlib_docs/tactic/rcases.html ;
`wlog`: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/WLOG.html

---

## Part C — Machine theorem provers

### C1. AlphaProof (DeepMind, IMO 2024 silver)
**Idea.** Couples a pretrained LM with an AlphaZero-style RL loop, operating entirely inside
**Lean** as verifier/environment. Bootstrapped from ~80M auto-formalized statements; RL lets
proved statements become training data for harder ones; used test-time adaptation/fine-tuning
on the actual competition problems once given them.
**Mechanism.** (1) Auto-formalization at scale to create formal training signal; (2) an RL loop
where formal search generates its own curriculum; (3) test-time compute spent specifically on
the target problem rather than relying only on a frozen policy — directly analogous to
tier-escalation spending more search *on the same goal*, not a fresh generic pass.
**Citations.** Nature 2025 (peer-reviewed, the primary technical source):
https://www.nature.com/articles/s41586-025-09833-y ; DeepMind blog:
https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/ ; follow-on gold-medal
Gemini Deep Think: https://deepmind.google/blog/advanced-version-of-gemini-with-deep-think-officially-achieves-gold-medal-standard-at-the-international-mathematical-olympiad/
**Uncertainty:** exact RL algorithm/search procedure not fully published; treat "self-play"/
curriculum mechanics as approximate.

### C2. DeepSeek-Prover-V2 & Draft-Sketch-Prove (DSP)
**Idea (DSP, original).** Convert an informal proof into a formal **proof sketch** — a skeleton
with high-level steps as lemmas/`have`s but gaps (`sorry`/`oops`) — then dispatch an automated
hammer/prover at just the gaps, instead of formalizing/proving the whole theorem in one shot.
**Idea (DeepSeek-Prover-V2).** A strong general LLM decomposes a theorem into subgoals as Lean
`have`-stubs; a smaller specialized prover fills each; resolved subgoals are stitched into a
full CoT+formal proof used as cold-start RL data for a large prover model (88.9% pass@ on
miniF2F-test, 49/658 on PutnamBench).
**Mechanism.** Two-tier architecture: a cheap/strong *decomposer* proposes named subgoal stubs
(mirrors B1's stub-and-fill, machine-generated); a separate *filler* only ever sees one subgoal
at a time — bounds context/search per call and localizes failure to a specific subgoal. This
maps directly onto a **proof-strategist** (decomposer) handing named `have`-stubs to
**lean-prover** (filler) — the existing Haiku-scout → Sonnet-prover boundary generalizes to
this exact split (→ D15).
**Citations.** DSP: Jiang et al., NeurIPS 2022, arXiv:2210.12283: https://arxiv.org/abs/2210.12283 ;
DeepSeek-Prover-V2: arXiv:2504.21801: https://arxiv.org/abs/2504.21801

### C3. LeanDojo / ReProver
**Idea.** LeanDojo extracts a dataset of ~98,734 theorems (with their tactic and premise annotations) from Mathlib and provides a
programmatic interaction environment (tactic-state in, tactic out) so an LLM trains/evaluates
as an *agent*. ReProver retrieves candidate premises (Dense-Passage-Retriever-style, cosine
similarity between current state and a premise-embedding library) and conditions tactic
generation on state + retrieved premises, instead of relying on parametric recall of exact
lemma names.
**Mechanism.** A **retrieval pre-pass**: embed the current goal, pull top-k candidates from a
vector index, *then* attempt a tactic — this is what `mathlib-scout` already does once per
challenge; the generalization is dispatching it **per stuck subgoal**, not just once up front
(→ D5). LeanDojo's hard train/test split by novel-premise-usage is also a useful **eval
discipline**: when grading `mathlib-scout`/`lean-suggest` quality, test on goals needing lemmas
not already in recent `PROOF_PATTERNS.md` entries (→ D17).
**Citation.** Yang et al., NeurIPS 2023: https://arxiv.org/abs/2306.15626 ; code:
https://github.com/lean-dojo/ReProver ; reported Pass@1 51.2% (ReProver) vs. 47.6%
(non-retrieval) vs. 29.0% (GPT-4 zero-shot) on the "random" split, at 120 vs. 1000+ GPU-hours.

### C4. Search algorithms — best-first, HTPS, budgets
**Idea.** Frame "find a proof" as search over a tree/hypergraph of proof states scored by a
learned value/policy. Best-first search (GPT-f, Polu & Sutskever 2020) always expands the
highest-scoring open node, under a hard budget (128 goal expansions, ≤16–32 tactic candidates
per expansion). **HyperTree Proof Search** (HTPS, Meta's Evariste, Lample et al. 2022) is
MCTS-inspired but built for **hypergraphs**: a tactic spawning multiple subgoals is one AND-node
requiring all children solved, not alternative OR-branches — it maintains a partial proof
hypertree and follows arg-max of a search policy from root to frontier. BFS-Prover (2025) shows
well-engineered best-first search is competitive with HTPS at scale.
**Mechanism.** (1) Explicit **AND/OR distinction** — a tactic splitting into 3 subgoals is one
hyperedge requiring all 3 closed, not 3 independent alternatives (→ D1's ledger schema must
encode this, not just a flat list). (2) A **hard expansion budget per proof attempt**, not per
tactic call, so a stuck branch can't silently consume unbounded compute (→ D2, D9). (3)
Score-and-reorder the **frontier**, not just the current node — abandon a locally-plausible but
globally-stuck branch for a promising sibling; this is stall detection/recovery for free if the
frontier is kept, not thrown away after each attempt (→ D6, D8).
**Citations.** GPT-f: Polu & Sutskever, arXiv:2009.03393: https://arxiv.org/pdf/2009.03393 ,
first ML system to contribute accepted proofs to a live formal-math library (Metamath):
https://openai.com/index/generative-language-modeling-for-automated-theorem-proving/ ; HTPS:
Lample et al., NeurIPS 2022, arXiv:2205.11491: https://arxiv.org/pdf/2205.11491 ; code (partial,
reference only): https://github.com/facebookresearch/Evariste ; BFS-Prover: arXiv:2502.03438:
https://arxiv.org/pdf/2502.03438

---

## Part D — Synthesis: mechanisms mapped to our system

Merged and deduplicated across both briefs, ranked by implementability. `Status` marks whether
the system already has a partial version (build on it) or nothing yet (build it). `Feeds`
names the artifact each mechanism was meant to land in.

| # | Mechanism | Source(s) | Concrete implementation here | Status | Feeds |
|---|---|---|---|---|---|
| D1 | **Subgoal ledger as an AND/OR DAG** — node = statement, edges = dependency, status enum, assigned tier/agent; a tactic yielding N subgoals is one hyperedge requiring all N closed | A3, B1/B2, C4 | Schema for the ledger (`.proof-ledger/<attempt_id>.json`); node shape mirrors blueprint's `\uses` graph | Partial — `blueprint-leaves.sh`/`blueprint-scout` do this for *external* blueprints only | Part E (schema), `proof-ledger.sh` |
| D2 | **Progress-sensitive budget** — replace the fixed attempt cap with a per-step progress-delta gate (smaller/more specific/closer-to-known-lemma?); gate continue/replan/escalate/abandon on it | A8, C4 (GPT-f's 128-expansion budget) | Total-budget tracked across the whole subgoal tree, not per-call | None — today's cap is fixed (2 attempts Sonnet, 3 Opus, count-based only) | `proof-trajectory-keeper` |
| D3 | **Attempted-and-failed log per goal** — durable negative-result record, read before the next attempt/escalation | A6 | Extend `PROOF_PATTERNS.md` (or a sibling dead-ends file, never built; dead ends went into the ledger instead) fed automatically from BLOCKED reports | Partial — BLOCKED reports carry this info but are transient, not persisted | `proof-ledger.sh`, extends `log-pattern.sh` |
| D4 | **Method+critic architecture** — preconditioned tactics; on failure a pattern-matched critic proposes a specific patch, not blind retry | A2 | The B3 tactic table *is* the methods library; critics = failure-shape → patch rules (e.g. "IH too weak" → generalize) | None | `proof-strategist` |
| D5 | **Retrieval pre-pass, per stuck subgoal** — embed goal, pull top-k lemma candidates, then attempt | C3 (ReProver, LeanSearch v2) | `mathlib-scout` dispatched per-stuck-subgoal by the trajectory-keeper, not just once at scaffold time | Partial — exists once per challenge | `proof-trajectory-keeper` |
| D6 | **Choice-point-level backtracking** — retry at the right granularity (swap a lemma vs. re-decompose) instead of restarting from scratch | A6, C4 (frontier re-ranking) | Trajectory-keeper models a choice-point stack (tactic/lemma/decomposition) | None | `proof-trajectory-keeper` |
| D7 | **Mandatory look-back gate** — post-SOLVED: "is this reusable/generalizable?", force-fed to `PROOF_PATTERNS.md` | A1 | Make `log-pattern.sh` a required step of the SOLVE path, not opt-in | Partial — script exists, not enforced | `/prove`, `/climb` |
| D8 | **Stuck-detection trigger** — N failed attempts with no progress on the same decomposition forces a mode switch (escalate or re-decompose) | A7, A8, C4 | Core job of the trajectory-keeper: detect stall, not just count attempts | None | `proof-trajectory-keeper` |
| D9 | **Escalation triggers keyed to search exhaustion, not attempt count** — escalate when a tier's own search options run out | C4 | Reframe the Haiku→Sonnet→Opus→Fable ladder's escalation condition | Partial — ladder exists, trigger is a fixed count | `proof-trajectory-keeper`, CLAUDE.md routing |
| D10 | **Mandatory small-case specialization gate** — cheap falsification/orientation pass before formalizing | A5 | Make `conjecture-scout` dispatch non-optional before scaffold for conjectural/parametrized goals | Partial — agent exists, dispatch optional | `/prove`, `/climb` |
| D11 | **Generalize-then-induct retry** — auto-attempt a generalized statement when direct induction stalls on IH-too-weak, before tier escalation | A5, A2 (Bundy critics) | A specific critic rule in `proof-strategist` | None | `proof-strategist` |
| D12 | **Explicit invariant-search sub-step** — for recursive/iterative goals, search for a preserved/monotone quantity before attacking induction | A4 | New step in `lean-prover`'s method table for induction-shaped goals | None | `proof-strategist` / agent update |
| D13 | **White-box, inspectable tactic set** — keep the B3 decision table explicit rather than an opaque hammer call, so a stall is diagnosable ("which rule almost fired") | C3 (Aesop) | Already the repo's style (B3 table); formalize as the methods library for D4 | Exists (informally) | `proof-strategist` |
| D14 | **Checkpoint on named sub-goals** (`have`/`suffices`/`calc`) — re-plan backs up to the nearest checkpoint, not the theorem root | B4, A6 | Ledger nodes (D1) correspond 1:1 to `have`/`suffices` names in the actual Lean file | None | Part E (schema) |
| D15 | **Decompose-then-fill two-tier split** — a planner proposes named subgoal stubs; a narrower-context filler proves one at a time | C2 (DeepSeek-Prover-V2), B1 | `proof-strategist` (planner) → `lean-prover` (filler); matches existing Haiku→Sonnet boundary | None (new agent) | `proof-strategist` |
| D16 | **Symmetry/WLOG reduction as an explicit planning step** — check before decomposing | B4 | `proof-strategist` checks for a `wlog`-shaped reduction first | None | `proof-strategist` |
| D17 | **Novel-premise generalization eval** — grade retrieval tools on goals needing lemmas not already in recent patterns | C3 (LeanDojo split) | Periodic eval harness for `mathlib-scout`/`lean-suggest.sh` | None | Later (meta-scoper backlog) |
| D18 | **Guilty-lemma localization on vacuity/counterexample** — repair the specific falsified leaf, not the whole subgoal tree | A6 (Lakatos) | Extend `proof-auditor`'s verdict to point at a specific ledger node; route re-proof there | Partial — auditor flags fidelity issues, doesn't localize to a ledger node yet (at the time of writing no ledger existed; `scripts/proof-ledger.sh` now provides one) | `proof-ledger.sh` + proof-auditor update |
| D19 | **Draft-sketch-prove staging** — cheap go/no-go + closed form before formalizing | C2 (DSP), A5 | `conjecture-scout` already plays this role; formalize as mandatory Stage 0 (same as D10) | Partial | `/prove`, `/climb` |
| D20 | *(watch item, low priority)* AlphaProof-style test-time adaptation / self-generated curriculum | C1 | No concrete near-term action — flagged for `meta-scoper` to reconsider once the ledger/trajectory-keeper exist | Speculative | `meta-scoper` backlog |

### Reading order for Part E

Build the subgoal-ledger schema (D1, D14) first — nearly everything else (D2, D3, D5, D6, D8,
D9, D18) either writes to it or reads from it. The `proof-strategist` (D4, D11, D12, D13, D15,
D16) and `proof-trajectory-keeper` (D2, D3, D6, D8, D9) agents are two different *roles* consuming
the same ledger: strategist decomposes and picks methods, keeper watches budget/progress/stalls
and decides continue/replan/escalate/abandon — keep that separation of concerns when writing
their specs.

---

## Part E — The trajectory-management methodology (synthesis)

> This is the **DEPTH-control** layer, which was missing when this was written: proving was then
> width-wise only (`/climb` swarm). It adds a project-management loop around a *single hard target* so an attempt never drifts or
> thrashes. It is the concrete spec that the agents and `scripts/proof-ledger.sh` implement,
> assembled from the D-mechanisms above. **Lean remains the sole arbiter**: a subgoal is `solved`
> only when `check-proof.sh` compiles it clean with no `sorry`.

### E1. The four-role control loop

One loop wraps one hard target; each role is an existing or new component, not a monolith.

1. **PLAN** — `proof-strategist` (Opus, advisory): understand + plan (Pólya A1), run the
   small-case specialization gate (D10/D19), propose a **subgoal DAG** leaf-first (D15), pick an
   attack + tier + tool per subgoal from the method table (B3/D4/D13), and **initialize the
   ledger** as a `sorry`-stub skeleton (B1).
2. **TRACK** — `scripts/proof-ledger.sh` + the ledger file (D1/D14): durable record of subgoals,
   status, attempts, tier, `goal_delta`, dead-ends, decisions.
3. **MANAGE** — `proof-trajectory-keeper` (Opus, **advisory**): read the ledger, enforce the
   budget (D2), detect stall/thrash/drift (D8/D6), and emit the critic-based **decision** (E4).
4. **ARBITRATE** — Lean via `check-proof.sh`/`verify-all.sh`: a subgoal flips to `solved` only on
   a clean compile.

> **Dispatch constraint (important).** A dispatched subagent cannot spawn sub-subagents. So
> `proof-strategist` and `proof-trajectory-keeper` are **advisory** (like `proof-auditor`): they
> read state and *return* a plan / a decision. The **orchestrator** — the main session running
> `/prove` or `/climb` — is what actually *executes* each step: it dispatches `lean-prover`
> (+opus) for a leaf attempt, records the result to the ledger, re-invokes the strategist on a
> DECOMPOSE/RE-PLAN, and calls `proof-auditor` at the end. The keeper is the PM that says "do X
> next"; the orchestrator does X.

Separation of concerns (per the reading-order note): the **strategist decomposes and picks
methods**; the **keeper watches budget/progress/stalls and decides** continue/replan/escalate/
abandon. Two roles, one shared ledger.

### E2. Subgoal ledger schema (AND/OR hypertree — D1, D14)

One JSON file per attempt, gitignored under the project home (e.g. `.proof-ledger/<attempt_id>.json`).

```jsonc
{
  "attempt_id": "C0019Foo-20260909",
  "target": { "module": "MathProof.Challenges.C0019Foo", "theorem": "foo", "statement": "…" },
  "status": "active | solved | blocked | abandoned",
  "budget": { "total_attempts": 12, "spent": 0, "per_subgoal_cap": 4, "wall_clock_min": 90 },
  "plan_version": 1,
  "subgoals": [{
    "id": "sg1", "goal": "…",
    "kind": "leaf | node",
    "deps": ["sg2", "sg3"],            // AND: all must be solved (one hyperedge) — C4
    "approaches": ["induction n", "strong induction"], // OR: alternatives kept on the frontier, not deleted — C4/D6
    "status": "open | in_progress | solved | dead | deferred",
    "tier": "scout | sonnet | opus | apex",
    "attempts": [
      { "n": 1, "tier": "sonnet", "sketch": "induction n; ring",
        "result": "fail", "error": "…", "goal_delta": 0 }   // delta < 0 = progress — D2/A8
    ],
    "dead_ends": ["approach X: why it failed"],   // read before the next attempt — never repeat — D3/A6
    "checkpoints": ["have h1 : …", "calc step 2"],// re-plan backs up to nearest, not to root — D14/B4
    "notes": "chosen invariant / generalization"
  }],
  "decisions": [{ "at": "ISO8601", "trigger": "stall", "decision": "escalate sonnet→opus",
                  "subgoal": "sg1", "rationale": "…" }],
  "dead_end_log": []                              // global negative-results record — D3
}
```

Ledger nodes correspond **1:1 to `have`/`suffices` names in the actual Lean file** (D14): the
ledger and the `sorry`-stub skeleton are two views of the same decomposition.

### E3. Budget model (progress-sensitive — D2, A8, C4)

- `total_attempts` — hard cap on prover dispatches for the *whole* target (runaway-spend guard;
  GPT-f's 128-expansion budget, scaled to our tiers).
- `per_subgoal_cap` — attempts on ONE subgoal before the keeper **must** decide (the key
  anti-thrash lever; the upgrade over today's fixed 2/3-attempt count).
- `goal_delta` per attempt — change in (open goals + `sorry`s). **Progress = delta < 0.** The
  budget gates on *measured progress*, not just the counter.
- (optional) tier-weighted spend — scout cheap, opus/apex expensive; escalation is keyed to
  **search exhaustion**, not wall-clock (D9).

### E4. Stall / thrash / drift detection + the decision ladder

**Detection (D8/D6):**
- **STALL** — last *K* attempts on a subgoal all `goal_delta ≥ 0`, or `per_subgoal_cap` hit.
- **THRASH** — a normalized tactic sketch repeats, or an already-logged dead-end is re-derived, or
  two approaches cycle with no progress.
- **DRIFT** — attempts stop matching any planned approach → re-anchor to the plan.

**Decision ladder (critic-based — D4; cheapest / most-likely-first).** On a STALL the keeper picks
exactly one, matching the error *signature* (Bundy critic A2), never a blind retry:

| # | Decision | Fire when (signature) | D-ref |
|---|----------|-----------------------|-------|
| 1 | **ANCHOR** — re-run `mathlib-scout`/`lean-suggest` on the refined goal | "unknown identifier / no applicable lemma"; cheap, first | D5 |
| 2 | **PENULTIMATE** — "what one lemma closes this if the rest held?" (`exact?`/`apply?`) | goal one step from a known result | A7 |
| 3 | **ESCALATE tier** — same goal, higher model (sonnet→opus→apex) | seems provable, tier's search exhausted | D9 |
| 4 | **INVARIANT-SEARCH** — find a preserved/monotone quantity, strengthen the IH | recursive goal, induction step won't close | D12 |
| 5 | **GENERALIZE** — prove a stronger/more-general lemma | induction fails "IH too weak" | D11 |
| 6 | **SPECIALIZE** — prove a concrete case first to reveal structure | stuck on the general case, no foothold | A5 |
| 7 | **DECOMPOSE** — strategist breaks the subgoal into children | "no single tactic", compound goal | D15 |
| 8 | **GUILTY-LEMMA REPAIR** — localize + fix the falsified leaf | auditor/`lean-eval` found it false/vacuous | D18 |
| 9 | **ABANDON subgoal** — mark `dead`, log why, re-plan parent | alternatives exhausted at right granularity | D6 |
| 10| **ABANDON target** — write BLOCKED report **with the full ledger** | `total_attempts` exhausted | D3 |

Cheap symmetry check **WLOG** (D16) and the **decompose-then-fill** split (D15) are applied at
PLAN time by the strategist, before the ladder ever runs.

### E5. Re-plan triggers

A subgoal STALLs at cap · a leaf is found **false** (`conjecture-scout`/`lean-eval`) → re-plan the
parent (bad decomposition) · a Mathlib lemma collapses several subgoals → simplify · budget ≥50%
spent with <50% subgoals solved → re-plan. Each re-plan bumps `plan_version`; superseded subgoals
are `deferred`, not deleted (frontier kept — C4/D6).

### E6. Look-back gate (mandatory, post-SOLVED — D7/A1)

Distinct from `proof-auditor`. After a clean audit, ask "is this method reusable / does it
generalize?" and force a `scripts/log-pattern.sh` row (and record the abandoned approaches as ledger dead ends
with `proof-ledger.sh dead-end`, if the winning path went through any — D3). The most-skipped, highest-leverage
step; make it part of the SOLVE path, not opt-in.

### E7. Build map (what implements what)

| Role / mechanism | Component | Build |
|---|---|---|
| PLAN, decompose, generalize/specialize, WLOG, method-pick, init ledger | **`proof-strategist`** (Opus) | built: `.claude/agents/proof-strategist.md` |
| MANAGE — budget, stall/thrash, critic decision (advisory; orchestrator executes the dispatch) | **`proof-trajectory-keeper`** (Opus) | built: `.claude/agents/proof-trajectory-keeper.md` |
| TRACK — ledger init/add/attempt/mark/dead-end/stall-check/status | **`scripts/proof-ledger.sh`** | built |
| EXECUTE a leaf attempt | `lean-prover` → `lean-prover-opus` | reuse |
| ANCHOR / retrieval pre-pass | `mathlib-scout`, `mathlib-search.sh`, `lean-suggest.sh` | reuse |
| Small-case gate / truth-check | `conjecture-scout`, `lean-eval.sh`, `wolfram.sh` | reuse |
| ARBITRATE | `check-proof.sh`, `verify-all.sh` | reuse |
| Final audit + guilty-lemma flag | `proof-auditor` (+ ledger-node pointer) | reuse/extend |
| Look-back flywheel | `log-pattern.sh` → `PROOF_PATTERNS.md` (dead ends live in the ledger) | reuse |
| Single-target DEPTH loop | **`/prove`** (extended) | extend |
| Batch: HARD→depth, EASY→width swarm | **`/climb`** (extended) | extend |

The two new agents sit *above* the model-tier ladder as plan/manage roles; the ladder and
Lean-is-arbiter discipline are unchanged.
