export const meta = {
  name: 'swarm-prove',
  description: 'Parallel-leaf proof swarm (lean-proof-agents /swarm Phase ③): plan → wave-scheduled parallel prove → audit → assemble+check',
  whenToUse:
    'A hard Lean proof whose proof-strategist DAG has ≥2 independent leaves and ≥1 real dependency level. Automates the /swarm async-keeper (SWARM_SPEC F3): DAG waves dispatch as deps land, no manual orchestrator loop. The orchestrator still runs the AUTHORITATIVE proof-auditor + verify-all and is the SOLE committer (hub-and-gate).',
  phases: [
    { title: 'Plan', detail: 'proof-strategist → subgoal DAG (skipped when args.leaves supplied)' },
    { title: 'Prove', detail: 'DAG-wave-scheduled parallel lean-prover per independent leaf (Sonnet→Opus escalation)' },
    { title: 'Audit', detail: 'parallel proof-auditor per leaf (skipped when args.auditLeaves === false)' },
    { title: 'Assemble', detail: 'integrator: bank.sh add/verify/assemble + check-proof --all (mechanical, re-gated)' },
  ],
};

// Runtime: this script is not a standalone Node program. It runs under Claude Code's Workflow tool,
// which provides the globals `args`, `phase`, `log`, `agent`, `parallel` (plus top-level await/return).
// Without that tool, follow the manual loop in .claude/skills/swarm/SKILL.md instead.
// Precondition: the bank must already exist — run `scripts/bank.sh init <attempt>` first.
// ───────────────────────── inputs (args) ─────────────────────────
// {
//   attempt:         "C0048Foo"           // REQUIRED — CamelCase bank id (MathProof.Bank.<attempt>)
//   target:          "C0048Foo"           // challenge module for assemble (default: attempt)
//   leaves:          [{name,statement,deps:[names],exact?,note?}]  // supply the DAG directly …
//   strategistPrompt:"…"                  // … OR let proof-strategist produce it
//   model:           "haiku"              // default model for leaf provers (omit → agent-definition tier)
//   auditLeaves:     true|false           // per-leaf proof-auditor pass (default true)
// }
// A leaf's `deps` are the names of OTHER leaves in this DAG it builds on ([] for a base leaf).
// `exact` (optional) = the full Lean declaration to write verbatim (used for deterministic mechanics tests).
const A = args || {};
const attempt = A.attempt;
if (!attempt) throw new Error('swarm-prove: args.attempt (CamelCase bank id) is required');
if (!/^[A-Za-z][A-Za-z0-9]*$/.test(attempt)) throw new Error(`swarm-prove: attempt must be one CamelCase identifier, got "${attempt}"`);
const target = A.target || attempt;
const defaultModel = A.model; // undefined → each agent uses its own definition-tier
const auditLeaves = A.auditLeaves !== false;

// omit an undefined model so the agent falls back to its definition tier (Agent-tool semantics)
function O(o) { const x = { ...o }; if (x.model === undefined) delete x.model; return x; }

// ───────────────────────── schemas ─────────────────────────
const DAG_SCHEMA = {
  type: 'object',
  properties: {
    leaves: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          name: { type: 'string', description: 'CamelCase leaf id' },
          statement: { type: 'string', description: 'exact Lean theorem/lemma signature, no proof' },
          deps: { type: 'array', items: { type: 'string' }, description: 'names of other leaves this one builds on' },
          note: { type: 'string' },
        },
        required: ['name', 'statement', 'deps'],
      },
    },
  },
  required: ['leaves'],
};
const LEAF_SCHEMA = {
  type: 'object',
  properties: {
    name: { type: 'string' },
    status: { type: 'string', enum: ['SOLVED', 'BLOCKED'] },
    path: { type: 'string' },
    axioms: { type: 'array', items: { type: 'string' } },
    note: { type: 'string' },
  },
  required: ['name', 'status'],
};
const AUDIT_SCHEMA = {
  type: 'object',
  properties: {
    name: { type: 'string' },
    verdict: { type: 'string', enum: ['PASS', 'FAIL'] },
    reason: { type: 'string' },
  },
  required: ['name', 'verdict'],
};
const ASSEMBLE_SCHEMA = {
  type: 'object',
  properties: {
    assembled_path: { type: 'string' },
    verify_ok: { type: 'boolean' },
    checkproof_ok: { type: 'boolean' },
    axioms: { type: 'array', items: { type: 'string' } },
    log: { type: 'string' },
  },
  required: ['verify_ok', 'checkproof_ok'],
};

// ───────────────────────── 1. Plan ─────────────────────────
phase('Plan');
let leaves = A.leaves;
if (!leaves || !leaves.length) {
  if (!A.strategistPrompt) throw new Error('swarm-prove: supply args.leaves OR args.strategistPrompt');
  log('No DAG supplied — dispatching proof-strategist to produce one.');
  const plan = await agent(
    `${A.strategistPrompt}\n\nEmit the subgoal DAG for bank attempt "${attempt}". For each leaf give: a CamelCase name, its EXACT Lean statement (theorem/lemma signature, no proof), and deps = the names of the OTHER leaves in this DAG it builds on (empty for base leaves). A leaf whose statement combines others MUST list those others in deps.`,
    O({ label: 'strategist', phase: 'Plan', schema: DAG_SCHEMA, agentType: 'proof-strategist' })
  );
  if (!plan || !plan.leaves || !plan.leaves.length) throw new Error('proof-strategist returned no DAG');
  leaves = plan.leaves;
}
leaves = leaves.map((l) => ({ name: l.name, statement: l.statement, deps: l.deps || [], exact: l.exact, note: l.note }));
const names = new Set(leaves.map((l) => l.name));

// topological levels; deps that are NOT leaves of this DAG are treated as external (already satisfied)
function computeWaves(ls) {
  const done = new Set();
  const waves = [];
  let rem = ls.slice();
  while (rem.length) {
    const ready = rem.filter((l) => l.deps.every((d) => done.has(d) || !names.has(d)));
    if (!ready.length) throw new Error('swarm-prove: dependency cycle or unsatisfiable deps among leaves: ' + rem.map((l) => l.name).join(', '));
    ready.forEach((l) => done.add(l.name));
    waves.push(ready);
    rem = rem.filter((l) => !done.has(l.name));
  }
  return waves;
}
const waves = computeWaves(leaves);
log(`DAG: ${leaves.length} leaves in ${waves.length} waves → ${waves.map((w, i) => `W${i + 1}[${w.map((l) => l.name).join(',')}]`).join(' → ')}`);

// leaf-prover prompt — the /swarm "Leaf-prover spawn contract" as a runbook
function leafPrompt(leaf) {
  const depImports = leaf.deps.filter((d) => names.has(d)).map((d) => `import MathProof.Bank.${attempt}.${d}`);
  const importBlock = ['import MathProof.Basic', ...depImports].join('\n');
  const file = `MathProof/Bank/${attempt}/${leaf.name}.lean`;
  const body = leaf.exact
    ? `Write EXACTLY this file (mechanics-validation leaf — do NOT deviate):\n\n\`\`\`lean\n${importBlock}\n\nnamespace MathProof.Bank.${attempt}\n\n${leaf.exact}\n\nend MathProof.Bank.${attempt}\n\`\`\``
    : `Prove this leaf. Write ${file} with this skeleton, replacing \`sorry\` with a real proof:\n\n\`\`\`lean\n${importBlock}\n\nnamespace MathProof.Bank.${attempt}\n\n${leaf.statement} := by\n  sorry\n\nend MathProof.Bank.${attempt}\n\`\`\``;
  return [
    `You are a swarm leaf-prover (see the /swarm skill, "Leaf-prover spawn contract"). Bank attempt: ${attempt}. Leaf: ${leaf.name}.`,
    ``,
    `WRITE TARGET (create/overwrite exactly this path): ${file}`,
    ``,
    body,
    ``,
    `Rules:`,
    `- The lemma MUST be PUBLIC (no \`private\` — module-scoped, invisible across bank modules). Cross-leaf refs use BARE names.`,
    `- Import ONLY MathProof.Basic + the SPECIFIC dep leaves shown above — NEVER the "${attempt}" aggregator (it cycles once this leaf is added).`,
    `- NO \`native_decide\`; NO \`sorry\` in the final file; 2-attempt cap, then stop and report BLOCKED.`,
    `- Self-verify: \`lake build MathProof.Bank.${attempt}.${leaf.name}\` clean, then \`scripts/check-proof.sh MathProof.Bank.${attempt}.${leaf.name} --all\` (axioms ⊆ {propext, Classical.choice, Quot.sound}).`,
    ``,
    `Return: name="${leaf.name}", status SOLVED|BLOCKED, path, axioms (from #print axioms), one-line note.`,
  ].join('\n');
}

// ───────────────────────── 2. Prove (wave-scheduled) ─────────────────────────
// Sequential over waves (a wave-N+1 leaf imports wave-N leaf files that must exist on disk first —
// a genuine cross-item barrier), parallel WITHIN each wave. This IS the automated async-keeper (F3).
phase('Prove');
const proven = {};
for (let w = 0; w < waves.length; w++) {
  const wave = waves[w];
  log(`Wave ${w + 1}/${waves.length}: proving ${wave.map((l) => l.name).join(', ')}`);
  const results = await parallel(
    wave.map((leaf) => async () => {
      let r = await agent(leafPrompt(leaf), O({ label: `prove:${leaf.name}`, phase: 'Prove', schema: LEAF_SCHEMA, agentType: 'lean-prover', model: defaultModel }));
      if ((!r || r.status !== 'SOLVED') && !leaf.exact) {
        log(`Leaf ${leaf.name} not SOLVED at Sonnet tier — escalating to lean-prover-opus.`);
        const r2 = await agent(
          leafPrompt(leaf) + '\n\nESCALATION: a Sonnet prover did not close this. Search deeper / decompose, but keep the SAME statement and the SAME write target.',
          { label: `escalate:${leaf.name}`, phase: 'Prove', schema: LEAF_SCHEMA, agentType: 'lean-prover-opus' }
        );
        if (r2 && r2.status === 'SOLVED') r = r2;
      }
      return r;
    })
  );
  wave.forEach((leaf, i) => { proven[leaf.name] = results[i]; });
}
const solved = leaves.filter((l) => proven[l.name] && proven[l.name].status === 'SOLVED');
const blocked = leaves.filter((l) => !proven[l.name] || proven[l.name].status !== 'SOLVED');
if (blocked.length) log(`⚠ BLOCKED leaves: ${blocked.map((l) => l.name).join(', ')} — assembly skipped; orchestrator re-strategizes these.`);

// ───────────────────────── 3. Audit (advisory; authoritative auditor runs on the assembled module) ─────────
let audits = [];
if (auditLeaves && solved.length) {
  phase('Audit');
  audits = await parallel(
    solved.map((leaf) => () =>
      agent(
        `Adversarially audit bank leaf ${leaf.name} of attempt ${attempt} (file MathProof/Bank/${attempt}/${leaf.name}.lean). Check: (1) no sorry / native_decide; (2) #print axioms ⊆ {propext, Classical.choice, Quot.sound}; (3) the statement is NON-VACUOUS and faithfully expresses "${leaf.statement}". Build with \`lake build MathProof.Bank.${attempt}.${leaf.name}\`. Return name, verdict PASS|FAIL, reason.`,
        { label: `audit:${leaf.name}`, phase: 'Audit', schema: AUDIT_SCHEMA, agentType: 'proof-auditor' }
      )
    )
  );
}
const auditFails = audits.filter(Boolean).filter((a) => a.verdict === 'FAIL');

// ───────────────────────── 4. Assemble (mechanical + re-gated; NOT a commit) ─────────────────────────
let assembled = null;
if (!blocked.length && !auditFails.length) {
  phase('Assemble');
  const orderedNames = waves.flat().map((l) => l.name);
  assembled = await agent(
    [
      `You are the swarm integrator for bank attempt "${attempt}" → target challenge module "${target}". All leaves are proven and on disk under MathProof/Bank/${attempt}/. Run these steps IN ORDER, then report:`,
      `1. For each leaf in this dependency order [${orderedNames.join(', ')}], run sequentially (NEVER in parallel — they share the blackboard aggregator file): \`scripts/bank.sh add ${attempt} <LeafName> MathProof/Bank/${attempt}/<LeafName>.lean\``,
      `2. \`scripts/bank.sh verify ${attempt}\` — every leaf builds, no sorry, trusted-trio axioms. If it fails, STOP and report verify_ok=false with the tail of the log.`,
      `3. \`scripts/bank.sh assemble ${attempt} ${target}\` — inlines leaves (topological order) into MathProof/Challenges/${target}.lean.`,
      `4. \`lake build MathProof.Challenges.${target}\` then \`scripts/check-proof.sh ${target} --all\`. Report checkproof_ok + the #print axioms output.`,
      ``,
      `Do NOT edit MathProof.lean, do NOT git commit, do NOT run verify-all.sh — those are the orchestrator's job (hub-and-gate). Return: assembled_path, verify_ok, checkproof_ok, axioms, log (last ~15 lines of any failure, else empty).`,
    ].join('\n'),
    O({ label: 'assemble', phase: 'Assemble', schema: ASSEMBLE_SCHEMA, agentType: 'general-purpose', model: defaultModel })
  );
}

// ───────────────────────── return (orchestrator gates + commits from here) ─────────────────────────
return {
  attempt,
  target,
  waves: waves.map((w) => w.map((l) => l.name)),
  leaves: leaves.map((l) => ({ name: l.name, status: (proven[l.name] && proven[l.name].status) || 'MISSING', axioms: (proven[l.name] && proven[l.name].axioms) || [] })),
  blocked: blocked.map((l) => l.name),
  audits: audits.filter(Boolean),
  auditFails: auditFails.map((a) => a.name),
  assembled,
  gate_ready: !!(assembled && assembled.verify_ok && assembled.checkproof_ok && !blocked.length && !auditFails.length),
  next: 'Orchestrator: proof-auditor on the assembled module → wire import into MathProof.lean → verify-all → commit → log-pattern → bank.sh clean.',
};
