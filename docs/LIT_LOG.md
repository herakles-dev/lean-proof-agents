# LIT_LOG — literature pre-pass log

One row per problem searched (via `scripts/lit-search.sh` / the `lit-scout` agent), so a target is
never re-searched from scratch (the problem database can lag the literature). Verdict wording
is **"no contradiction found as of <date>"**, never a bare "open" (papers rarely cite the problem #).

| Date | Problem | Verdict | db_last_update | Notes / refs |
|---|---|---|---|---|
| 2026-09-16 | Erdős #647 | OPEN-CONFIRMED (no contradiction found) | 2025-08-31 | `verifiable` / £25; no paper resolves the existence question (hits were Ramanujan-τ / divisor-function noise). Certified no-witness in `[25,60)` at the time (C0042), since extended to `[25,3000)` (C0044); `sweep` no-witness ≤ 2·10⁶ (searched, not certified). |
| 2026-09-16 | Erdős #64 | LIKELY-SEARCHED(≤58) | — | Erdős–Gyárfás. lit-scout surfaced a 60-vertex lower-bound paper with a **certified exhaustive search ≤58 vertices** → any new search must start above 58; far beyond the reach of the v1 certificate checker. Re-scope before attempting. |
