/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import groovy.transform.CompileStatic
import verification.Z3Backend

/**
 * Phase 195 — the <b>perf-budget assertion</b>: the project's flagged compilation-slowdown risk
 * ("Z3 calls take 10–100 ms each"), turned from a documented risk into an asserted invariant, the same
 * move the runtime rung's coverage canary made for silent tier drift.
 *
 * <p>The primary ceilings are <b>deterministic counters</b>, not wall-clock: given the corpus and the
 * encoder, the number of solver checks issued and distinct VCs built is reproducible on any machine
 * (up to ~1–2% jitter from test-class ordering in the shared JVM — the ceilings' headroom dwarfs it) —
 * an encoder change that starts issuing double the checks (a lost cache key, a duplicated discharge
 * pass, an axiom re-mint) trips the budget on the slowest CI runner and the fastest laptop alike.
 * Wall-clock appears only as (a) a generous single-check backstop against a pathological VC (a
 * quantifier explosion shows up as one enormous check long before machines disagree about it) and
 * (b) a report line for humans. UNKNOWN results get a small allowlisted ceiling: a hard-UNKNOWN is a
 * capability regression signal, but a slow machine can legitimately time a hard VC out.
 *
 * <p>Ceilings are sized ~25–30% above the measured full-{@code check} figures — headroom for organic
 * per-slice growth (a new case group adds tens of checks, not thousands); a trip means either a real
 * regression or a deliberate corpus jump, and re-basing the constant is a one-line, reviewed change.
 */
@CompileStatic
class PerfBudget {

    /** Total solver {@code check()} calls (cache hits + real solves). Deterministic. */
    // Re-based 2026-10-29 (after Phase 464): `test` measured 16,396 checks / 10,331 distinct against 16,500 / 11,000 —
    // 65 phases of corpus growth since Phase 399's 13,189 / 8,516, about 50 checks a phase (new case groups, and the
    // witness re-checks: Phase 464's along the runs through a loop with no invariant). Not measured per phase.
    // (2026-10-24: 16,500 at 13,189.)
    // Re-based 2026-10-24 (Phase 399): the witness searches of Phases 386–398 took `verify` from 11,423 checks / 7,369
    // distinct to 12,832 / 8,462 (the `test` run measured 13,588 / 8,573 before Phase 399's path de-duplication). The
    // growth, by phase: 392's preservation witness +461 / +374, 397's nested-entry witness and depth +285 / +234, 398's
    // second pass +731 / +370 — of which Phase 399's de-duplication won back 360 / 56 (the second pass re-tried the
    // first's paths: their assume markers are rebuilt, so equal paths compared unequal); the other phases +60 each or less.
    // After it, `test` measured 13,189 / 8,516.
    // (2026-10-23: 15,000 at 11,379; 2026-10-22: 13,000 at 10,413.)
    static final long MAX_CHECK_CALLS = 21_000

    /** Distinct VCs actually solved (the cache-miss population). Deterministic. */
    static final long MAX_DISTINCT_VCS = 13_500   // re-based with it (10,331 distinct; 2026-10-24: 11,000 at 8,516; 2026-10-23: 9,500 at 7,367)

    /** UNKNOWN results (solver gave up / timed out). The corpus carries a handful of hard VCs plus the
     *  Phase 203/204 inconsistency canaries (recurrence-axiom refutes that intentionally time MBQI out —
     *  measured 24 after those landed); re-based with headroom. Re-based 2026-10-23: Phases 375–379 add cases that are
     *  undecided by design (a sum claim whose refutation needs a model of the sum's quantified axioms: the ClearSplit
     *  fold without its hypothesis, Phase 379's four bounds the elements don't give); `test` measured 43. */
    static final long MAX_UNKNOWN = 55

    /** Pathological single-check backstop — machine-dependent, hence deliberately enormous. */
    static final long MAX_SINGLE_CHECK_MS = 30_000

    static String report() {
        long hits = Z3Backend.vcCacheHits(), misses = Z3Backend.vcCacheMisses()
        "perf: ${hits + misses} solver checks (${misses} solved / ${hits} cached), " +
            "${Z3Backend.solverMsTotal()} ms in Z3 (max ${Z3Backend.solverMsMax()} ms, " +
            "${Z3Backend.slowCheckCount()} over 500 ms), ${Z3Backend.unknownResults()} UNKNOWN" +
            (Z3Backend.effectiveBudgetMax() > 0 ? ", budget up to ${Z3Backend.effectiveBudgetMax()} ms" : '')
    }

    /** Assert the ceilings; the message carries the full report so a trip is self-explanatory. */
    static void assertBudget() {
        String r = report()
        long calls = Z3Backend.vcCacheHits() + Z3Backend.vcCacheMisses()
        assert calls <= MAX_CHECK_CALLS               : "check-call ceiling exceeded — ${r}"
        assert Z3Backend.vcCacheMisses() <= MAX_DISTINCT_VCS : "distinct-VC ceiling exceeded — ${r}"
        assert Z3Backend.unknownResults() <= MAX_UNKNOWN     : "UNKNOWN ceiling exceeded — ${r}"
        // Phase 383 — relative to the largest budget a check was given, which load scaling can take past 30 s (8 s × 4)
        long backstop = Math.max(MAX_SINGLE_CHECK_MS, 2L * Z3Backend.effectiveBudgetMax())
        assert Z3Backend.solverMsMax() <= backstop : "single-check backstop exceeded — ${r}"
    }
}
