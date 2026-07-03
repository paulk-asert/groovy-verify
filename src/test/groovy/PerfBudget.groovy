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
    static final long MAX_CHECK_CALLS = 6_000

    /** Distinct VCs actually solved (the cache-miss population). Deterministic. */
    static final long MAX_DISTINCT_VCS = 4_000

    /** UNKNOWN results (solver gave up / timed out). The corpus carries a handful of hard VCs plus the
     *  Phase 203/204 inconsistency canaries (recurrence-axiom refutes that intentionally time MBQI out —
     *  measured 24 after those landed); re-based with headroom. */
    static final long MAX_UNKNOWN = 40

    /** Pathological single-check backstop — machine-dependent, hence deliberately enormous. */
    static final long MAX_SINGLE_CHECK_MS = 30_000

    static String report() {
        long hits = Z3Backend.vcCacheHits(), misses = Z3Backend.vcCacheMisses()
        "perf: ${hits + misses} solver checks (${misses} solved / ${hits} cached), " +
            "${Z3Backend.solverMsTotal()} ms in Z3 (max ${Z3Backend.solverMsMax()} ms, " +
            "${Z3Backend.slowCheckCount()} over 500 ms), ${Z3Backend.unknownResults()} UNKNOWN"
    }

    /** Assert the ceilings; the message carries the full report so a trip is self-explanatory. */
    static void assertBudget() {
        String r = report()
        long calls = Z3Backend.vcCacheHits() + Z3Backend.vcCacheMisses()
        assert calls <= MAX_CHECK_CALLS               : "check-call ceiling exceeded — ${r}"
        assert Z3Backend.vcCacheMisses() <= MAX_DISTINCT_VCS : "distinct-VC ceiling exceeded — ${r}"
        assert Z3Backend.unknownResults() <= MAX_UNKNOWN     : "UNKNOWN ceiling exceeded — ${r}"
        assert Z3Backend.solverMsMax() <= MAX_SINGLE_CHECK_MS : "single-check backstop exceeded — ${r}"
    }
}
