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
package verification

import groovy.transform.CompileStatic

import java.util.concurrent.ConcurrentHashMap

/**
 * Phase 216 — the <b>trusted-spec ledger</b>: one uniform inventory of every fact a compilation
 * assumed <i>without proof</i>, whatever its provenance:
 * <ul>
 *   <li><b>in-place</b> — a {@code trusted = true} {@code @ThrowsIf} arm on the user's own method
 *       (documented third-party behaviour, Phase 214);</li>
 *   <li><b>external spec</b> — a registry skeleton consumed for a library call
 *       ({@code java.lang.Math#abs}, Phase 215) — trusted by definition, since nobody proves the
 *       JDK's bodies.</li>
 * </ul>
 *
 * The design principle from the {@code trusted} discussions: <b>trust that is visible is trust that
 * gets reviewed</b>. Proof-waiving is deliberately quiet at the use site (that's its point), so the
 * ledger is where it must reappear: the harness prints {@link #summary} beside the perf line, and
 * DocLint inventories the shipped spec files. Entries are deduplicated JVM-wide (the compiler daemon
 * may compile many units); {@link #reset} is the test hook.
 */
@CompileStatic
class TrustLedger {

    private static final Set<String> ENTRIES = ConcurrentHashMap.newKeySet()

    /** Record one trusted fact: {@code kind} ∈ {in-place @ThrowsIf, external spec}, {@code where} is
     *  the owning method (FQN#name), {@code what} the contract detail. Idempotent. */
    static void record(String kind, String where, String what) {
        ENTRIES.add("[${kind}] ${where} — ${what}".toString())
    }

    /** All recorded trusted facts, sorted for stable output. */
    static List<String> entries() { ENTRIES.sort() }

    /** One line for the harness stream, beside the perf report. */
    static String summary() {
        int inPlace = ENTRIES.count { it.startsWith('[in-place') } as int
        int external = ENTRIES.count { it.startsWith('[external') } as int
        "trusted: ${ENTRIES.size()} fact(s) assumed without proof (${external} external spec(s), " +
            "${inPlace} in-place trusted contract(s))"
    }

    static void reset() { ENTRIES.clear() }
}
