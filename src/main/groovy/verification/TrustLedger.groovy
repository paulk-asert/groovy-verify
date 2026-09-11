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
 *   <li><b>opaque carrier</b> — a {@code Monoid}/{@code Semigroup} value handed to a parallel reduction whose
 *       combiner has no body in sight (a parameter, a library constant): its laws are assumed, where a carrier
 *       built from a visible lambda has them proven (Phase 291).</li>
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

    /** Records made on this thread since {@link #capture} — duplicates included, so a test can see what ONE
     *  compile recorded even when the JVM-wide set already held the entry. Null (no capture) by default. */
    private static final ThreadLocal<List<String>> CAPTURED = new ThreadLocal<List<String>>()

    /**
     * {@code VERIFY_TRUST} (also {@code -Dverify.trust}) — Phase 291: surfacing the ledger to a consumer's own build.
     * {@code report} prints each trusted fact a class relied on when the checker finishes that class
     * ({@code trusted: …} on stdout, the {@code VERIFY_EXPLAIN} channel); {@code deny} makes each one a compile
     * error instead. Null — unset, or any other value — leaves the ledger an inventory only, the default path
     * byte-identical. Mutable only as a test hook (the harness {@code trustMode:} key).
     */
    static volatile String mode = normaliseMode(System.getenv('VERIFY_TRUST') ?: System.getProperty('verify.trust'))

    static String normaliseMode(String m) {
        String t = m?.trim()?.toLowerCase()
        t == 'report' || t == 'deny' ? t : null
    }

    /** Records made on this thread since the checker last surfaced them (only while {@link #mode} is set). */
    private static final ThreadLocal<List<String>> PENDING = new ThreadLocal<List<String>>()

    /** Record one trusted fact: {@code kind} ∈ {in-place @ThrowsIf, external spec, opaque carrier}, {@code where}
     *  is the owning method (FQN#name), {@code what} the contract detail. Idempotent. */
    static void record(String kind, String where, String what) {
        String e = "[${kind}] ${where} — ${what}".toString()
        ENTRIES.add(e)
        CAPTURED.get()?.add(e)
        if (mode != null) {
            List<String> p = PENDING.get()
            if (p == null) {
                p = new ArrayList<String>()
                PENDING.set(p)
            }
            p.add(e)
        }
    }

    /** The facts recorded on this thread since the last drain — deduplicated, in order — clearing them. */
    static List<String> drainPending() {
        List<String> p = PENDING.get()
        PENDING.remove()
        p ? new ArrayList<String>(new LinkedHashSet<String>(p)) : new ArrayList<String>()
    }

    /** All recorded trusted facts, sorted for stable output. */
    static List<String> entries() { ENTRIES.sort() }

    /** Start capturing this thread's records (the harness brackets one case's compile with this). */
    static void capture() { CAPTURED.set(new ArrayList<String>()) }

    /** The records captured on this thread since {@link #capture}, ending the capture. */
    static List<String> captured() {
        List<String> out = CAPTURED.get() ?: Collections.<String> emptyList()
        CAPTURED.remove()
        out
    }

    /** One line for the harness stream, beside the perf report. */
    static String summary() {
        int inPlace = ENTRIES.count { it.startsWith('[in-place') } as int
        int external = ENTRIES.count { it.startsWith('[external') } as int
        int opaque = ENTRIES.count { it.startsWith('[opaque carrier') } as int
        "trusted: ${ENTRIES.size()} fact(s) assumed without proof (${external} external spec(s), " +
            "${inPlace} in-place trusted contract(s), ${opaque} opaque carrier(s))"
    }

    static void reset() { ENTRIES.clear() }
}
