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
package concurrent

import groovy.transform.CompileStatic
import groovy.transform.stc.POJO
import groovy.contracts.Invariant

/**
 * A <b>seqlock</b> (sequence lock) — a lock-free, single-writer / many-reader optimistic-read protocol, and the
 * one example that gives <b>all three rungs distinct, non-overlapping work</b> (see {@code CONCURRENCY.md}). The
 * bug class it adds to the suite is the <em>torn read</em>: a reader observing a multi-field record that was never
 * written together. {@link SpscBuffer} is a publication race (writer ordering); {@link BoundedCounter} a
 * check-then-act (read-modify-write atomicity); this is read-side snapshot atomicity.
 *
 * <p>Two fields, {@code x} and {@code y}, are a single logical record that must always agree ({@code x == y}). The
 * sequence counter {@code seq} encodes the writer's progress with a parity discipline: <b>even = unlocked</b> (the
 * record is consistent), <b>odd = a write is in progress</b> (the record may be momentarily torn). That is exactly
 * the implication-guarded class {@code @Invariant} below — the verifier's <em>fair share</em>:
 *
 * <ul>
 *   <li><b>rung 1 — groovy-verify</b> proves the protocol <em>sequentially</em>: {@link #write} re-establishes
 *       {@code x == y} before it republishes (bumps {@code seq} back to even), and a successful {@link #tryRead}
 *       (the guard passed: {@code seq} unchanged and even) returns a <em>consistent</em> snapshot. The proof leans
 *       on the guarded invariant — the novel piece here is the implication {@code seq % 2 == 0 ==> x == y}, a tiny
 *       two-state protocol a sequential checker is uniquely good at. {@code SeqLockVerifyTest} reads <em>this file</em>
 *       and discharges the writer protocol (the class {@code @Invariant}), and proves the reader obligation
 *       ({@code @Ensures({ result == null || result[0] == result[1] })}) over {@code tryRead}'s same body — the
 *       contract lives in the test, not on the field, because the runtime rungs compile this source with
 *       groovy-contracts' transforms OFF (bare bytecode), and a {@code result}-bearing {@code @Ensures} won't
 *       type-check under that bare {@code @CompileStatic} (the same reason {@link AtomicBoundedCounter} carries no
 *       contract of its own). Both refute when the protocol is broken.</li>
 *   <li><b>rung 3a — Lincheck</b> model-checks the ACTUAL bytecode: the correct {@code tryRead} only ever returns a
 *       committed, consistent snapshot (linearizable); {@link SeqLockLeaky}'s unguarded read is caught.</li>
 *   <li><b>rung 3b — jcstress</b> stress-runs it on real JIT/hardware and tallies the torn-read outcome the others
 *       approach differently (the JMM grain; see {@code SeqLockJCStress}).</li>
 * </ul>
 *
 * <p><b>The fragment, honestly.</b> A real reader <em>spins</em> — retries until the guard passes — and a spin loop
 * has no well-founded measure, so it is outside the straight-line fragment (as every loop is; cf. the CAS retry loop
 * in {@link AtomicBoundedCounter}). So the verified unit is {@link #tryRead}: <em>one</em> optimistic attempt,
 * returning the snapshot or {@code null} to signal "retry". The spin is lifted to the caller — the jcstress/Lincheck
 * actors loop on {@code tryRead} — which keeps the Groovy method loop-free and provable while the runtime rungs carry
 * the retry. Same source, both rungs; they differ only in <em>level</em> (rung 1 proves the snapshot is consistent
 * <em>above</em> the memory model; rungs 3 establish it <em>at</em> it).
 *
 * <p>{@code @CompileStatic @POJO} for the same reason as {@link SpscBuffer}: direct field bytecode and no metaclass
 * plumbing, so Lincheck/jcstress have nothing Groovy-specific to instrument.
 */
@CompileStatic
@POJO
@Invariant({ seq % 2 == 0 ==> x == y })   // unlocked (seq even) ⟹ the record is consistent
class SeqLock {
    private volatile int seq = 0   // even = unlocked/consistent, odd = write in progress (only the writer advances it)
    private int x = 0              // the two halves of one logical record; protected by seq's parity
    private int y = 0

    /**
     * Writer side. Bump {@code seq} to odd (take the write lock — the record may now be torn), update both halves,
     * bump back to even (publish). The verifier proves the exit re-establishes {@code x == y} before republishing —
     * if it didn't, the {@code seq even ==> x == y} invariant would refute (see {@link SeqLockLeaky}'s writer twin).
     */
    void write(int v) {
        seq = seq + 1      // odd: write in progress — the invariant's guard is now false, so x/y may diverge
        x = v
        y = v
        seq = seq + 1      // even: publish — x == y restored, the guarded invariant holds again
    }

    /**
     * Reader side, ONE optimistic attempt. Snapshot {@code seq}, read both halves, snapshot {@code seq} again: if it
     * is unchanged and even, no writer interfered and the pair is a consistent committed snapshot — return it.
     * Otherwise a write was in progress or landed mid-read, so return {@code null} ("retry"). The verifier's reader
     * obligation — {@code @Ensures({ result == null || result[0] == result[1] })}, a non-null result is always
     * consistent — is proved over this exact body in {@code SeqLockVerifyTest} (it can't ride this bare runtime
     * compile; see the class doc).
     */
    List<Integer> tryRead() {
        int s1 = seq
        int rx = x
        int ry = y
        int s2 = seq
        if (s1 == s2 && s1 % 2 == 0) return [rx, ry]   // consistent: seq held still across the read, and unlocked
        return null                                     // contended: the caller retries
    }
}
