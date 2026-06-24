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
package lincheck

import concurrent.SeqLock
import concurrent.SeqLockLeaky
import groovy.transform.CompileStatic
import groovy.transform.stc.POJO
import org.jetbrains.lincheck.datastructures.Operation
import org.jetbrains.lincheck.datastructures.ModelCheckingOptions
import org.junit.jupiter.api.Test

import static org.junit.jupiter.api.Assertions.assertThrows

/**
 * Rung 3a of the seqlock's three-rung story (see {@code CONCURRENCY.md}): Lincheck model-checks the ACTUAL bytecode
 * of the seqlock across interleavings, discharging the read-side snapshot-atomicity that the compile-time checker
 * (rung 1) proves only sequentially. groovy-verify proves a successful {@code tryRead} returns a consistent snapshot
 * <em>assuming</em> its local view is faithful; Lincheck checks that against every interleaving of the real code.
 *
 * <p>The protocol is single-writer / many-reader, so {@code write} is pinned to {@code nonParallelGroup = 'writer'}
 * (one writer) while {@code read} runs freely (many readers). The exposed {@code read} operation is the <em>spin in
 * the caller</em> the design calls for: it loops on the data structure's single-attempt {@code tryRead} until the
 * guard passes, so it always returns a consistent committed snapshot — which is what linearizability needs (a
 * single-attempt {@code tryRead} returning {@code null} on contention has no sequential explanation and is
 * deliberately NOT exposed here). The spin terminates because the lone writer is a finite operation; Lincheck's
 * spin-cycle detection switches to it so the reader's loop makes progress.
 *
 * <p>What Lincheck checks here that it does NOT on the buffer: a <em>torn read</em>. A {@code tryRead} that returns
 * {@code [1, 0]} is a read of a record half-updated — no sequential history of {write, tryRead} (where each write is
 * atomic on the record) can produce it, so Lincheck flags it as non-linearizable. This catches the <em>logic</em>
 * torn read (the reader skipping its validation); the pure memory-visibility torn read is jcstress's grain, which
 * Lincheck's sequentially-consistent managed strategy is blind to (see {@code CONCURRENCY.md}).
 */
@CompileStatic
@POJO
class SeqLockLincheckTest {

    /** The correct seqlock: tryRead validates the sequence, so it only ever returns a consistent committed snapshot. */
    @CompileStatic
    @POJO
    static class Correct {
        private final SeqLock sl = new SeqLock()
        @Operation(nonParallelGroup = 'writer') void write(int v) { sl.write(v) }
        @Operation List<Integer> read() {            // spin in the caller: retry tryRead until a consistent snapshot
            List<Integer> r = sl.tryRead()
            while (r == null) r = sl.tryRead()
            r
        }
    }

    /** The leaky seqlock: tryRead skips the sequence guard, so a snapshot taken mid-write escapes torn. */
    @CompileStatic
    @POJO
    static class Leaky {
        private final SeqLockLeaky sl = new SeqLockLeaky()
        @Operation(nonParallelGroup = 'writer') void write(int v) { sl.write(v) }
        @Operation List<Integer> read() {            // the leaky tryRead never returns null, so this runs once
            List<Integer> r = sl.tryRead()
            while (r == null) r = sl.tryRead()
            r
        }
    }

    private static ModelCheckingOptions opts() {
        new ModelCheckingOptions()
                .iterations(30)
                .threads(2)
                .actorsPerThread(3)
                .actorsBefore(1)
                .actorsAfter(0)
    }

    @Test
    void correctSeqLockIsLinearizable() {
        opts().check(Correct)        // passes: the seq guard rejects every torn snapshot (returns null to retry)
    }

    @Test
    void leakySeqLockIsCaught() {
        // Lincheck finds the interleaving where a writer lands between the reader's two field reads, so tryRead
        // returns a torn pair — a read no sequential history explains. Reported as a linearizability violation.
        assertThrows(AssertionError) { opts().check(Leaky) }
    }
}
