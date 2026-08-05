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

import java.lang.invoke.VarHandle

/**
 * The seqlock <b>torn read</b> as a real interleaving bug — the reader that <em>skips the sequence validation</em>,
 * the analogue of {@link SpscBufferLeaky}'s publish-before-write (there the inversion is in the writer; here it is in
 * the reader). The writer is the same parity-disciplined {@link SeqLock#write} — it bumps {@code seq} odd, updates
 * the two halves of the record, bumps {@code seq} even — but this reader reads {@code x} and {@code y} with NO
 * {@code seq} snapshot or parity check, so it can read the two halves straddling a write and observe a record that
 * was never written together ({@code x != y}).
 *
 * <p>Lincheck model-checks the exact bytecode and reports the torn pair as a linearizability violation (a read with
 * no sequential explanation); jcstress observes it empirically across real schedules — the {@code 1, 0} / {@code 0, 1}
 * outcomes (see {@code SeqLockJCStress}). It is the read-side mirror of the {@code SeqLock}'s {@code @Ensures}
 * refutation in {@code SeqLockVerifyTest} (the parity-skipping reader). {@code @CompileStatic @POJO} for the same
 * reason as {@link SeqLock} — clean, dispatch-free bytecode for the runtime rungs.
 */
@CompileStatic
@POJO
class SeqLockLeaky {
    private volatile int seq = 0
    private int x = 0
    private int y = 0

    /** Writer side — the correct parity discipline, fence and all, byte-for-byte {@link SeqLock#write}. Kept in step
     *  deliberately: the bug here must stay purely on the reader, so the twin isolates one variable. */
    void write(int v) {
        seq = seq + 1      // odd: write in progress
        VarHandle.releaseFence()   // JMM: the lock is taken before any half of the record moves
        x = v
        y = v
        seq = seq + 1      // even: publish
    }

    /** Reader side — BUG: reads both halves with no {@code seq} guard, so a snapshot taken mid-write escapes torn.
     *  (No {@link VarHandle#acquireFence} either — but that is not the bug: there is no re-sample to order it
     *  against. This reader tears on plain interleaving, with or without a memory-model subtlety.) */
    List<Integer> tryRead() {
        int rx = x         // no `s1 = seq` snapshot…
        int ry = y         // …a writer can land between these two reads…
        return [rx, ry]    // …and we publish the torn pair instead of returning null to retry
    }
}
