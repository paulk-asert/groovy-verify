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

/**
 * A correct lock-free single-producer/single-consumer bounded buffer — the real-code rung under the
 * groovy-verify {@code Buffer} (verified sequentially) and {@code examples/concurrency/Buffer.tla} (model-checked).
 * Lincheck checks the ACTUAL bytecode across interleavings.
 *
 * <p><b>This is a facsimile, not a copy</b> — but the boundary is narrower than "different code shapes". The
 * <i>data structure</i> is not the divider: groovy-verify verifies this very circular shape — the
 * {@code P107 ring-buffer} "circular (modulo) ring" case proves {@code items[t % capacity]} in bounds and the
 * occupancy invariant preserved. The verified {@code Buffer} is a linear, non-wrapping model ({@code values[head]},
 * {@code read}/{@code write}) only for clarity and to match its ported source, not because circular is out of reach. The real divider is the <b>concurrency representation</b>: groovy-verify reasons
 * <i>above</i> the memory model — it abstracts the peer thread into empty {@code @Rely}/{@code @UnderRely}
 * rely-step methods and never models the JMM, {@code volatile}, or the atomicity grain (that omission is precisely
 * what this rung exists to cover). Those stubs are inert at runtime and the verified class carries no real
 * synchronisation, so it is not a runnable thread-safe artifact; Lincheck instruments <i>real</i> bytecode, so it
 * needs the actual {@code volatile} lock-free code here. None of the rungs validates another's exact code; each
 * demonstrates the same algorithm at its own fidelity (README: "None subsumes the others").
 *
 * <p>{@code @CompileStatic} is load-bearing here: it makes {@code offer}/{@code poll} compile to direct
 * field and array bytecode (getfield/putfield, iaload/iastore) with no Groovy call-site caching or
 * dynamic dispatch — so the methods Lincheck instruments and explores are as clean as the Java original.
 *
 * <p>The §VII discipline made concrete: write the (already-declassified) value into the slot, THEN
 * publish it by advancing {@code tail}. That publish-after-write order is the operational form of "the
 * slot's data is Low before {@code tail++} pulls it into the Low region". {@link SpscBufferLeaky} inverts
 * the order and Lincheck catches the leak.
 */
@CompileStatic
@POJO
class SpscBuffer {
    private final int[] items
    private final int capacity
    private volatile int head = 0   // consumer's read index (only the consumer advances it)
    private volatile int tail = 0   // producer's write index (only the producer advances it)

    SpscBuffer(int capacity) {
        this.capacity = capacity
        this.items = new int[capacity]
    }

    /** Producer side. Returns false if full. */
    boolean offer(int x) {
        int t = tail
        if (t - head == capacity) return false      // full
        items[t % capacity] = x                     // 1. write the value into the slot…
        tail = t + 1                                // 2. …THEN publish it (release the slot to the consumer)
        true
    }

    /** Consumer side. Returns null if empty. */
    Integer poll() {
        int h = head
        if (tail - h == 0) return null              // empty (acquire-load of tail)
        int v = items[h % capacity]                 // read the published value
        head = h + 1                                // free the slot
        v
    }
}
