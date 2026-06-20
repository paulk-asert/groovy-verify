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
import groovy.contracts.Requires

/**
 * A correct lock-free single-producer/single-consumer bounded buffer. <b>This one source is checked by two rungs at
 * once — not a facsimile, the same code</b> (see {@code examples/concurrency/README.md}):
 *
 * <ul>
 *   <li><b>groovy-verify</b> proves the {@code @Invariant} at compile time: {@code items[t % capacity]} is in
 *       bounds and the bounded-occupancy invariant is preserved by {@code offer}/{@code poll}, established by the
 *       constructor. Driven by a harness that compiles <i>this exact file</i> with the checker enabled — see
 *       {@code SpscBufferVerifyTest}.</li>
 *   <li><b>Lincheck</b> model-checks the ACTUAL bytecode of this file across interleavings (this source set).</li>
 * </ul>
 *
 * <p>The only difference between the two builds is a <b>compile knob</b>, not the source. The {@code @Invariant} /
 * {@code @Requires} below are the very contracts groovy-verify proves; the Lincheck compile <i>disables
 * groovy-contracts' AST transforms</i> (see {@code build.gradle}'s {@code compileConcurrentGroovy}), so the
 * annotations resolve but inject nothing — leaving the bare lock-free bytecode Lincheck needs. (Just disabling
 * assertions isn't enough: with the transforms on, an assertion compiles to Groovy power-assert plus shared
 * static trackers and a per-call closure, all of which Lincheck would <i>explore</i> as concurrency surface
 * unrelated to the algorithm — so the managed run hangs. Disabling the transforms is the one-move way to bare
 * bytecode; see {@code build.gradle} for the full rationale and the {@code addGuarantee} alternative.)
 *
 * <p>So the two rungs do not differ in <i>code</i> — they differ in <b>level</b>: groovy-verify reasons <i>above</i>
 * the memory model (it never models the JMM, {@code volatile}, or the atomicity grain — deliberately, that is rung
 * 3's job), while Lincheck operates at it. Same source, same shape; complementary fidelity (README: "None subsumes
 * the others").
 *
 * <p>{@code @CompileStatic} is load-bearing: it makes {@code offer}/{@code poll} compile to direct field and array
 * bytecode (getfield/putfield, iaload/iastore) with no call-site caching — clean both for Lincheck to instrument
 * and for groovy-verify to read.
 *
 * <p>The §VII discipline made concrete: write the (already-declassified) value into the slot, THEN publish it by
 * advancing {@code tail}. That publish-after-write order is the operational form of "the slot's data is Low before
 * {@code tail++} pulls it into the Low region". {@link SpscBufferLeaky} inverts the order and Lincheck catches the leak.
 */
@CompileStatic
@POJO
@Invariant({ capacity > 0 && items.length == capacity && 0 <= head && head <= tail && tail - head <= capacity })
class SpscBuffer {
    private final int[] items
    private final int capacity
    private volatile int head = 0   // consumer's read index (only the consumer advances it)
    private volatile int tail = 0   // producer's write index (only the producer advances it)

    @Requires({ capacity > 0 })
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
