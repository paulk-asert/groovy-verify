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
import groovy.contracts.Ensures
import verification.Rely
import verification.Guarantee
import verification.UnderRely
import verification.Label
import verification.Declassify

/**
 * The §VII capstone buffer — information flow × rely/guarantee — as a <b>single shared source</b> checked by two
 * rungs at once (see {@code examples/concurrency/README.md}), exactly like {@link SpscBuffer} but carrying the
 * <i>whole</i> §VII argument, not just the bounds:
 *
 * <ul>
 *   <li><b>groovy-verify</b> (rung 1) proves the bounds @Invariant under each thread's @UnderRely interference AND
 *       the no-leak information-flow property (the {@code @Label}/{@code level} region discipline, the §III-A
 *       secure-update at {@code tail++}). {@code BufferVerifyTest} reads <i>this exact file</i> and runs the checker.</li>
 *   <li><b>Lincheck</b> (rung 3) model-checks the ACTUAL bytecode for linearizability across interleavings.</li>
 * </ul>
 *
 * <p>The same compile-knob story as {@link SpscBuffer}: the Lincheck build disables groovy-contracts' AST transforms
 * so {@code @Invariant}/{@code @Requires}/{@code @Ensures} are inert; the {@code verification.*} annotations
 * ({@code @Rely}/{@code @Guarantee}/{@code @UnderRely}/{@code @Label}) are plain annotations with no transform, and
 * {@code Declassify.to} / {@code deliver} are a runtime identity / no-op — so the bytecode Lincheck sees is the bare
 * lock-free buffer.
 *
 * <p>One extra wrinkle vs. SpscBuffer: the rely/guarantee proof needs the rely-stable {@code @Requires}
 * preconditions (an in-body path fact isn't threaded through the {@code @UnderRely} rely-step's havoc). They're kept,
 * and a runtime empty/full guard is added alongside — provably <i>dead</i> under the precondition (so the proof goes
 * through) yet <i>live</i> at runtime when contracts are disabled (so Lincheck can call freely). Linear/non-wrapping,
 * so it's a one-shot fill/drain buffer under Lincheck.
 */
@CompileStatic
@POJO
@Invariant({ capacity > 0 && values.length == capacity && 0 <= head && head <= tail && tail <= values.length })
class Buffer {
    enum L { Low, High }
    static boolean leq(L a, L b) { a == L.Low || b == L.High }
    static L join(L a, L b) { leq(a, b) ? b : a }

    @Label(by = 'level') private final int[] values
    private final int capacity      // == values.length; the constructor @Requires resolves this name in both compiles
    private volatile int head = 0   // consumer read index (only the consumer advances it)
    private volatile int tail = 0   // producer write index (only the producer advances it)

    /** The value-dependent positional label: a slot in [head, tail) is Low (published), else High. */
    static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }

    // §IV compatibility predicates: each thread's guarantee is the other's rely.
    @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
    @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
    @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) { tail == oldTail }
    @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) { tail == oldTail && oldHead <= head }

    @Ensures({ true }) static void deliver(@Label('Low') int x) { }   // the public (Low) sink

    @Requires({ capacity > 0 })
    Buffer(int capacity) {
        this.capacity = capacity
        this.values = new int[capacity]
    }

    /** Consumer side. @Requires is the rely-stable proof precondition; the guard is its live runtime twin. */
    @Requires({ head < tail })
    @UnderRely('Consumer')
    Integer consume() {
        if (tail - head == 0) return null
        int v = values[head]            // in [head, tail) → Low; in bounds under the rely
        deliver(v)                      // Low → Low public sink: no leak
        head = head + 1
        return v
    }

    /** Producer side. Declassify, write the slot, THEN publish by advancing tail (the §III-A secure-update). */
    @Requires({ tail < values.length })
    @UnderRely('Producer')
    boolean produce(@Label('High') int secret) {
        if (tail - values.length == 0) return false
        int msg = Declassify.to('Low', secret)   // §III-E controlled release: the slot's datum becomes Low
        values[tail] = msg
        tail = tail + 1
        return true
    }
}
