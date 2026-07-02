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
package cases

import static cases.CaseDsl.*

/** 'P-vii' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G011_p_vii {

    static final List<Map> CASES = [

        // The §VII capstone made Lincheck-ready, ONE source: keep the rely-stable @Requires preconditions (so the
        // full R/G + info-flow proof still goes through — the runtime guard is provably DEAD under the
        // precondition), AND add the runtime empty/full guard returning null/false. With groovy-contracts disabled
        // at the Lincheck boundary the precondition isn't enforced, so the guard is LIVE and the buffer is
        // thread-safe to call freely. (A bare runtime guard WITHOUT the precondition fails here: an in-body path
        // fact isn't threaded through the @UnderRely rely-step's havoc, unlike a rely-stable precondition.)
        [group: 'P-vii', name: 'capstone made Lincheck-ready: precondition + live runtime guard verifies', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        int head
                        int tail
                        @Label(by = 'level') int[] values
                        static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }
                        @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
                        @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
                        @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) { tail == oldTail }
                        @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) { tail == oldTail && oldHead <= head }
                        @Ensures({ true }) static void deliver(@Label('Low') int x) { }
                        @Requires({ head < tail })
                        @UnderRely('Consumer')
                        Integer consume() {
                            if (tail - head == 0) return null
                            int v = values[head]
                            deliver(v)
                            head = head + 1
                            return v
                        }
                        @Requires({ tail < values.length })
                        @UnderRely('Producer')
                        boolean produce(@Label('High') int secret) {
                            if (tail - values.length == 0) return false
                            int msg = Declassify.to('Low', secret)
                            values[tail] = msg
                            tail = tail + 1
                            return true
                        }
                    }''')],
        // §VII CAPSTONE — info-flow × rely/guarantee on ONE buffer (Smith's culminating example: plain and secret
        // messages produced/consumed concurrently). The same `Buffer` carries: the lattice + value-dependent
        // POSITIONAL label (the region [head,tail) is Low), the four §IV compatibility predicates, AND two
        // @UnderRely methods that are checked for BOTH bounds-safety-under-interference (R/G) AND no-leak (info-flow).
        // The consumer reads values[head] (Low region) and delivers it to a public sink under the producer's
        // interference (head fixed, tail grows); the producer declassifies, writes at tail, and advances tail (the
        // §III-A array secure-update) under the consumer's interference (tail fixed, head grows). The secure-update
        // is rely-stable: level(tail, head, tail+1) is Low for ANY head <= tail (the invariant), so the consumer
        // advancing head cannot break it. Both properties hold together — the composition Step 3 set out to reach.
        [group: 'P-vii', name: 'capstone: info-flow × R/G on one buffer verifies', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        int head
                        int tail
                        @Label(by = 'level') int[] values
                        static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }
                        @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
                        @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
                        @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) { tail == oldTail }
                        @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) { tail == oldTail && oldHead <= head }
                        @Ensures({ true }) static void deliver(@Label('Low') int x) { }      // public sink
                        @Requires({ head < tail })
                        @UnderRely('Consumer')
                        int consume() {
                            int v = values[head]        // in [head, tail) → Low; in bounds (head < tail <= length)
                            deliver(v)                  // Low → Low public sink: no leak
                            head = head + 1
                            return v
                        }
                        @Requires({ tail < values.length })
                        @UnderRely('Producer')
                        void produce(@Label('High') int secret) {
                            int msg = Declassify.to('Low', secret)   // §III-E controlled release
                            values[tail] = msg                        // a Low value at the boundary slot
                            tail = tail + 1                           // §III-A secure-update under interference
                        }
                    }''')],
        // SOUNDNESS of the capstone — the R/G interleaving machinery does NOT mask an info-flow leak. The producer
        // skips the declassification and advances `tail` over a raw secret: the §III-A array secure-update refutes
        // at `tail++` (High → Low) even though the body is also being checked under the consumer's interference.
        [group: 'P-vii', name: 'capstone: producer leaking a secret under R/G still refutes', expect: 'information leak',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        int head
                        int tail
                        @Label(by = 'level') int[] values
                        static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }
                        @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) { tail == oldTail }
                        @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) { tail == oldTail && oldHead <= head }
                        @Requires({ tail < values.length })
                        @UnderRely('Producer')
                        void produce(@Label('High') int secret) {
                            values[tail] = secret                     // a raw HIGH value at the boundary slot
                            tail = tail + 1                           // pulls High into the Low region: REFUTES
                        }
                    }''')],
        [group: 'P-vii', name: 'README capstone: info-flow x R/G Buffer', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
class Buffer {
    enum L { Low, High }
    static boolean leq(L a, L b) { a == L.Low || b == L.High }
    static L join(L a, L b) { leq(a, b) ? b : a }
    int head, tail
    @Label(by = 'level') int[] values                              // each slot's level depends on POSITION…
    static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }   // …the region [head,tail) is Low

    @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
    @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) { head == oldHead && oldTail <= tail }
    @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) { tail == oldTail }
    @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) { tail == oldTail && oldHead <= head }

    @Ensures({ true }) static void deliver(@Label('Low') int x) { }   // a PUBLIC sink — only accepts Low

    @Requires({ head < tail })
    @UnderRely('Consumer')                 // runs under the producer's interference: head pinned, tail grows
    int consume() {
        int v = values[head]               // in [head, tail) ⇒ Low (proven across the concurrent append)
        deliver(v)                         // Low → Low public sink: NO LEAK
        head = head + 1
        return v
    }
    @Requires({ tail < values.length })
    @UnderRely('Producer')                 // runs under the consumer's interference: tail pinned, head grows
    void produce(@Label('High') int secret) {
        int msg = Declassify.to('Low', secret)   // §III-E controlled release
        values[tail] = msg                       // a Low value at the boundary slot
        tail = tail + 1                          // §III-A array secure-update: old.tail ENTERS the Low region
    }
}''')],
    ]
}
