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

/** 'P244 guarantee conformance' — bodies checked against their declared guarantees (slice 5 of the SEQ/PAR ladder). */
class G308_p244_guarantee_conformance {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 244 guarantee conformance: @Guarantee(\'Role\') on a BODY method declares that its own-step transitions honour the Role\'s guarantee predicate — the obligation the §VII argument had left to hand-inspection, now discharged on a synthesised twin (body minus the @UnderRely env step, @Requires kept, @Ensures pred(old.fields, fields)). The buffer flagship proves with both methods declared; a producer that also moves head, or a consumer that moves tail, refutes ("Guarantee conformance does not hold") with a counterexample. Own-step semantics pinned: an exact-increment guarantee proves under a monotonic rely ONLY because the env step is excluded. Wiring completeness: a rely assumed via role-based @UnderRely with NO peer @Guarantee predicate errors as "Unbacked rely"; a @Guarantee naming no predicate, or a predicate whose post-state params name no fields, skips loudly.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [

        // ---------- the flagship, with conformance declared: everything proves ----------
        // The G033 merged buffer plus the Phase 244 declarations: read() honours gCons, write()
        // honours gProd. The lemma chain is now closed end to end — predicates compatible
        // (G ⟹ R, already checked), AND each body actually does what its guarantee says.
        [group: 'P244 guarantee conformance', name: 'buffer with conformant producer and consumer proves', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                       int head
                       int tail
                       int[] values
                       @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) {
                           tail == oldTail
                       }
                       @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) {
                           tail == oldTail && oldHead <= head
                       }
                       @Requires({ head < tail })
                       @UnderRely('Consumer')
                       @Guarantee('Consumer')
                       int read() {
                           int v = values[head]
                           head = head + 1
                           return v
                       }
                       @Requires({ tail < values.length })
                       @UnderRely('Producer')
                       @Guarantee('Producer')
                       void write(int x) {
                           values[tail] = x
                           tail = tail + 1
                       }
                   }''')],
        // Soundness: a producer that ALSO moves head violates gProd (head == oldHead) — caught.
        [group: 'P244 guarantee conformance', name: 'producer moving head violates its guarantee', expect: 'Guarantee conformance does not hold',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                       int head
                       int tail
                       int[] values
                       @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Requires({ tail < values.length && head < tail })
                       @UnderRely('Producer')
                       @Guarantee('Producer')
                       void write(int x) {
                           values[tail] = x
                           tail = tail + 1
                           head = head + 1
                       }
                       @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) {
                           tail == oldTail
                       }
                       @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) {
                           tail == oldTail && oldHead <= head
                       }
                   }''')],
        // The consumer-side mirror: read() moving tail violates gCons (tail == oldTail).
        [group: 'P244 guarantee conformance', name: 'consumer moving tail violates its guarantee', expect: 'Guarantee conformance does not hold',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                       int head
                       int tail
                       int[] values
                       @Rely('Consumer')      static boolean rCons(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Guarantee('Producer') static boolean gProd(int oldHead, int oldTail, int head, int tail) {
                           head == oldHead && oldTail <= tail
                       }
                       @Rely('Producer')      static boolean rProd(int oldHead, int oldTail, int head, int tail) {
                           tail == oldTail
                       }
                       @Guarantee('Consumer') static boolean gCons(int oldHead, int oldTail, int head, int tail) {
                           tail == oldTail && oldHead <= head
                       }
                       @Requires({ head < tail && tail < values.length })
                       @UnderRely('Consumer')
                       @Guarantee('Consumer')
                       int read() {
                           int v = values[head]
                           head = head + 1
                           tail = tail + 1
                           return v
                       }
                   }''')],
        // ---------- the minimal pair on the monotonic counter ----------
        [group: 'P244 guarantee conformance', name: 'an increment honours the monotonic guarantee', ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Rely('Other')   static boolean rOther(int oldCount, int count) { oldCount <= count }
                       @Guarantee('Me') static boolean gMe(int oldCount, int count)    { oldCount <= count }
                       @Guarantee('Me')
                       void bump() { count = count + 1 }
                   }''')],
        [group: 'P244 guarantee conformance', name: 'a decrement violates the monotonic guarantee', expect: 'Guarantee conformance does not hold',
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Rely('Other')   static boolean rOther(int oldCount, int count) { oldCount <= count }
                       @Guarantee('Me') static boolean gMe(int oldCount, int count)    { oldCount <= count }
                       @Requires({ count > 0 })
                       @Guarantee('Me')
                       void drop() { count = count - 1 }
                   }''')],
        // ---------- own-step semantics: the env step is EXCLUDED from the transition ----------
        // gMe demands an exact at-most-one increment. Under the monotonic rely the ENTRY→EXIT
        // transition can grow by any amount (the environment runs first), so this proves only
        // because conformance covers the thread's OWN step — the env step is stripped.
        [group: 'P244 guarantee conformance', name: 'conformance covers the own step, not the env step', ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Rely('Other')   static boolean rOther(int oldCount, int count) { oldCount <= count }
                       @Guarantee('Me') static boolean gMe(int oldCount, int count)    { oldCount <= count && count <= oldCount + 1 }
                       @UnderRely('Other')
                       @Guarantee('Me')
                       void bump() { count = count + 1 }
                   }''')],
        // ---------- wiring completeness, loudly (in conformance-adopting classes) ----------
        // The roles collapsed: the same role both relies AND guarantees, so no OTHER role backs the
        // assumed rely. In a class that adopts the conformance discipline (a body-level @Guarantee),
        // that wiring hole is loud. (A class with no body @Guarantee keeps the modular single-sided
        // posture — its rely is an interface assumption, like a @Requires at a boundary.)
        [group: 'P244 guarantee conformance', name: 'a rely with no peer guarantee is unbacked', expect: 'Unbacked rely',
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Rely('Other')      static boolean rOther(int oldCount, int count) { oldCount <= count }
                       @Guarantee('Other') static boolean gOther(int oldCount, int count) { oldCount <= count }
                       @Requires({ k <= count })
                       @UnderRely('Other')
                       @Guarantee('Other')
                       void observeAndBump(int k) {
                           count = count + 1
                       }
                   }''')],
        // A conformance declaration with no predicate for its role: neither checked nor assumed — loudly.
        [group: 'P244 guarantee conformance', name: 'a guarantee naming no predicate skips loudly', expect: 'Skipped guarantee-conformance',
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Guarantee('Ghost')
                       void bump() { count = count + 1 }
                   }''')],
        // A predicate whose post-state parameters name no fields: no transition to check — loudly.
        [group: 'P244 guarantee conformance', name: 'a predicate not naming fields skips loudly', expect: 'Skipped guarantee-conformance',
         src: tc('''@Invariant({ count >= 0 })
                    class Counter {
                       int count
                       @Guarantee('Me') static boolean gMe(int oldX, int x) { oldX <= x }
                       @Guarantee('Me')
                       void bump() { count = count + 1 }
                   }''')],
    ]
}
