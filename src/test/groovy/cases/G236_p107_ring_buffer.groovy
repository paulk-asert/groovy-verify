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

/** 'P107 ring-buffer' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G236_p107_ring_buffer {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A ring buffer as a mutable data structure: enqueue/dequeue preserve the class @Invariant under @Modifies framing; an over-strong frame refutes. Both the non-wrapping bounded queue and the WRAPPING circular (modulo) ring verify — `items[t % capacity]` is proven in bounds — so the circular shape is no harder for the fragment.'

    static final List<Map> CASES = [
        // ---------- P107 ring buffer: a verified mutable data structure (class @Invariant) ----------
        // A bounded (non-wrapping) queue as a ring buffer, after Leino's Dafny tutorial (Why3's `ring_buffer`).
        // The state is a `char`/int buffer `data` + head `m` + tail `n`; the type invariant is a class
        // `@Invariant`, which the engine *assumes* on entry and *checks is preserved* on exit of every method
        // (so a mutator that breaks it refutes). Why3's ghost `seq contents` abstraction is dropped — we have
        // no model fields — and the queue is specified directly over the array region `data[m..n)` with
        // `old`-relative framing. No new engine code: object array-field + `@Modifies`-style framing +
        // scalar/array `old` + class-invariant preservation all already exist.
        [group: 'P107 ring-buffer', name: 'enqueue: writes tail, frames the rest, preserves invariant', ok: true,
         src: tc('''@Invariant({ 0 < data.length && 0 <= m && m <= n && n <= data.length })
                    class Queue {
                        int[] data
                        int m
                        int n
                        @Requires({ n < data.length })
                        @Ensures({ n == old.n + 1 && data[old.n] == x && (0..<old.n).every { data[it] == old.data[it] } })
                        void enqueue(int x) {
                            data[n] = x
                            n = n + 1
                        }
                    }''')],
        // Frame control: claiming the *written* slot is also unchanged (range 0..old.n inclusive) must refute.
        [group: 'P107 ring-buffer', name: 'enqueue over-strong frame refuted', expect: 'Cannot prove postcondition',
         src: tc('''@Invariant({ 0 < data.length && 0 <= m && m <= n && n <= data.length })
                    class Queue {
                        int[] data
                        int m
                        int n
                        @Requires({ n < data.length })
                        @Ensures({ (0..<old.n + 1).every { data[it] == old.data[it] } })
                        void enqueue(int x) {
                            data[n] = x
                            n = n + 1
                        }
                    }''')],
        // dequeue: returns the head element and advances m; invariant preserved.
        [group: 'P107 ring-buffer', name: 'dequeue: returns head, advances m', ok: true,
         src: tc('''@Invariant({ 0 < data.length && 0 <= m && m <= n && n <= data.length })
                    class Queue {
                        int[] data
                        int m
                        int n
                        @Requires({ m < n })
                        @Ensures({ result == old.data[old.m] && m == old.m + 1 })
                        int dequeue() {
                            int r = data[m]
                            m = m + 1
                            return r
                        }
                    }''')],
        // Invariant-preservation control: an unguarded bump breaks `n <= data.length`, so it must refute
        // at method exit — proof that the class invariant is genuinely checked, not just assumed.
        [group: 'P107 ring-buffer', name: 'invariant-breaking mutator refuted', expect: 'Cannot prove class invariant',
         src: tc('''@Invariant({ 0 < data.length && 0 <= m && m <= n && n <= data.length })
                    class Queue {
                        int[] data
                        int m
                        int n
                        void bump() { n = n + 1 }
                    }''')],
        // size() >= 0 is provable only because the class invariant (m <= n) is assumed on entry.
        [group: 'P107 ring-buffer', name: 'size non-negative from the invariant', ok: true,
         src: tc('''@Invariant({ 0 < data.length && 0 <= m && m <= n && n <= data.length })
                    class Queue {
                        int[] data
                        int m
                        int n
                        @Ensures({ result >= 0 })
                        int size() { return n - m }
                    }''')],
        // The WRAPPING (circular, modulo-indexed) ring also verifies — so the non-wrapping `Queue` above is a
        // clarity/source-matching choice, NOT a fragment limit. `items[t % capacity]` is proven in bounds (Z3 knows
        // `0 <= t % capacity < capacity` for `capacity > 0`, and the @Invariant pins `items.length == capacity`),
        // and offer/poll preserve the bounded-occupancy invariant. This is the same circular shape that
        // `src/concurrent/.../SpscBuffer` uses for Lincheck — confirming the two rungs diverge on the *concurrency
        // model* (rely-steps above the JMM vs real `volatile`), not on the data structure.
        [group: 'P107 ring-buffer', name: 'circular (modulo) ring: offer/poll bounds-safe, invariant preserved', ok: true,
         src: tc('''@Invariant({ capacity > 0 && items.length == capacity && 0 <= head && head <= tail && tail - head <= capacity })
                    class Ring {
                        int[] items
                        int capacity
                        int head
                        int tail
                        @Requires({ tail - head < capacity })          // not full: room to write
                        void offer(int x) {
                            items[tail % capacity] = x                 // PROVEN in bounds: 0 <= tail % capacity < items.length
                            tail = tail + 1
                        }
                        @Requires({ head < tail })                     // not empty
                        int poll() {
                            int v = items[head % capacity]             // PROVEN in bounds
                            head = head + 1
                            return v
                        }
                    }''')],
        // Soundness control: drop the not-full guard and `offer` can overflow the logical buffer (`tail - head`
        // exceeds capacity, overwriting the unread slot at `head`), so the bounded-occupancy invariant is no longer
        // preserved at method exit → refutes. (Array bounds stay safe — modulo guarantees that; the guard protects
        // *occupancy*, not the index.)
        [group: 'P107 ring-buffer', name: 'circular ring without the not-full guard breaks the invariant', expect: 'Cannot prove class invariant',
         src: tc('''@Invariant({ capacity > 0 && items.length == capacity && 0 <= head && head <= tail && tail - head <= capacity })
                    class Ring {
                        int[] items
                        int capacity
                        int head
                        int tail
                        void offer(int x) {                            // no @Requires: may write when full
                            items[tail % capacity] = x
                            tail = tail + 1
                        }
                    }''')],
    ]
}
