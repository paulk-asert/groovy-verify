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

/** 'P-array' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G032_p_array {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Information-flow over an array\'s value-dependent positional label (the §VII buffer): the consumable region is Low; reading the High region or advancing tail over a secret refutes.'

    static final List<Map> CASES = [
        // PROBE-array (Step 2b — array-element labels, Smith §VII's actual buffer). The element's classification is
        // value-dependent on POSITION and the control fields: L(values[i]) = (head <= i < tail) ? Low : High (the
        // consumable region is Low). The consumer reads values[head] under the availability guard `head < tail`, so
        // the element is Low and the public sink accepts it. (`level`'s first param is the index; the rest bind by
        // name to the control fields, like the scalar @Label(by=) convention.)
        [group: 'P-array', name: 'consume the Low region verifies', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        int head
                        int tail
                        @Label(by = 'level') int[] values
                        static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }
                        @Ensures({ true }) static void process(@Label('Low') int x) { }
                        void consume() {
                            if (head < tail) {
                                process(values[head])      // in bounds (head < tail <= length); L = Low → sink accepts
                            }
                        }
                    }''')],
        // Reading OUTSIDE the consumable region — an index before `head` is High — leaks into the public sink.
        [group: 'P-array', name: 'consume the High region refutes', expect: 'information leak',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        int head
                        int tail
                        @Label(by = 'level') int[] values
                        static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }
                        @Ensures({ true }) static void process(@Label('Low') int x) { }
                        @Requires({ 0 < head })
                        void consume() {
                            process(values[0])             // index 0 is BEFORE [head, tail) → High → REFUTES (in bounds: 0 < length)
                        }
                    }''')],
        // PRODUCER side (§III-A secure-update over the array). The producer declassifies a secret, writes it at
        // `tail`, then advances `tail` — which pulls the element at old.tail INTO the Low region. That is secure
        // only because the value there is Low (declassified): leq(Γ(values[tail]), level(tail, head, tail+1)).
        [group: 'P-array', name: 'producer: declassify, write, advance tail (verifies)', ok: true,
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        int head
                        int tail
                        @Label(by = 'level') int[] values
                        static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }
                        @Requires({ tail < values.length })
                        void produce(@Label('High') int secret) {
                            int msg = Declassify.to('Low', secret)   // §III-E: declassify → Low
                            values[tail] = msg                        // write a Low value at the boundary slot
                            tail = tail + 1                           // §III-A secure-update: old.tail enters Low region
                        }
                    }''')],
        // The leak: advancing `tail` over an UNDECLASSIFIED secret reclassifies a High value to Low — refutes at tail++.
        [group: 'P-array', name: 'producer: advancing tail over an undeclassified secret refutes', expect: 'information leak',
         src: tc('''@Invariant({ 0 <= head && head <= tail && tail <= values.length })
                    class Buffer {
                        enum L { Low, High }
                        static boolean leq(L a, L b) { a == L.Low || b == L.High }
                        static L join(L a, L b) { leq(a, b) ? b : a }
                        int head
                        int tail
                        @Label(by = 'level') int[] values
                        static L level(int i, int head, int tail) { (head <= i && i < tail) ? L.Low : L.High }
                        @Requires({ tail < values.length })
                        void produce(@Label('High') int secret) {
                            values[tail] = secret                     // write a HIGH value at the boundary slot
                            tail = tail + 1                           // reclassifies High → Low: REFUTES
                        }
                    }''')],
    ]
}
