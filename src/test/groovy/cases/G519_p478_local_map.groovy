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

/**
 * 'P478 a local map' — a typed local {@code Map<K, V>} wasn't a map to the checker: only parameters and fields were. Its
 * reads and stores took the list path, so a String key reached an Int-indexed array ({@code m.put('x', 0)} then
 * {@code m.get('x')} stopped the method's implicit checks with an internal error), and an Integer key's puts were lost.
 * And {@code m.x = v} wasn't seen as a put at all: a literal-bound map's {@code m.x} still read the literal, so
 * {@code [x: 1]}, {@code m.x = 0}, {@code 100.intdiv(m.x)} proved. A local map assigned only where it's declared is now
 * a map, a literal's entries are its contents, and {@code m.x} on a String-keyed map is {@code m['x']}.
 */
class G519_p478_local_map {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 478: a typed local map (`Map<String, Integer> m = [x: 1]`) is a map — its puts and reads are modelled (a String key stopped the method's checks with an internal error) — and `m.x = v` is a put (soundness: it was lost, and `m.x` still read the literal's value)."

    static final List<Map> CASES = [

        // ---------- a typed local map is a map: its puts and reads ----------
        [group: "P478 a local map", name: "a put then a get", expect: ['Possible ArithmeticException', 'fails on: f('], refute: 'internal error',
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.put('x', 0)
                            return 100.intdiv(m.get('x'))
                        }
                    }''')],
        [group: "P478 a local map", name: "… a subscript store", expect: ['Possible ArithmeticException', 'fails on: f(0)'], refute: 'internal error',
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m['x'] = n
                            return 100.intdiv(m['x'])
                        }
                    }''')],
        [group: "P478 a local map", name: "… into an empty map", expect: ['Possible ArithmeticException', 'fails on: f(0)'], refute: 'internal error',
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [:]
                            m.put('x', n)
                            return 100.intdiv(m.get('x'))
                        }
                    }''')],
        [group: "P478 a local map", name: "… an Integer-keyed one", expect: ['Possible ArithmeticException', 'fails on: f(0)'], refute: 'doesn\'t model',
         src: tc('''class A {
                        static int f(int n) {
                            Map<Integer, Integer> m = [(1): 1]
                            m.put(1, n)
                            return 100.intdiv(m.get(1))
                        }
                    }''')],
        [group: "P478 a local map", name: "a literal unwritten still folds", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 2]
                            return 100.intdiv(m.get('x'))
                        }
                    }''')],
        [group: "P478 a local map", name: "the size counts a new key", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.put('y', 2)
                            assert m.size() == 2
                            return 0
                        }
                    }''')],
        [group: "P478 a local map", name: "… and not an old one", expect: ['Assertion may not hold', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.put('x', 2)
                            assert m.size() == 2
                            return 0
                        }
                    }''')],

        // ---------- `m.x = v` is a put (soundness: it was lost, and m.x read the literal) ----------
        [group: "P478 a local map", name: "a property store over the literal", expect: ['Possible ArithmeticException', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.x = 0
                            return 100.intdiv(m.x)
                        }
                    }''')],
        [group: "P478 a local map", name: "… read by get", expect: ['Possible ArithmeticException', 'fails on: f(0)'],
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.x = n
                            return 100.intdiv(m.get('x'))
                        }
                    }''')],
        [group: "P478 a local map", name: "… a subscript store read as a property", expect: ['Possible ArithmeticException', 'fails on: f(0)'],
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m['x'] = n
                            return 100.intdiv(m.x)
                        }
                    }''')],
        [group: "P478 a local map", name: "… an assert after it checked", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.x = 2
                            assert m.x == 2
                            return 0
                        }
                    }''')],
        [group: "P478 a local map", name: "… past a re-assignment", expect: ['Possible ArithmeticException', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            int k = 1
                            k = 2
                            Map<String, Integer> m = [x: 1]
                            m.x = 0
                            return 100.intdiv(m.x + k - 2)
                        }
                    }''')],
        [group: "P478 a local map", name: "… a call's precondition sees it", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.x = 2
                            return g(m.x)
                        }
                        @Requires({ v != 0 })
                        static int g(int v) { 100.intdiv(v) }
                    }''')],
        [group: "P478 a local map", name: "… past a loop, a put", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.put('x', 2)
                            int s = 0
                            for (int i = 0; i < n; i++) { s += i }
                            return g(m.get('x'))
                        }
                        @Requires({ v != 0 })
                        static int g(int v) { 100.intdiv(v) }
                    }''')],
        [group: "P478 a local map", name: "another key keeps the literal's value", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.y = 0
                            return 100.intdiv(m.x)
                        }
                    }''')],
        [group: "P478 a local map", name: "… in an if's arm", expect: ['Possible ArithmeticException', 'fails on: f(6)'],
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            if (n > 5) m.x = 0
                            return 100.intdiv(m.x)
                        }
                    }''')],
        [group: "P478 a local map", name: "… in a loop", expect: ['Possible ArithmeticException', 'fails on: f(1)'],
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            for (int i = 0; i < n; i++) { m.x = i }
                            return 100.intdiv(m.x)
                        }
                    }''')],
    ]
}
