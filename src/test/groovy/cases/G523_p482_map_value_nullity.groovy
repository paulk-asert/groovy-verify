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
 * 'P482 a map value's nullity' — Phase 37 lowered {@code xs.get(i) != null} / {@code xs[i] != null} (and the dereference
 * {@code xs.get(i).m()}) to a list's per-element null flags for any container, a map's too: an Integer-keyed map's
 * flags were never cleared by {@code m.put(1, null)}, so {@code @Requires({ m.get(1) != null })} kept {@code m.get(1)}
 * non-null past it, and a String key crashed the method's implicit checks (an Int-indexed array read with a String). Only a
 * list's or an array's elements have the flags now; a map's value dereference is skipped loudly.
 */
class G523_p482_map_value_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 482: a map's `m.get(k)` / `m[k]` no longer reads a list's element null flags (soundness: `m.put(1, null)` left `m.get(1)` non-null, and a String key stopped the method's checks) — its dereference is skipped loudly."

    static final List<Map> CASES = [

        // ---------- an Integer-keyed map: a null put ----------
        [group: "P482 a map value's nullity", name: "a null put, then a call on the value", expect: ['Cannot invoke method length() on null object', 'obligation: m.get(1) != null'], refute: 'fails on:',
         src: tc('''class A {
                        @Requires({ m != null && m.get(1) != null })
                        static int f(Map<Integer, String> m) {
                            m.put(1, null)
                            return m.get(1).length()
                        }
                    }''')],
        [group: "P482 a map value's nullity", name: "… an assertion it's non-null", expect: ['Assertion may not hold: (m.get(1) != null)'], refute: 'fails on:',
         src: tc('''class A {
                        @Requires({ m != null && m.get(1) != null })
                        static int f(Map<Integer, String> m) {
                            m.put(1, null)
                            assert m.get(1) != null
                            return 1
                        }
                    }''')],

        // ---------- a String-keyed map: no internal error ----------
        [group: "P482 a map value's nullity", name: "a String key's value, a call on it", expect: ['Cannot invoke method length() on null object', "obligation: m.get('x') != null", 'fails on: f([:])'], refute: 'internal error',
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { m.get('x').length() }
                    }''')],
        [group: "P482 a map value's nullity", name: "… by subscript", expect: ['Cannot invoke method length() on null object', "obligation: m['x'] != null", 'fails on: f([:])'], refute: 'internal error',
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { m['x'].length() }
                    }''')],
        [group: "P482 a map value's nullity", name: "… an assertion it's non-null", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, String> m = [x: 'a']
                            assert m.get('x') != null
                            return 1
                        }
                    }''')],
        [group: "P482 a map value's nullity", name: "… and the method's other checks run", expect: ['Division by zero', "obligation: n != 0"], refute: 'internal error',
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, String> m, int n) {
                            assert m.get('x') != null
                            return 100.intdiv(n)
                        }
                    }''')],
        [group: "P482 a map value's nullity", name: "… a character of the value", expect: ['fails on: f([:])'], refute: 'internal error',
         src: tc('''class A {
                        @Requires({ m != null })
                        static String f(Map<String, String> m) { m['x'][0] }
                    }''')],

        // ---------- a list's and an array's elements keep their flags ----------
        [group: "P482 a map value's nullity", name: "a list's element stated non-null", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs.get(0) != null })
                        static int f(List<String> xs) { xs.get(0).length() }
                    }''')],
        [group: "P482 a map value's nullity", name: "… by subscript", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<String> xs) { xs[0].length() }
                    }''')],
        [group: "P482 a map value's nullity", name: "an array's element stated non-null", ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 && a[0] != null })
                        static int f(String[] a) { a[0].length() }
                    }''')],
        [group: "P482 a map value's nullity", name: "a list's element unstated", expect: ['Cannot invoke method length() on null object', 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<String> xs) { xs.get(0).length() }
                    }''')],
    ]
}
