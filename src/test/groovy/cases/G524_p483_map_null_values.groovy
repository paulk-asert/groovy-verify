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
 * 'P483 a map's null values' — Phase 482 skipped a map value's dereference loudly: its nullity wasn't modelled. A map's
 * {@code m.get(k)} / {@code m[k]} (and a String-keyed {@code m.x}) is null when {@code k} isn't a key or the value put
 * there is null — measured on Groovy 6.0.0, {@code [x: 'a'].get('y').length()} and {@code [x: null].get('x').length()}
 * both throw "Cannot invoke method length() on null object". Each map now carries a value-null flag per key, through
 * puts, literals, havocs and call framing.
 */
class G524_p483_map_null_values {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 483: a map's `m.get(k)` / `m[k]` is null when `k` isn't a key or a null was put there — modelled through puts, literals, havocs and call framing, so `@Requires({ m.get('x') != null })` discharges `m.get('x').length()` and `m.put('x', null)` refutes it."

    static final List<Map> CASES = [

        // ---------- a stated value ----------
        [group: "P483 a map's null values", name: "a value stated non-null", ok: true,
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, String> m) { m.get('x').length() }
                    }''')],
        [group: "P483 a map's null values", name: "… stated by subscript, read by get", ok: true,
         src: tc('''class A {
                        @Requires({ m != null && m['x'] != null })
                        static int f(Map<String, String> m) { m.get('x').length() }
                    }''')],
        [group: "P483 a map's null values", name: "… stated as a property", ok: true,
         src: tc('''class A {
                        @Requires({ m != null && m.x != null })
                        static int f(Map<String, String> m) { m['x'].length() }
                    }''')],
        [group: "P483 a map's null values", name: "… unstated, an assertion", expect: ["Assertion may not hold: (m.get('x') != null)", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { assert m.get('x') != null; 1 }
                    }''')],
        [group: "P483 a map's null values", name: "… a key isn't a non-null value", expect: ['Cannot invoke method length() on null object', "obligation: m.get('x') != null"],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { m.containsKey('x') ? m.get('x').length() : 0 }
                    }''')],
        [group: "P483 a map's null values", name: "… a guard", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { m.get('x') != null ? m.get('x').length() : 0 }
                    }''')],

        // ---------- puts ----------
        [group: "P483 a map's null values", name: "a non-null put", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { m.put('x', 'ab'); m.get('x').length() }
                    }''')],
        [group: "P483 a map's null values", name: "a null put", expect: ['Cannot invoke method length() on null object', "obligation: m.get('x') != null", 'fails on: f([x: ""])'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, String> m) { m.put('x', null); m.get('x').length() }
                    }''')],
        [group: "P483 a map's null values", name: "… by subscript", expect: ['Cannot invoke method length() on null object', "obligation: m.get('x') != null"],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, String> m) { m['x'] = null; m.get('x').length() }
                    }''')],
        [group: "P483 a map's null values", name: "… another key's", ok: true,
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, String> m) { m.put('y', null); m.get('x').length() }
                    }''')],
        [group: "P483 a map's null values", name: "a primitive's put is never null", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [:]
                            m.put('x', n)
                            assert m.get('x') != null
                            return 1
                        }
                    }''')],
        [group: "P483 a map's null values", name: "a parameter's put is its nullity", expect: ['Cannot invoke method length() on null object', 'fails on: f([x: ""], null)'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m, String s) { m.put('x', s); m.get('x').length() }
                    }''')],
        [group: "P483 a map's null values", name: "… stated non-null", ok: true,
         src: tc('''class A {
                        @Requires({ m != null && s != null })
                        static int f(Map<String, String> m, String s) { m.put('x', s); m.get('x').length() }
                    }''')],
        [group: "P483 a map's null values", name: "a put in a loop", expect: ['Cannot invoke method length() on null object', "obligation: m.get('x') != null"],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null && n >= 0 })
                        static int f(Map<String, String> m, int n) {
                            for (int i = 0; i < n; i++) { m['x'] = null }
                            return m.get('x').length()
                        }
                    }''')],

        // ---------- a local literal ----------
        [group: "P483 a map's null values", name: "a literal's key", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, String> m = [x: 'a']
                            return m.get('x').length()
                        }
                    }''')],
        [group: "P483 a map's null values", name: "… a missing key", expect: ['Cannot invoke method length() on null object', "obligation: m.get('y') != null", 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, String> m = [x: 'a']
                            return m.get('y').length()
                        }
                    }''')],
        [group: "P483 a map's null values", name: "… a null value", expect: ['Cannot invoke method length() on null object', "obligation: m['x'] != null", 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, String> m = [x: (String) null]
                            return m['x'].length()
                        }
                    }''')],

        // ---------- a call's precondition ----------
        [group: "P483 a map's null values", name: "a callee's stated value, met by a put", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { m.put('x', 'a'); g(m) }
                        @Requires({ m != null && m.get('x') != null })
                        static int g(Map<String, String> m) { m.get('x').length() }
                    }''')],
        [group: "P483 a map's null values", name: "… broken by a null put", expect: ["m.get('x') != null"],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { m.put('x', null); g(m) }
                        @Requires({ m != null && m.get('x') != null })
                        static int g(Map<String, String> m) { m.get('x').length() }
                    }''')],

        // ---------- a call's effects, a loop body, an unwritten map's repro ----------
        [group: "P483 a map's null values", name: "a key kept, its value nulled by a callee", expect: ['Cannot invoke method length() on null object', "obligation: m.get('x') != null"],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, String> m) {
                            clobber(m)
                            return m.containsKey('x') ? m.get('x').length() : 0
                        }
                        static void clobber(Map<String, String> m) { if (m != null) m.put('x', null) }
                    }''')],
        [group: "P483 a map's null values", name: "a callee's postcondition over the map's value", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) {
                            m.put('x', 'a')
                            assert has(m)
                            return 1
                        }
                        @Requires({ mm != null })
                        @Ensures({ result == (mm.get('x') != null) })
                        static boolean has(Map<String, String> mm) { mm.get('x') != null }
                    }''')],
        [group: "P483 a map's null values", name: "a put, then a read, in a loop body", ok: true,
         src: tc('''class A {
                        @Requires({ m != null && n >= 0 })
                        static int f(Map<String, String> m, int n) {
                            int t = 0
                            for (int i = 0; i < n; i++) {
                                m['x'] = 'ab'
                                t += m.get('x').length()
                            }
                            return t
                        }
                    }''')],
        [group: "P483 a map's null values", name: "an unwritten map's stated value", expect: ['Division by zero', 'fails on: f([x: ""], 0)'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, String> m, int n) { m.get('x').length() + 100.intdiv(n) }
                    }''')],
    ]
}
