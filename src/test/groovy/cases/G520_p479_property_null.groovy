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
 * 'P479 a property read on null' — Phase 415 gave an array's {@code .length} its receiver's null obligation, and left every
 * other property: {@code p.v} and a map's {@code m.x} on a null parameter or local throw ("Cannot get property 'v' on
 * null object"; a plain store "Cannot set property"; measured on Groovy 6, dynamic and @TypeChecked) and were checked
 * for nothing. Any property of a parameter or local now carries it. A callee's postcondition that reads a property of
 * {@code result} wherever it holds would throw on a null one, so its value is non-null after a call that returns.
 */
class G520_p479_property_null {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 479 (soundness): a property read or stored on a parameter or local (`b.v`, a map's `m.x`) carries its receiver's null obligation, as an array's `.length` did — it throws on null, and was checked for nothing; a callee whose postcondition reads `result.p` returns non-null."

    static final List<Map> CASES = [

        // ---------- a property of a parameter or local may be read, or stored, on null ----------
        [group: "P479 a property read on null", name: "an object's property read", expect: ["Cannot get property 'v' on null object", 'obligation: b != null', 'fails on: f(null)'],
         src: tc('''class A {
                        static int f(B b) {
                            return b.v
                        }
                    }
                    class B { int v }''')],
        [group: "P479 a property read on null", name: "… stored", expect: ["Cannot set property 'v' on null object", 'fails on: f(null)'],
         src: tc('''class A {
                        static int f(B b) {
                            b.v = 1
                            return 0
                        }
                    }
                    class B { int v }''')],
        [group: "P479 a property read on null", name: "… a compound store reads it first", expect: ["Cannot get property 'v' on null object", 'fails on: f(null)'],
         src: tc('''class A {
                        static int f(B b) {
                            b.v += 1
                            return 0
                        }
                    }
                    class B { int v }''')],
        [group: "P479 a property read on null", name: "a map parameter's `m.x`", expect: ["Cannot get property 'x' on null object", 'fails on: f(null)'],
         src: tc('''class A {
                        static int f(Map<String, Integer> m) {
                            return m.x == null ? 0 : 1
                        }
                    }''')],
        [group: "P479 a property read on null", name: "… stored", expect: ["Cannot set property 'x' on null object", 'fails on: f(null)'],
         src: tc('''class A {
                        static int f(Map<String, Integer> m) {
                            m.x = 1
                            return 0
                        }
                    }''')],
        [group: "P479 a property read on null", name: "a local from a call", expect: ["Cannot get property 'v' on null object"],
         src: tc('''class A {
                        static int f(int n) {
                            B b = g(n)
                            return b.v
                        }
                        static B g(int n) { n > 0 ? new B() : null }
                    }
                    class B { int v }''')],

        // ---------- ruled out ----------
        [group: "P479 a property read on null", name: "a guard", ok: true,
         src: tc('''class A {
                        static int f(B b) {
                            if (b == null) return 0
                            return b.v
                        }
                    }
                    class B { int v }''')],
        [group: "P479 a property read on null", name: "a precondition", ok: true,
         src: tc('''class A {
                        @Requires({ b != null })
                        static int f(B b) {
                            b.v = 1
                            return b.v
                        }
                    }
                    class B { int v }''')],
        [group: "P479 a property read on null", name: "safe navigation", ok: true,
         src: tc('''class A {
                        static int f(Map<String, Integer> m) {
                            return m?.x == null ? 0 : 1
                        }
                    }''')],
        [group: "P479 a property read on null", name: "a literal local", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            return m.x
                        }
                    }''')],
        [group: "P479 a property read on null", name: "a primitive's property", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            return n.class == Integer ? 1 : 0
                        }
                    }''')],

        // ---------- a call's value: its postcondition reads `result.p`, so a null one throws there ----------
        [group: "P479 a property read on null", name: "a callee whose postcondition reads its result's property", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            P r = mk(n)
                            return r.v
                        }
                        @Ensures({ result.v == n })
                        static P mk(int n) { new P(n) }
                    }
                    record P(int v) {}''')],
        [group: "P479 a property read on null", name: "… only right of an ||, so not always", expect: ["Cannot get property 'v' on null object"],
         src: tc('''class A {
                        static int f(int n) {
                            P r = mk(n)
                            return r.v
                        }
                        @Ensures({ n < 0 || result.v == n })
                        static P mk(int n) { new P(n) }
                    }
                    record P(int v) {}''')],
        [group: "P479 a property read on null", name: "… its left, so always", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            P r = mk(n)
                            return r.v
                        }
                        @Ensures({ result.v == n || n < 0 })
                        static P mk(int n) { new P(n) }
                    }
                    record P(int v) {}''')],
        [group: "P479 a property read on null", name: "… a result that may be null", expect: ["Cannot get property 'v' on null object"],
         src: tc('''class A {
                        static int f(int n) {
                            P r = mk(n)
                            return r.v
                        }
                        @Ensures({ result == null || result.v == n })
                        static P mk(int n) { n > 0 ? new P(n) : null }
                    }
                    record P(int v) {}''')],
    ]
}
