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
 * 'P421 call result nullity' — a contracted call's {@code result == null} read one name-keyed flag ({@code result?null})
 * that every call on a path shared, and the name its value was assigned to never took it. So two callees promising
 * {@code result != null} and {@code result == null} made the path vacuous: {@code @Ensures({ result == 1 })} proved of
 * {@code return x}. And {@code StringBuilder m = g(); m.append('x')} reported a null that g's
 * {@code @Ensures({ result != null })} rules out (a list's call did carry it, Phase 225).
 *
 * Each call's flag is its own now (the caller's own {@code result} put back after), and the name assigned the call's
 * value takes it — a declaration, a reassignment, a loop body's, a returned call's.
 */
class G463_p421_call_result_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 421: each contracted call's `result == null` is its own (two callees' contrary promises no longer make the path vacuous), and the local assigned the call's value — declared, reassigned, in a loop, returned — takes what its @Ensures says."

    /** Callees whose bodies prove their promises. */
    static final String LIB = '''
                        @Requires({ p != null })
                        @Ensures({ result != null })
                        static StringBuilder g(StringBuilder p) { p }
                        @Ensures({ result == null })
                        static StringBuilder h() { null }
                        static StringBuilder u(StringBuilder p) { p }
    '''

    static final List<Map> CASES = [

        // g's promise and h's were one flag, contradicting each other: anything proved
        [group: "P421 call result nullity", name: "two calls' promises are their own",
         expect: ["Cannot prove postcondition of f", "fails on: f("],
         src: tc('''class A {
                        @Ensures({ result != null })
                        static String g() { 'a' }
                        @Ensures({ result == null })
                        static String h() { null }
                        @Ensures({ result == 1 })
                        static int f(int x) {
                            String a = g()
                            String b = h()
                            return x
                        }
                    }''')],

        [group: "P421 call result nullity", name: "a non-null @Ensures makes the local non-null",
         ok: true,
         src: tc("""class A { ${LIB}
                        @Requires({ p != null })
                        static void f(StringBuilder p) {
                            StringBuilder m = g(p)
                            m.append('x')
                        }
                    }""")],

        [group: "P421 call result nullity", name: "… reassigned too",
         ok: true,
         src: tc("""class A { ${LIB}
                        @Requires({ p != null })
                        static void f(StringBuilder p, StringBuilder q) {
                            StringBuilder m = q
                            m = g(p)
                            m.append('x')
                        }
                    }""")],

        [group: "P421 call result nullity", name: "a null @Ensures makes it null",
         expect: ["Cannot invoke method append() on null object", "obligation: m != null", "fails on: f()"],
         src: tc("""class A { ${LIB}
                        static void f() {
                            StringBuilder m = h()
                            m.append('x')
                        }
                    }""")],

        [group: "P421 call result nullity", name: "an uncontracted call's says nothing",
         expect: ["Cannot invoke method append() on null object", "obligation: m != null"],
         src: tc("""class A { ${LIB}
                        static void f(StringBuilder p) {
                            StringBuilder m = u(p)
                            m.append('x')
                        }
                    }""")],

        [group: "P421 call result nullity", name: "two locals take each call's own",
         expect: ["Cannot invoke method append() on null object", "obligation: b != null", "fails on: f(new StringBuilder())"],
         refute: "obligation: a != null",
         src: tc("""class A { ${LIB}
                        @Requires({ p != null })
                        static void f(StringBuilder p) {
                            StringBuilder a = g(p)
                            StringBuilder b = h()
                            b.append('y')
                            a.append('x')
                        }
                    }""")],

        // The postcondition's path binds it too
        [group: "P421 call result nullity", name: "a postcondition reads it",
         ok: true,
         src: tc("""class A { ${LIB}
                        @Requires({ p != null })
                        @Ensures({ result })
                        static boolean f(StringBuilder p, StringBuilder q) {
                            StringBuilder m = q
                            m = g(p)
                            return m != null
                        }
                    }""")],

        // ── in a loop, and returned ──

        [group: "P421 call result nullity", name: "a loop body's call",
         ok: true,
         src: tc("""class A { ${LIB}
                        @Requires({ p != null })
                        static void f(StringBuilder p, int n) {
                            for (int i = 0; i < n; i++) {
                                StringBuilder m = g(p)
                                m.append('x')
                            }
                        }
                    }""")],

        [group: "P421 call result nullity", name: "… and one promising null",
         expect: ["Cannot invoke method append() on null object", "fails on: f(1)"],
         src: tc("""class A { ${LIB}
                        static void f(int n) {
                            for (int i = 0; i < n; i++) {
                                StringBuilder m = h()
                                m.append('x')
                            }
                        }
                    }""")],

        [group: "P421 call result nullity", name: "a returned call's promise is the method's",
         ok: true,
         src: tc("""class A { ${LIB}
                        @Requires({ p != null })
                        @Ensures({ result != null })
                        static StringBuilder f(StringBuilder p) { g(p) }
                    }""")],

        [group: "P421 call result nullity", name: "… and refutes when it promises null",
         expect: ["Cannot prove postcondition of f", "ensured: (result != null)"],
         src: tc("""class A { ${LIB}
                        @Ensures({ result != null })
                        static StringBuilder f() { h() }
                    }""")],
    ]
}
