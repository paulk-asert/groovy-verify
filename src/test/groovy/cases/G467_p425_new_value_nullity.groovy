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
 * 'P425 new value nullity' — a value whose nullity alone the encoder knows (a {@code new StringBuilder()}, a
 * {@code null}) had no value to translate, so a callee's {@code return new StringBuilder()} skipped its postcondition
 * and a {@code g(new StringBuilder())} or {@code g(null)} argument skipped the precondition, both loudly. After the
 * skipped precondition, {@code StringBuilder m = g(new StringBuilder()); m.append('x')} reported a possible null with
 * no failing call, though g promised {@code result != null}.
 *
 * Each is an opaque value now, with its nullity known: on the return side `result`'s, at the call site the formal's,
 * for the precondition and for the @Ensures assumed after the call. A claim on the value itself stays outside the
 * fragment.
 */
class G467_p425_new_value_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 425: `return new StringBuilder()` proves `@Ensures({ result != null })` and `g(new StringBuilder())` / `g(null)` discharge or refute `@Requires({ p != null })`, an opaque value with a known nullity, where both skipped; a claim on the value stays outside the fragment."

    static final List<Map> CASES = [

        // Skipped before: the returned value didn't translate
        [group: "P425 new value nullity", name: "a returned `new` is non-null",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result != null })
                        static StringBuilder g() { return new StringBuilder() }
                        @Ensures({ result != null })
                        static StringBuilder h(boolean b) { if (b) return new StringBuilder('x'); return new StringBuilder() }
                    }''')],

        [group: "P425 new value nullity", name: "… so `result == null` refutes",
         expect: ["Cannot prove postcondition of g", "ensured: (result == null)"],
         src: tc('''class A {
                        @Ensures({ result == null })
                        static StringBuilder g() { return new StringBuilder() }
                    }''')],

        [group: "P425 new value nullity", name: "… and a `null` path beside it fails on its call",
         expect: ["Cannot prove postcondition of g", "fails on: g(false)"],
         src: tc('''class A {
                        @Ensures({ result != null })
                        static StringBuilder g(boolean b) { if (b) return new StringBuilder(); return null }
                    }''')],

        [group: "P425 new value nullity", name: "a claim on the returned value stays outside",
         expect: ["Skipped verification of postcondition for g", "outside fragment"],
         src: tc('''class A {
                        @Ensures({ result.length() == 0 })
                        static StringBuilder g() { return new StringBuilder() }
                    }''')],

        // Skipped before, then `m.append` showed "no failing call"
        [group: "P425 new value nullity", name: "a `new` argument meets `p != null`, and the call's promise holds after",
         ok: true,
         src: tc('''class A {
                        @Requires({ p != null })
                        @Ensures({ result != null })
                        static StringBuilder g(StringBuilder p) { p }
                        static void f() { StringBuilder m = g(new StringBuilder()); m.append('x') }
                    }''')],

        [group: "P425 new value nullity", name: "a `null` argument fails `p != null`",
         expect: ["Cannot prove precondition of g", "required: (p != null)", "fails on: f()"],
         src: tc('''class A {
                        @Requires({ p != null })
                        static int g(StringBuilder p) { 1 }
                        static int f() { g(null) }
                    }''')],

        [group: "P425 new value nullity", name: "the callee's @Ensures reads the argument's nullity",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == (p == null) })
                        static boolean g(StringBuilder p) { p == null }
                        @Ensures({ !result })
                        static boolean f() { boolean b = g(new StringBuilder()); return b }
                        @Ensures({ result })
                        static boolean h() { boolean b = g(null); return b }
                    }''')],

        [group: "P425 new value nullity", name: "… and refutes the contrary",
         expect: ["Cannot prove postcondition of f", "fails on: f()"],
         src: tc('''class A {
                        @Ensures({ result == (p == null) })
                        static boolean g(StringBuilder p) { p == null }
                        @Ensures({ result })
                        static boolean f() { boolean b = g(new StringBuilder()); return b }
                    }''')],

        // The formal's nullity is the callee's: the caller's own `p` keeps its own
        [group: "P425 new value nullity", name: "the formal's nullity doesn't reach a caller name it shares",
         expect: ["Cannot invoke method append() on null object", "fails on: f(null)"],
         src: tc('''class A {
                        @Ensures({ result == (p == null) })
                        static boolean g(StringBuilder p) { p == null }
                        static void f(StringBuilder p) { boolean b = g(new StringBuilder()); p.append('x') }
                    }''')],

        [group: "P425 new value nullity", name: "a claim on the argument's value stays outside",
         expect: ["Skipped verification of precondition for g", "outside fragment"],
         src: tc('''class A {
                        @Requires({ p.length() == 0 })
                        static int g(StringBuilder p) { 1 }
                        static int f() { g(new StringBuilder()) }
                    }''')],
    ]
}
