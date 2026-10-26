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
 * 'P429 uninitialised local' — a local declared without a value (`int n`) skipped the postcondition path ("uninitialised
 * local 'n'"), so the common branch-assigned shape `int n; if (b) n = 1 else n = p; return n` was never checked.
 *
 * Groovy gives such a local its type's default — measured on Groovy 6, dynamic, `@TypeChecked` and `@CompileStatic`
 * alike: 0 for an integral primitive, false for a boolean, null for a reference or boxed type. The declaration is now
 * an assignment of that default, so a path that leaves it unwritten is checked against it.
 */
class G471_p429_uninitialised_local {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 429: a local declared without a value holds Groovy's default (0, false, or null) on the postcondition path, so a branch-assigned `int n; if (b) n = 1 else n = p` is checked rather than skipped."

    static final List<Map> CASES = [

        // Skipped before: "uninitialised local 'n'"
        [group: "P429 uninitialised local", name: "a local assigned on every branch",
         ok: true,
         src: tc('''class A {
                        @Requires({ p > 0 })
                        @Ensures({ result > 0 })
                        static int f(boolean b, int p) { int n; if (b) { n = 1 } else { n = p }; return n }
                        @Requires({ p != null })
                        @Ensures({ result != null })
                        static String g(boolean b, String p) { String s; if (b) { s = 'x' } else { s = p }; return s }
                    }''')],

        [group: "P429 uninitialised local", name: "… and refuted when a branch's value breaks it",
         expect: ["Cannot prove postcondition of f", "ensured: (result > 0)", "fails on: f(false, 0)"],
         src: tc('''class A {
                        @Requires({ p >= 0 })
                        @Ensures({ result > 0 })
                        static int f(boolean b, int p) { int n; if (b) { n = 1 } else { n = p }; return n }
                    }''')],

        // The unwritten path holds the default: an int's 0
        [group: "P429 uninitialised local", name: "an int left unwritten is 0",
         expect: ["Cannot prove postcondition of f", "ensured: (result > 0)", "fails on: f(false)"],
         src: tc('''class A {
                        @Ensures({ result > 0 })
                        static int f(boolean b) { int n; if (b) { n = 1 }; return n }
                    }''')],

        [group: "P429 uninitialised local", name: "the defaults themselves",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == 0 })
                        static int f() { int n; return n }
                        @Ensures({ result == 0 })
                        static long g() { long n; return n }
                        @Ensures({ !result })
                        static boolean h() { boolean z; return z }
                        @Ensures({ result == null })
                        static String k() { String s; return s }
                        @Ensures({ result })
                        static boolean m() { Integer n; return n == null }
                    }''')],

        // A reference left unwritten is null
        [group: "P429 uninitialised local", name: "a String left unwritten is null",
         expect: ["Cannot prove postcondition of f", "ensured: (result != null)", "fails on: f(false)"],
         src: tc('''class A {
                        @Ensures({ result != null })
                        static String f(boolean b) { String s; if (b) { s = 'x' }; return s }
                    }''')],
    ]
}
