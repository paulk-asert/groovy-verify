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
 * 'P448 swapped formal names' — Phase 447 kept a callee's formals from reading the caller's same-named variables, but not
 * a formal whose name an actual mentions: `g(s, a)` into `g(String a, String s)` — the shape of every recursive
 * `gcd(b, a % b)`. Its `a` read the caller's `a`, though the actual is `s`. Every formal is its own now but one passed
 * its own same-named variable (`g(s)`), and an actual's oracles are read in the caller's view of the names.
 */
class G490_p448_swapped_formal_names {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 448: a callee's formal whose name another argument mentions (`g(s, a)` into `g(a, s)`) reads its own argument's nullity, size or set, not the caller's same-named variable's — each swapped @Requires or @Ensures below compiled clean (unsound)."

    static final List<Map> CASES = [

        // Unsound before: each compiled clean — the caller's `a != null` discharged g's, which is about `s`
        [group: "P448 swapped formal names", name: "a swapped @Requires reads its own argument's nullity",
         expect: "Cannot prove precondition of g at this call site",
         src: tc('''class A {
                        @Requires({ a != null })
                        static int f(String a, String s) { g(s, a) }
                        @Requires({ a != null })
                        static int g(String a, String s) { a.size() }
                    }''')],

        [group: "P448 swapped formal names", name: "… and is discharged by it", ok: true,
         src: tc('''class A {
                        @Requires({ s != null })
                        static int f(String a, String s) { g(s, a) }
                        @Requires({ a != null })
                        static int g(String a, String s) { a.size() }
                    }''')],

        [group: "P448 swapped formal names", name: "… its size",
         expect: "Cannot prove precondition of g at this call site",
         src: tc('''class A {
                        @Requires({ a != null && b != null && a.size() > 0 })
                        static int f(List<Integer> a, List<Integer> b) { g(b, a) }
                        @Requires({ a != null && a.size() > 0 })
                        static int g(List<Integer> a, List<Integer> b) { a[0] }
                    }''')],

        [group: "P448 swapped formal names", name: "… its set",
         expect: "Cannot prove precondition of g at this call site",
         src: tc('''class A {
                        @Requires({ a != null && b != null && a.contains(5) })
                        static void f(Set<Integer> a, Set<Integer> b) { g(b, a) }
                        @Requires({ a != null && a.contains(5) })
                        static void g(Set<Integer> a, Set<Integer> b) { }
                    }''')],

        [group: "P448 swapped formal names", name: "a swapped @Ensures is about its own argument",
         expect: "Assertion may not hold: a.contains(5)",
         src: tc('''class A {
                        @Requires({ a != null && b != null && b.contains(5) })
                        static void f(Set<Integer> a, Set<Integer> b) { g(b, a); assert a.contains(5) }
                        @Requires({ a != null && b != null && a.contains(5) })
                        @Ensures({ a.contains(5) })
                        static void g(Set<Integer> a, Set<Integer> b) { }
                    }''')],

        // A formal passed its own same-named variable is that variable
        [group: "P448 swapped formal names", name: "a formal passed its own name is the caller's", ok: true,
         src: tc('''class A {
                        @Requires({ s != null && a != null })
                        static int f(String s, String a) { g(s) }
                        @Requires({ s != null })
                        static int g(String s) { s.size() }
                    }''')],
    ]
}
