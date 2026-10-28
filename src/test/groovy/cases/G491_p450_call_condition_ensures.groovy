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
 * 'P450 a call's @Ensures in a condition' — a statement's contracted call is hoisted to a local and its @Ensures assumed,
 * but a call in a condition (`if (g(a))`, `g(a) ? … : …`) wasn't: the condition was left untranslated (dropped), or —
 * for an equational @Ensures (`result == E`, Phase 116's combiner) — inlined with its formals bound by value only, so
 * `s != null` in E read the null flag of a name `s`: none of the argument's, or the CALLER's own `s` (unsound). A
 * condition's contracted call is its @Ensures' value now, and a combiner's named or literal argument is spliced into E.
 */
class G491_p450_call_condition_ensures {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 450: a contracted call in a condition (`if (g(a))`, a ternary) carries its @Ensures — `g(a)` promising `a != null` guards `a.size()`, where it was a false NPE alarm — and an equational @Ensures inlined over an argument reads that argument, not a caller's same-named variable (which compiled clean — unsound)."

    static final List<Map> CASES = [

        // Each was a Possible NullPointerException
        [group: "P450 a call's @Ensures in a condition", name: "an if on a call guards what it promises", ok: true,
         src: tc('''class A {
                        static int f(String a) {
                            if (g(a)) return a.size()
                            return 0
                        }
                        @Ensures({ result == (s != null) })
                        static boolean g(String s) { s != null }
                    }''')],

        [group: "P450 a call's @Ensures in a condition", name: "… a ternary on one", ok: true,
         src: tc('''class A {
                        static int f(String a) { g(a) ? a.size() : 0 }
                        @Ensures({ result == (s != null) })
                        static boolean g(String s) { s != null }
                    }''')],

        [group: "P450 a call's @Ensures in a condition", name: "… an @Ensures that only implies it", ok: true,
         src: tc('''class A {
                        static int f(String a) {
                            if (g(a)) return a.size()
                            return 0
                        }
                        @Ensures({ !result || s != null })
                        static boolean g(String s) { s != null && s.size() > 1 }
                    }''')],

        // Unsound before: compiled clean — g(a)'s inlined `s != null` read the caller's own `s`
        [group: "P450 a call's @Ensures in a condition", name: "an inlined @Ensures reads its argument, not a caller's same name",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        static int f(String a, String s) {
                            if (g(a)) return s.size()
                            return 0
                        }
                        @Ensures({ result == (s != null) })
                        static boolean g(String s) { s != null }
                    }''')],

        [group: "P450 a call's @Ensures in a condition", name: "… nor does an implication",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        static int f(String a, String s) {
                            if (g(a)) return s.size()
                            return 0
                        }
                        @Ensures({ !result || s != null })
                        static boolean g(String s) { s != null && s.size() > 1 }
                    }''')],

        // A false alarm before: the guard read the caller's `ys`, not `xs`
        [group: "P450 a call's @Ensures in a condition", name: "an inlined size guard is the argument's", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) {
                            if (g(xs)) return xs[0]
                            return 0
                        }
                        @Ensures({ result == (ys != null && ys.size() > 0) })
                        static boolean g(List<Integer> ys) { ys != null && ys.size() > 0 }
                    }''')],
    ]
}
