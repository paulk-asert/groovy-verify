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
 * 'P422 safe navigation' — `x?.m(args)` on a null x is null: no call, and its arguments aren't evaluated (measured,
 * Groovy 6, dynamic, @TypeChecked and @CompileStatic). It carried x's null obligation as `x.m()` does, so
 * `xs?.size()` reported "Cannot invoke method size() on null object" (fails on: f(null), which returns null).
 *
 * That false positive hid a soundness hole: the encoder read `x?.m()` as `x.m()`, so once the obligation went,
 * `@Ensures({ result >= 0 }) Integer f(List xs) { xs?.size() }` proved, and f(null) returns null. Its value is the
 * call's when x isn't null; when it is, an integer's is below every number (Groovy's `null < 0`), its truth false, and
 * any other value unconstrained. What the call and its arguments oblige holds only when x isn't null, and the
 * receiver's own is evaluated either way. Where the null value is used as one that throws on null (`xs?.size() + 1`:
 * "Cannot execute null+1"; `int n = xs?.size()`), x keeps its obligation; elsewhere it has none.
 */
class G464_p422_safe_navigation {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 422: `x?.m(args)` carries no null obligation on x where its null value is harmless (a statement, a comparison, a condition, a concatenation, an Elvis, a reference's value), and keeps it where a null throws (arithmetic, an int); what the call and its arguments oblige holds only when x isn't null; its value is null when x is, below every number in a comparison and false in a condition."

    static final List<Map> CASES = [

        [group: "P422 safe navigation", name: "a safe call carries no null obligation",
         ok: true,
         src: tc('''class A {
                        static Integer f(List<Integer> xs) { xs?.size() }
                        static void g(StringBuilder sb) { sb?.append('x') }
                    }''')],

        // null?.isEmpty() is null, which is false: the size() is reached with a null
        [group: "P422 safe navigation", name: "… but the plain call after it does",
         expect: ["Cannot invoke method size() on null object", "fails on: f(null)"],
         refute: ["isEmpty()", "clear()"],
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            if (xs?.isEmpty()) return 0
                            return xs.size()
                        }
                        static int g(List<Integer> xs) {
                            xs?.clear()
                            return xs.size()
                        }
                    }''')],

        // ── where its null value is used ──

        // Groovy throws on these: `Cannot execute null+1`, `Cannot cast 'null' to class 'int'`
        [group: "P422 safe navigation", name: "a null used as a number still throws",
         expect: ["xs?.size() is null when xs is, and a null throws where it's used", "obligation: xs != null",
                  "fails on: f(null)", "fails on: g(null)", "fails on: h(null)"],
         src: tc('''class A {
                        static def f(List<Integer> xs) { xs?.size() + 1 }
                        static int g(List<Integer> xs) { int n = xs?.size(); return n }
                        static int h(List<Integer> xs) { xs?.size() }
                    }''')],

        [group: "P422 safe navigation", name: "where a null is harmless, nothing is reported",
         ok: true,
         src: tc('''class A {
                        static int f(List<Integer> xs) { if (xs?.size() > 0) return xs[0]; return 0 }
                        static int g(List<Integer> xs) { int n = xs?.size() ?: 0; return n }
                        static String h(String s) { s?.trim() + 'x' }
                        static Integer i(String s) { s?.trim()?.length() }
                        static int j(List<Integer> xs) { if (!xs?.isEmpty()) return 1; return 0 }
                    }''')],

        // Groovy orders null below every number: `null < 0`, `!(null >= -5)`
        [group: "P422 safe navigation", name: "a comparison reads null below every number",
         ok: true,
         src: tc('''class A {
                        @Ensures({ xs != null || result })
                        static boolean f(List<Integer> xs) { xs?.size() < 0 }
                    }''')],

        [group: "P422 safe navigation", name: "… one way only",
         expect: ["Cannot prove postcondition of f", "fails on: f(null)"],
         src: tc('''class A {
                        @Ensures({ xs != null || result })
                        static boolean f(List<Integer> xs) { xs?.size() >= -5 }
                    }''')],

        // `if (null)` doesn't run its branch
        [group: "P422 safe navigation", name: "a condition reads its null as false",
         ok: true,
         src: tc('''class A {
                        @Ensures({ xs != null || result == 0 })
                        static int f(List<Integer> xs) { if (xs?.isEmpty()) return 1; return 0 }
                        @Ensures({ xs != null || result == 0 })
                        static int g(List<Integer> xs) { if (xs?.isEmpty() || false) return 1; return 0 }
                    }''')],

        // A Boolean's null isn't false as a value (`null == true` is false): the claim refutes, no call shown
        [group: "P422 safe navigation", name: "a boolean's null value is no truth value",
         expect: ["Cannot prove postcondition of f", "no failing call: the failure rests on xs?.isEmpty"],
         src: tc('''class A {
                        @Requires({ xs == null || xs.isEmpty() })
                        @Ensures({ result == true })
                        static Boolean f(List<Integer> xs) { xs?.isEmpty() }
                    }''')],

        // ── what holds only when the receiver isn't null ──

        [group: "P422 safe navigation", name: "a non-null receiver's bounds still count",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f([])"],
         src: tc('''class A {
                        static Integer f(List<Integer> xs) { xs?.get(5) }
                    }''')],

        // On a null xs the get isn't called: its size is no constraint
        [group: "P422 safe navigation", name: "… and only when it isn't null",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs == null || xs.size() > 5 })
                        static Integer f(List<Integer> xs) { xs?.get(5) }
                    }''')],

        [group: "P422 safe navigation", name: "an argument is evaluated only on a non-null receiver",
         expect: ["Cannot invoke method size() on null object", "obligation: xs != null",
                  "fails on: f(new StringBuilder(), null)"],
         refute: "append()",
         src: tc('''class A {
                        static void f(StringBuilder sb, List<Integer> xs) { sb?.append(xs.size()) }
                    }''')],

        [group: "P422 safe navigation", name: "… so a precondition for that case is enough",
         ok: true,
         src: tc('''class A {
                        @Requires({ sb == null || xs != null })
                        static void f(StringBuilder sb, List<Integer> xs) { sb?.append(xs.size()) }
                    }''')],

        // The receiver itself is evaluated either way: a[0] on an empty array throws
        [group: "P422 safe navigation", name: "the receiver's own obligation is unguarded",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f(new String[0])"],
         src: tc('''class A {
                        @Requires({ a != null })
                        static Integer f(String[] a) { a[0]?.length() }
                    }''')],

        // ── its value ──

        // Read as xs.size() it proved, and f(null) returns null
        [group: "P422 safe navigation", name: "a safe call's value is null on a null receiver",
         expect: ["Cannot prove postcondition of f", "ensured: (result >= 0)", "fails on: f(null)"],
         src: tc('''class A {
                        @Ensures({ result >= 0 })
                        static Integer f(List<Integer> xs) { xs?.size() }
                    }''')],

        [group: "P422 safe navigation", name: "… so it may not be non-null",
         expect: ["Cannot prove postcondition of f", "ensured: (result != null)", "fails on: f(null)"],
         src: tc('''class A {
                        @Ensures({ result != null })
                        static Integer f(List<Integer> xs) { xs?.size() }
                    }''')],

        [group: "P422 safe navigation", name: "… and is the call's otherwise",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == null || result >= 0 })
                        static Integer f(List<Integer> xs) { xs?.size() }
                        @Requires({ xs != null })
                        @Ensures({ result >= 0 })
                        static Integer g(List<Integer> xs) { xs?.size() }
                    }''')],
    ]
}
