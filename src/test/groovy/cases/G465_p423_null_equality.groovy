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
 * 'P423 null equality' — Phase 422 left a safe call's null case unconstrained for a boolean (and a string or decimal),
 * so `==` on it read the value alone: `@Ensures({ result == true })` of `xs?.isEmpty()` refuted with no call shown,
 * `xs?.isEmpty() == false` couldn't prove false on a null `xs`, and `xs?.isEmpty() == null` was outside the fragment.
 *
 * Measured on Groovy 6, dynamic and @CompileStatic: only a null equals a null — `null == false` and `null == true` are
 * false, `null != true` true, `null == null` true. So `==` and `!=` read the nullities first, for a safe call and for a
 * name one was assigned to (the result, a local); an integer's null case is a sentinel no number equals already.
 */
class G465_p423_null_equality {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 423: `==`/`!=` on a safe call's value (or a name it was assigned to) read Groovy's rule that only a null equals a null: `xs?.isEmpty() == false` is false on a null `xs`, `!= true` true, `== null` its nullity."

    static final List<Map> CASES = [

        [group: "P423 null equality", name: "a null equals neither true nor false",
         ok: true,
         src: tc('''class A {
                        @Ensures({ xs != null || result == false })
                        static boolean f(List<Integer> xs) { xs?.isEmpty() == false }
                        @Ensures({ xs != null || result == false })
                        static boolean g(List<Integer> xs) { xs?.isEmpty() == true }
                        @Ensures({ xs != null || result })
                        static boolean h(List<Integer> xs) { xs?.isEmpty() != true }
                    }''')],

        // It refuted with no call shown: the null case was any boolean
        [group: "P423 null equality", name: "a returned null fails `result == true` on its call",
         expect: ["Cannot prove postcondition of f", "ensured: (result == true)", "fails on: f(null)"],
         src: tc('''class A {
                        @Requires({ xs == null || xs.isEmpty() })
                        @Ensures({ result == true })
                        static Boolean f(List<Integer> xs) { xs?.isEmpty() }
                    }''')],

        [group: "P423 null equality", name: "… and proves when it can't be null",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.isEmpty() })
                        @Ensures({ result == true })
                        static Boolean f(List<Integer> xs) { xs?.isEmpty() }
                    }''')],

        // Outside the fragment before: the null couldn't be translated
        [group: "P423 null equality", name: "`== null` is the safe call's nullity",
         ok: true,
         src: tc('''class A {
                        @Ensures({ result == (xs == null) })
                        static boolean f(List<Integer> xs) { xs?.isEmpty() == null }
                        @Ensures({ result == (xs == null) })
                        static boolean g(List<Integer> xs) { xs?.size() == null }
                    }''')],

        [group: "P423 null equality", name: "a local assigned it keeps its null",
         ok: true,
         src: tc('''class A {
                        @Ensures({ xs != null || !result })
                        static boolean f(List<Integer> xs) { Boolean b = xs?.isEmpty(); return b == false }
                    }''')],

        [group: "P423 null equality", name: "two nulls are equal",
         ok: true,
         src: tc('''class A {
                        @Ensures({ !(xs == null && ys == null) || result })
                        static boolean f(List<Integer> xs, List<Integer> ys) { xs?.isEmpty() == ys?.isEmpty() }
                    }''')],

        [group: "P423 null equality", name: "… a null and a non-null aren't",
         expect: ["Cannot prove postcondition of f", "fails on: f(null, ["],
         src: tc('''class A {
                        @Ensures({ result })
                        static boolean f(List<Integer> xs, List<Integer> ys) { xs?.isEmpty() == ys?.isEmpty() }
                    }''')],
    ]
}
