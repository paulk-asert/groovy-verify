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
 * 'P456 a ternary of lists returned' — a list has no `ite` value, so a list return of a ternary
 * (`n == 0 ? [] : f(n - 1) + [n]`) bound as nothing and the postcondition was skipped, where the `if (n == 0) return []`
 * form proved. It's checked as the two returns it chooses between now, each under its test. And a list-valued call in a
 * scalar-looking return (`f(n - 1) + n`, an append) was hoisted as an Int: integer addition, and a true size claim
 * refuted. It's left untranslated, a loud skip, as an append on a named list is (Phase 323).
 */
class G497_p456_ternary_list_return {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 456: a list return of a ternary (`n == 0 ? [] : f(n - 1) + [n]`, `n > 0 ? [n, n] : [0]`) is checked as the two returns it chooses between, where its postcondition was skipped; and an append onto a list-valued call (`f(n - 1) + n`) is a loud skip, where it was integer addition and a true size claim was refuted."

    static final List<Map> CASES = [

        // Each was a skip: return expression '… ? … : …' is outside fragment
        [group: "P456 a ternary of lists returned", name: "a recursive ternary of lists proves its size", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() == n })
                        @Decreases({ n })
                        static List<Integer> f(int n) { n == 0 ? [] : f(n - 1) + [n] }
                    }''')],

        [group: "P456 a ternary of lists returned", name: "… a literal in each arm", ok: true,
         src: tc('''class A {
                        @Ensures({ result != null && result.size() == (n > 0 ? 2 : 1) })
                        static List<Integer> f(int n) { n > 0 ? [n, n] : [0] }
                    }''')],

        [group: "P456 a ternary of lists returned", name: "… nested ternaries", ok: true,
         src: tc('''class A {
                        @Ensures({ result != null && result.size() >= 1 })
                        static List<Integer> f(int n) { n > 0 ? [n] : (n < 0 ? [n, n] : [0]) }
                    }''')],

        [group: "P456 a ternary of lists returned", name: "… a parameter's list in an arm", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result != null && result.size() >= xs.size() })
                        static List<Integer> f(List<Integer> xs, int n) { n > 0 ? xs + [n] : xs }
                    }''')],

        [group: "P456 a ternary of lists returned", name: "an arm that breaks the claim is refuted",
         expect: "fails on: f(0)",
         src: tc('''class A {
                        @Ensures({ result != null && result.size() == 2 })
                        static List<Integer> f(int n) { n > 0 ? [n, n] : [0] }
                    }''')],

        [group: "P456 a ternary of lists returned", name: "… a recursive one",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && (n == 0 || result.size() == n + 1) })
                        @Decreases({ n })
                        static List<Integer> f(int n) { n == 0 ? [] : f(n - 1) + [n] }
                    }''')],

        [group: "P456 a ternary of lists returned", name: "without a measure the skip asks for one",
         expect: "a recursive call's @Ensures is assumed only when a @Decreases measure shows the recursion ends",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() == n })
                        static List<Integer> f(int n) { n == 0 ? [] : f(n - 1) + [n] }
                    }''')],

        // A false alarm before: the call hoisted as an Int, the list operator integer arithmetic, `result.size() = 0`
        // (written as an append, `+ n`, which Phase 457 models, then a removal, `- n`, which 458 does; a repetition,
        // `* 2`, isn't modelled, so it still skips)
        [group: "P456 a ternary of lists returned", name: "a list operator on a recursive call skips, not refuted",
         expect: "return expression '(A.f((n - 1)) * 2)' is outside fragment",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() <= n })
                        @Decreases({ n })
                        static List<Integer> f(int n) {
                            if (n == 0) return []
                            return f(n - 1) * 2
                        }
                    }''')],

        [group: "P456 a ternary of lists returned", name: "… on another method's",
         expect: "return expression '(A.g(n) * 2)' is outside fragment",
         src: tc('''class A {
                        @Ensures({ result != null && result.size() == 4 })
                        static List<Integer> f(int n) { g(n) * 2 }
                        @Ensures({ result != null && result.size() == 2 })
                        static List<Integer> g(int n) { [n, n] }
                    }''')],
    ]
}
