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
 * 'P457 an element appended to a list' — `xs + n` with an int or Integer `n` appends it (`List.plus(Object)`), and
 * Phase 323's concatenation model refused it: a loud skip wherever it was written (`return f(n - 1) + n`, `xs + n`,
 * `List<Integer> ys = xs + n`). It's one element segment of the concatenation now, after the list it's added to.
 */
class G498_p457_list_element_append {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 457: an element appended to a list with `+` (`xs + n`, `f(n - 1) + n`, `xs + n + 1`) is modelled — one more element, at the end — where it was a loud skip."

    static final List<Map> CASES = [

        // Each was a skip: return expression '…' is outside fragment
        [group: "P457 an element appended to a list", name: "a recursion appending its element proves its size", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() == n })
                        @Decreases({ n })
                        static List<Integer> f(int n) {
                            if (n == 0) return []
                            return f(n - 1) + n
                        }
                    }''')],

        [group: "P457 an element appended to a list", name: "… and its last element", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 1 })
                        @Ensures({ result != null && result.size() == n && result[n - 1] == n })
                        @Decreases({ n })
                        static List<Integer> f(int n) { n == 1 ? [1] : f(n - 1) + n }
                    }''')],

        [group: "P457 an element appended to a list", name: "a parameter's list gains the element at its end", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result != null && result.size() == xs.size() + 1 && result[xs.size()] == n })
                        static List<Integer> f(List<Integer> xs, int n) { xs + n }
                    }''')],

        [group: "P457 an element appended to a list", name: "… two, chained into a local", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result == xs.size() + 2 })
                        static int f(List<Integer> xs, int n) {
                            List<Integer> ys = xs + n + 1
                            return ys.size()
                        }
                    }''')],

        [group: "P457 an element appended to a list", name: "… an Integer", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result != null && result.size() == xs.size() + 1 })
                        static List<Integer> f(List<Integer> xs, Integer n) { xs + n }
                    }''')],

        [group: "P457 an element appended to a list", name: "a size it doesn't have is refuted",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result != null && result.size() == xs.size() })
                        static List<Integer> f(List<Integer> xs, int n) { xs + n }
                    }''')],

        [group: "P457 an element appended to a list", name: "… an element it isn't",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ n >= 1 })
                        @Ensures({ result != null && result.size() == n && result[n - 1] == 1 })
                        @Decreases({ n })
                        static List<Integer> f(int n) { n == 1 ? [1] : f(n - 1) + n }
                    }''')],

        // Unchanged: an int's own `+` is arithmetic
        [group: "P457 an element appended to a list", name: "an int's + is still addition", ok: true,
         src: tc('''class A {
                        @Ensures({ result == n + 1 })
                        static int f(int n) { n + 1 }
                    }''')],
    ]
}
