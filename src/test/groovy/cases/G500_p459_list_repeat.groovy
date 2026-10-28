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
 * 'P459 a list repeated' — `xs * k` (`List.multiply`) is `k` copies of `xs` in order, and nothing modelled it: a loud
 * skip wherever it was written. With `k` a literal from 0 to 16 it's the concatenation `xs + xs + … + xs`, Phase
 * 323's segments `k` times over. A symbolic `k` makes the size `xs.size() * k`, nonlinear, and stays a skip.
 */
class G500_p459_list_repeat {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 459: a list repeated with `*` a literal number of times (`xs * 2`, `[n] * 3`, `f(n - 1) * 2`, up to 16) is modelled as that many copies concatenated — exact size and elements — where it was a loud skip; a symbolic count stays a skip."

    static final List<Map> CASES = [

        [group: "P459 a list repeated", name: "a list doubled has twice the size", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result != null && result.size() == 2 * xs.size() })
                        static List<Integer> f(List<Integer> xs) { xs * 2 }
                    }''')],

        [group: "P459 a list repeated", name: "… its second copy repeats the first", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ (0..<xs.size()).every { int j -> result[j] == xs[j] && result[j + xs.size()] == xs[j] } })
                        static List<Integer> f(List<Integer> xs) { xs * 2 }
                    }''')],

        [group: "P459 a list repeated", name: "a literal repeated three times", ok: true,
         src: tc('''class A {
                        @Ensures({ result.size() == 3 && result.every { int t -> t == n } })
                        static List<Integer> f(int n) { [n] * 3 }
                    }''')],

        [group: "P459 a list repeated", name: "none of it is empty", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result.isEmpty() })
                        static List<Integer> f(List<Integer> xs) { xs * 0 }
                    }''')],

        [group: "P459 a list repeated", name: "a repetition joined to an element, into a local", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result == 2 * xs.size() + 1 })
                        static int f(List<Integer> xs, int n) {
                            List<Integer> ys = xs * 2 + n
                            return ys.size()
                        }
                    }''')],

        [group: "P459 a list repeated", name: "a recursion doubling its list", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() == 2 ** n })
                        @Decreases({ n })
                        static List<Integer> f(int n) { n == 0 ? [1] : f(n - 1) * 2 }
                    }''')],

        [group: "P459 a list repeated", name: "a repetition gives a callee a list it accepts", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() <= 5 })
                        static int f(List<Integer> xs) { g(xs * 2) }
                        @Requires({ ys != null && ys.size() <= 10 })
                        static int g(List<Integer> ys) { 0 }
                    }''')],

        [group: "P459 a list repeated", name: "doubling isn't adding one copy's worth less", expect: 'Cannot prove postcondition',
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result.size() < 2 * xs.size() })
                        static List<Integer> f(List<Integer> xs) { xs * 2 }
                    }''')],

        [group: "P459 a list repeated", name: "the copy starts over, not where it left off", expect: 'Cannot prove postcondition',
         src: tc('''class A {
                        @Requires({ a != b })
                        @Ensures({ result.size() == 4 && result[2] == b })
                        static List<Integer> f(int a, int b) { [a, b] * 2 }
                    }''')],

        // ---------- not modelled ----------
        [group: "P459 a list repeated", name: "a symbolic count is still a skip", expect: 'outside fragment',
         src: tc('''class A {
                        @Requires({ xs != null && k >= 0 })
                        @Ensures({ result.size() == xs.size() * k })
                        static List<Integer> f(List<Integer> xs, int k) { xs * k }
                    }''')],

        [group: "P459 a list repeated", name: "an int's * is still multiplication", ok: true,
         src: tc('''class A {
                        @Ensures({ result == 2 * a })
                        static int f(int a) { a * 2 }
                    }''')],
    ]
}
