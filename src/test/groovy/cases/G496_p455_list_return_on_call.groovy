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
 * 'P455 a list return built on a call' — a list-valued call bound to a local (`List<Integer> r = f(n - 1)`, Phase 225)
 * or returned bare carried its @Ensures, but one inside the return expression (`f(n - 1) + [n]`, `[n, *f(n - 1)]`) had
 * no list value: the postcondition was skipped. Each such call becomes a list local now, and the return is bound as
 * the concatenation (Phase 323's model) — for a recursive call under its @Decreases, or any other contracted one.
 */
class G496_p455_list_return_on_call {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 455: a list return built on a list-valued call (`return f(n - 1) + [n]`, `return [n, *f(n - 1)]`, `g(n) + [n]`) carries the call's @Ensures, as one bound to a local already did, where the postcondition was skipped."

    static final List<Map> CASES = [

        // Each was a skip: return expression '…' is outside fragment
        [group: "P455 a list return built on a call", name: "a recursive call appended to proves its size", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() == n })
                        @Decreases({ n })
                        static List<Integer> f(int n) {
                            if (n == 0) return []
                            return f(n - 1) + [n]
                        }
                    }''')],

        [group: "P455 a list return built on a call", name: "… one spread into a literal", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() == n })
                        @Decreases({ n })
                        static List<Integer> f(int n) {
                            if (n == 0) return []
                            return [n, *f(n - 1)]
                        }
                    }''')],

        [group: "P455 a list return built on a call", name: "… the element it adds", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 1 })
                        @Ensures({ result != null && result.size() == n && result[0] == n })
                        @Decreases({ n })
                        static List<Integer> f(int n) {
                            if (n == 1) return [1]
                            return [n, *f(n - 1)]
                        }
                    }''')],

        [group: "P455 a list return built on a call", name: "… another method's call", ok: true,
         src: tc('''class A {
                        @Ensures({ result != null && result.size() == 3 && result[2] == n })
                        static List<Integer> f(int n) { g(n) + [n] }
                        @Ensures({ result != null && result.size() == 2 })
                        static List<Integer> g(int n) { [n, n] }
                    }''')],

        [group: "P455 a list return built on a call", name: "a size claim it doesn't give is refuted",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && (n == 0 || result.size() == n + 1) })
                        @Decreases({ n })
                        static List<Integer> f(int n) {
                            if (n == 0) return []
                            return f(n - 1) + [n]
                        }
                    }''')],

        [group: "P455 a list return built on a call", name: "… an element claim",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ n >= 1 })
                        @Ensures({ result != null && result.size() == n && result[0] == 1 })
                        @Decreases({ n })
                        static List<Integer> f(int n) {
                            if (n == 1) return [1]
                            return [n, *f(n - 1)]
                        }
                    }''')],

        [group: "P455 a list return built on a call", name: "the measure is checked at it",
         expect: "Cannot prove recursion measure decreases and stays >= 0 at this recursive call in f",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null })
                        @Decreases({ n })
                        static List<Integer> f(int n) {
                            if (n == 0) return []
                            return f(n) + [n]
                        }
                    }''')],

        [group: "P455 a list return built on a call", name: "without a measure the skip asks for one",
         expect: "a recursive call's @Ensures is assumed only when a @Decreases measure shows the recursion ends",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.size() == n })
                        static List<Integer> f(int n) {
                            if (n == 0) return []
                            return f(n - 1) + [n]
                        }
                    }''')],
    ]
}
