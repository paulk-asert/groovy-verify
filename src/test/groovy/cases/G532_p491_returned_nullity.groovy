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
 * 'P491 nullity returned' — a returned list ({@code return out}) gave {@code result} the list's values and size (Phase
 * 41) but fresh null flags, so {@code @Ensures({ result.every { it != null } })} failed after {@code out.add(n)} with an
 * {@code int n}. It has the list's flags now. (The same phase reads a rewrite's variable by its own declared type, so an
 * {@code async} arm's {@code int i} renamed {@code i$a1} and sent on a channel isn't null; a queue is built in a loop,
 * whose summary forgets its flags, so that shows only once comparisons read null.)
 */
class G532_p491_returned_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 491: a returned list keeps its elements' nullity — `return out` after `out.add(n)` with an `int n` has none null, so `@Ensures({ result.every { it != null } })` proves."

    static final List<Map> CASES = [

        // ---------- a returned list ----------
        [group: "P491 nullity returned", name: "a returned list's", ok: true,
         src: tc('''class A {
                        @Ensures({ result.size() == 2 && result.every { it != null } })
                        static List<Integer> f(int n) { List<Integer> out = []; out.add(n); out.add(n + 1); return out }
                    }''')],
        [group: "P491 nullity returned", name: "… of a boxed value", expect: ['Cannot prove postcondition', 'fails on: f(null)'],
         src: tc('''class A {
                        @Ensures({ result.every { it != null } })
                        static List<Integer> f(Integer n) { List<Integer> out = []; out.add(n); return out }
                    }''')],

        [group: "P491 nullity returned", name: "a returned literal's", ok: true,
         src: tc('''class A {
                        @Ensures({ result.every { it != null } })
                        static List<Integer> f(int n) { [n, n + 1] }
                    }''')],
        [group: "P491 nullity returned", name: "a returned drop's", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { it != null } })
                        @Ensures({ result.every { it != null } })
                        static List<Integer> f(List<Integer> xs) { xs.drop(1) }
                    }''')],
        [group: "P491 nullity returned", name: "a returned shift's", ok: true,
         src: tc('''class A {
                        @Ensures({ result.every { it != null } })
                        static List<Integer> f(int n) { List<Integer> out = []; out << n << n; return out }
                    }''')],
    ]
}
