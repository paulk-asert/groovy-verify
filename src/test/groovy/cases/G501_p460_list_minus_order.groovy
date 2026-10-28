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
 * 'P460 a removal keeps the rest, in order' — Phase 458 modelled `xs - n` and `xs - ys` by what the result can't hold
 * (anything removed, anything not from `xs`) and its size, but not what it must: every element of `xs` that isn't
 * removed is in the result, and in `xs`'s order. A claim that a kept element survives, that the head stays in front
 * or that a sorted list stays sorted couldn't be proved.
 */
class G501_p460_list_minus_order {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 460: a removal from a list (`xs - n`, `xs - ys`) keeps every other element, in order — a kept element is still contained, a kept head stays in front, a sorted list stays sorted — where only what was removed and the size were modelled."

    static final List<Map> CASES = [

        // ---------- every other element is kept ----------
        [group: "P460 a removal keeps the rest, in order", name: "an element not removed is still there", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.contains(m) && m != n })
                        @Ensures({ result.contains(m) })
                        static List<Integer> f(List<Integer> xs, int n, int m) { xs - n }
                    }''')],

        // Not modelled for a list removed: with it, a false claim about `xs - ys` (P458's "removing a list may empty it")
        // couldn't be refuted in any time. Undecided, not passed
        [group: "P460 a removal keeps the rest, in order", name: "an element not in a removed list isn't known kept", expect: 'Could not decide postcondition',
         src: tc('''class A {
                        @Requires({ xs != null && ys != null && xs.contains(m) && !ys.contains(m) })
                        @Ensures({ result.contains(m) })
                        static List<Integer> f(List<Integer> xs, List<Integer> ys, int m) { xs - ys }
                    }''')],

        [group: "P460 a removal keeps the rest, in order", name: "an element removed isn't kept for being there", expect: 'Cannot prove postcondition',
         src: tc('''class A {
                        @Requires({ xs != null && xs.contains(m) })
                        @Ensures({ result.contains(m) })
                        static List<Integer> f(List<Integer> xs, int n, int m) { xs - n }
                    }''')],

        // ---------- in order ----------
        [group: "P460 a removal keeps the rest, in order", name: "a head not removed stays in front", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != n })
                        @Ensures({ result.size() > 0 && result[0] == xs[0] })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],

        [group: "P460 a removal keeps the rest, in order", name: "a sorted list stays sorted", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.isSorted() })
                        @Ensures({ result.isSorted() })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],

        [group: "P460 a removal keeps the rest, in order", name: "… removing a list too", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && ys != null && xs.isSorted() })
                        @Ensures({ result.isSorted() })
                        static List<Integer> f(List<Integer> xs, List<Integer> ys) { xs - ys }
                    }''')],

        // the kept element moves up into the removed one's place
        [group: "P460 a removal keeps the rest, in order", name: "a kept element moves up", expect: 'Cannot prove postcondition',
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == n && xs[1] != n })
                        @Ensures({ result.size() == 1 && result[0] == xs[0] })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],

        [group: "P460 a removal keeps the rest, in order", name: "… to exactly the removed one's place", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] == n && xs[1] != n })
                        @Ensures({ result.size() == 1 && result[0] == xs[1] })
                        static List<Integer> f(List<Integer> xs, int n) { xs - n }
                    }''')],
    ]
}
