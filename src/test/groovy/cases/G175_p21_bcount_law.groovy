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

/** 'P21 bcount law' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G175_p21_bcount_law {

    static final List<Map> CASES = [

        // ---------- Phase 21: the bcount per-add law (Sets.boundedCount as a primitive) ----------
        // Sets.boundedCount(s, k) is the bounded count as a primitive, carrying its bound axiom and a per-mutation
        // law. Adding a FRESH, in-domain element raises the count by exactly one — the bcount analogue of
        // the per-store `count` law, now threading the count across a set mutation.
        [group: 'P21 bcount law', name: 'fresh in-domain add increments count', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ 0 <= u && u < k && u !in s })
                        @Modifies({ this.s })
                        @Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) + 1 })
                        void put(int u, int k) { s.add(u) }
                    }''')],
        // Soundness: drop the freshness guard and the count need not grow (u may already be present).
        [group: 'P21 bcount law', name: 'non-fresh add refutes +1', expect: 'Cannot prove postcondition',
         src: tc('''class C { Set<Integer> s
                        @Requires({ 0 <= u && u < k })
                        @Modifies({ this.s })
                        @Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) + 1 })
                        void put(int u, int k) { s.add(u) }
                    }''')],
        // The domain guard matters: adding an element OUTSIDE [0,k) leaves the bounded count unchanged.
        [group: 'P21 bcount law', name: 'out-of-domain add keeps count', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ u >= k })
                        @Modifies({ this.s })
                        @Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) })
                        void put(int u, int k) { s.add(u) }
                    }''')],
        // Remove of a present, in-domain element drops the bounded count by one.
        [group: 'P21 bcount law', name: 'in-domain remove decrements count', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ 0 <= u && u < k && (u in s) })
                        @Modifies({ this.s })
                        @Ensures({ Sets.boundedCount(s, k) == Sets.boundedCount(old.s, k) - 1 })
                        void drop(int u, int k) { s.remove(u) }
                    }''')],
        // The bound axiom rides the primitive: a domain-bounded count never exceeds its bound.
        [group: 'P21 bcount law', name: 'primitive count carries its bound', ok: true,
         src: tc('''class C {
                        @Requires({ k >= 0 })
                        @Ensures({ 0 <= Sets.boundedCount(s, k) && Sets.boundedCount(s, k) <= k })
                        static int f(Set<Integer> s, int k) { 0 }
                    }''')],
    ]
}
