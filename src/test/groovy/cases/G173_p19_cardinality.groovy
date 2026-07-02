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

/** 'P19 cardinality' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G173_p19_cardinality {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Set cardinality: a full bounded set covers its domain; coverage needs the bound; size <= n.'

    static final List<Map> CASES = [

        // ---------- Phase 19: the cardinality axiom — pigeonhole over a bounded domain ----------
        // Sets.boundedBy(s, n) ≜ s ⊆ [0,n): |s| <= n, and full iff it covers the domain. This is the
        // bridge the uninterpreted cardinality (Phase 16) lacked — relating |s| to actual membership.
        // FULL ⟹ MEMBER: a bounded set of size n contains every node of the domain (pigeonhole).
        [group: 'P19 cardinality', name: 'full bounded set covers the domain', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, n) && s.size() == n && 0 <= u && u < n })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
        // Soundness: without Sets.boundedBy there is no link from size to membership → cannot conclude u in s.
        [group: 'P19 cardinality', name: 'coverage needs the bound (refuted)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s.size() == n && 0 <= u && u < n })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
        // The size bound itself: a domain-bounded set has at most n elements.
        [group: 'P19 cardinality', name: 'bounded set size is at most n', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, n) })
                        @Ensures({ s.size() <= n })
                        static int f(Set<Integer> s, int n) { 0 }
                    }''')],
        // HOLE ⟹ NOT FULL: a bounded set missing a domain element has size < n — exactly the fact a
        // cardinality-terminating DFS needs at its coverage branch (an unvisited in-domain node ⟹ room remains).
        [group: 'P19 cardinality', name: 'a hole means the set is not full', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedBy(s, n) && 0 <= u && u < n && u !in s })
                        @Ensures({ s.size() < n })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
        // Soundness: without the bound, a missing element says nothing about the (uninterpreted) size.
        [group: 'P19 cardinality', name: 'hole needs the bound (refuted)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ 0 <= u && u < n && u !in s })
                        @Ensures({ s.size() < n })
                        static int f(Set<Integer> s, int n, int u) { 0 }
                    }''')],
    ]
}
