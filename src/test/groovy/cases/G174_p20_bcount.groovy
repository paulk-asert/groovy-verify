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

/** 'P20 bcount' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G174_p20_bcount {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The bounded-count law 0 <= bcount(s,k) <= k; a full domain gives bcount==k, over-counting breaks the bound.'

    static final List<Map> CASES = [

        // ---------- Phase 20: bcount — the bounded-sum cardinality, properties earned by induction ----------
        // bcount(s, k) = Σ_{i<k} (i ∈ s ? 1 : 0): the genuine count of s's members in [0, k), written as
        // an ordinary recursive method. Its defining BOUND — 0 <= bcount(s,k) <= k — is the converse
        // counting the uninterpreted `card` lacked, and the framework proves it by its OWN induction
        // (@Decreases on k, self-@Ensures as the inductive hypothesis) — no built-in axiom.
        [group: 'P20 bcount', name: 'bound lemma: 0 <= bcount(s,k) <= k', ok: true,
         src: tc('''class C {
                        @Requires({ k >= 0 })
                        @Ensures({ 0 <= result && result <= k })   // the BOUND — the converse counting `card` lacked
                        @Decreases({ k })
                        static int bcount(Set<Integer> s, int k) {
                            if (k == 0) return 0
                            int rest = bcount(s, k - 1)
                            return rest + ((k - 1) in s ? 1 : 0)
                        }
                    }''')],
        // FULL ⇒ COUNT = k: if every node of [0,k) is in s, the bounded count is exactly k. This ties the
        // count to actual membership (the direction `Sets.boundedBy`'s pigeonhole gives), proved by induction
        // — the recursion's @Requires `(0..<k-1).every{...}` follows from the caller's over [0,k).
        [group: 'P20 bcount', name: 'full domain ⇒ bcount(s,k) == k', ok: true,
         src: tc('''class C {
                        @Requires({ k >= 0 && (0..<k).every { it in s } })
                        @Ensures({ result == k })
                        @Decreases({ k })
                        static int bcount(Set<Integer> s, int k) {
                            if (k == 0) return 0
                            int rest = bcount(s, k - 1)
                            return rest + ((k - 1) in s ? 1 : 0)
                        }
                    }''')],
        // Soundness: the bound is earned, not assumed — a body that over-counts (rest + 2) breaks `<= k`.
        [group: 'P20 bcount', name: 'over-counting breaks the bound', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ k >= 0 })
                        @Ensures({ 0 <= result && result <= k })
                        @Decreases({ k })
                        static int bcount(Set<Integer> s, int k) {
                            if (k == 0) return 0
                            int rest = bcount(s, k - 1)
                            return rest + 2
                        }
                    }''')],
    ]
}
