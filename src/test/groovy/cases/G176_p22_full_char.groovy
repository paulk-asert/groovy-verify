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

/** 'P22 full-char' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G176_p22_full_char {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'count==k iff every domain node is in the set (the cardinality characterisation of full coverage).'

    static final List<Map> CASES = [

        // ---------- Phase 22: the full-characterization axiom + end-to-end DFS coverage ----------
        // Sets.boundedCount(s,k) == k  ⟺  s covers [0,k). COUNT FULL ⇒ COVERS: a count of k over a k-slot domain
        // forces every node in — the converse of Phase 20's full ⇒ count, and the fact DFS needs.
        [group: 'P22 full-char', name: 'count == k ⇒ every domain node is in', ok: true,
         src: tc('''class C {
                        @Requires({ Sets.boundedCount(s, k) == k && 0 <= u && u < k })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int k, int u) { 0 }
                    }''')],
        // COVERS ⇒ COUNT FULL: the other direction also holds from the primitive's axiom.
        [group: 'P22 full-char', name: 'covers domain ⇒ count == k', ok: true,
         src: tc('''class C {
                        @Requires({ k >= 0 && (0..<k).every { it in s } })
                        @Ensures({ Sets.boundedCount(s, k) == k })
                        static int f(Set<Integer> s, int k) { 0 }
                    }''')],
        // Soundness: full count says nothing about a node OUTSIDE the domain [0,k).
        [group: 'P22 full-char', name: 'coverage is only within the domain (refuted)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ Sets.boundedCount(s, k) == k && u >= k })
                        @Ensures({ u in s })
                        static int f(Set<Integer> s, int k, int u) { 0 }
                    }''')],
        // THE CAPSTONE: a cardinality-terminating DFS proves UNCONDITIONAL coverage — the node handed in
        // ends visited, with no fuel bound. Termination is `n - Sets.boundedCount(visited, n)` (the per-add law
        // makes it strictly decrease on a fresh add); coverage closes because at the "set full" branch the
        // full-characterization forces the node in. Composes sets, maps, induction, set framing, bounded
        // quantifiers, the per-add law and the full-characterization into the DFS soundness property.
        [group: 'P22 full-char', name: 'DFS: unconditional coverage (start in visited)', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next   // functional graph
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ n - Sets.boundedCount(visited, n) })   // strictly decreases — the per-add law
                        @Ensures({ (u in visited) &&
                                   (0..<n).every { (it in old.visited) ==> (it in visited) } })   // ← UNCONDITIONAL coverage
                        void visit(int u) {
                            if (u !in visited && Sets.boundedCount(visited, n) < n) {
                                visited.add(u)
                                visit(next[u])
                            }
                        }
                    }''')],
        // The honest boundary, made concrete: we prove the node itself is covered, NOT its successors —
        // claiming `next[u] in visited` refutes (a node visited earlier needn't have had its edge followed;
        // that is the closure/completeness gap, which needs the frontier/stack invariant).
        [group: 'P22 full-char', name: 'DFS: successor-covered is NOT proved (boundary)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ n - Sets.boundedCount(visited, n) })
                        @Ensures({ next[u] in visited })
                        void visit(int u) {
                            if (u !in visited && Sets.boundedCount(visited, n) < n) {
                                visited.add(u)
                                visit(next[u])
                            }
                        }
                    }''')],
    ]
}
