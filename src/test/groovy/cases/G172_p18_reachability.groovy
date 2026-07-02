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

/** 'P18 reachability' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G172_p18_reachability {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A DFS\'s visited set grows monotonically and covers the target node (fuel- and cardinality-bounded).'

    static final List<Map> CASES = [

        // ---------- Phase 18: reachability — a recursive graph traversal over a Set<Node> ----------
        // A DFS on a functional graph (`next` is a Map<Node,Node> successor) marking nodes in a Set.
        // Fuel-bounded so termination is a plain int measure; the reachability postcondition proves BOTH
        // halves the fragment can soundly express: (1) SOUNDNESS — visited only grows (every previously
        // visited node stays visited), a bounded universal over the node domain; (2) PROGRESS — the node
        // handed in ends visited (while fuel remained). Composes sets, maps, induction, caller-side set
        // framing (the recursive call havocs `visited` and reframes it from the callee's @Ensures), and
        // bounded quantifiers — no new machinery.
        [group: 'P18 reachability', name: 'fuel DFS: visited grows AND node covered', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next   // functional graph: successor of node u
                        Set<Integer> visited
                        int n   // node domain 0..<n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ fuel })
                        @Ensures({ (0..<n).every { (it in old.visited) ==> (it in visited) } &&
                                   (fuel <= 0 || (u in visited)) })   // grows monotonically, and u gets covered
                        void visit(int u, int fuel) {
                            if (fuel > 0 && u !in visited) {
                                visited.add(u)
                                visit(next[u], fuel - 1)
                            }
                        }
                    }''')],
        // Soundness anchor: claiming the node is visited UNCONDITIONALLY (dropping the `fuel <= 0 ||`
        // guard) is false — when fuel runs out the base case adds nothing — so it refutes. This is the
        // honest boundary: progress is conditional on the termination budget.
        [group: 'P18 reachability', name: 'unconditional coverage refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ fuel })
                        @Ensures({ u in visited })
                        void visit(int u, int fuel) {
                            if (fuel > 0 && u !in visited) {
                                visited.add(u)
                                visit(next[u], fuel - 1)
                            }
                        }
                    }''')],
        // The same SOUNDNESS half under the set-cardinality termination measure (`n - visited.size()`):
        // the visited-only-grows reachability postcondition, proved with the DFS-shaped cardinality
        // @Decreases rather than a fuel counter (the size guard supplies the measure's lower bound).
        [group: 'P18 reachability', name: 'cardinality DFS: visited only grows', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ n - visited.size() })
                        @Ensures({ (0..<n).every { (it in old.visited) ==> (it in visited) } })
                        void visit(int u) {
                            if (u !in visited && visited.size() < n) {
                                visited.add(u)
                                visit(next[u])
                            }
                        }
                    }''')],
        // Soundness: a traversal that REMOVES a node breaks monotonic growth → refuted.
        [group: 'P18 reachability', name: 'removal breaks monotonic growth', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (0..<n).every { 0 <= next[it] && next[it] < n } })
                        @Modifies({ this.visited })
                        @Decreases({ fuel })
                        @Ensures({ (0..<n).every { (it in old.visited) ==> (it in visited) } })
                        void visit(int u, int fuel) {
                            if (fuel > 0 && (u in visited)) {
                                visited.remove(u)
                                visit(next[u], fuel - 1)
                            }
                        }
                    }''')],
    ]
}
