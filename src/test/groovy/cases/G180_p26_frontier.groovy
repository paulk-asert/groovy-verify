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

/** 'P26 frontier' — 1 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G180_p26_frontier {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A DFS establishes its closure via a frontier/stack invariant.'

    static final List<Map> CASES = [

        // ---------- Phase 26: the frontier/stack invariant — DFS establishes closure ----------
        // The (a) half of completeness. The recursion stack is a Set ghost `onStack`, pushed before the
        // recursive call and popped after. The invariant is closed-EXCEPT-ON-STACK: every visited node is on
        // the stack OR its successor is visited. `visit` maintains it AND restores the stack (net zero), so
        // when the stack is empty the invariant *is* full closure. Mark-then-recurse: u is covered by being
        // on the stack until the recursion into next[u] returns (covering next[u]), then u is popped.
        [group: 'P26 frontier', name: 'DFS establishes closure (frontier/stack invariant)', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        Set<Integer> onStack
                        int n
                        @Requires({ 0 <= u && u < n &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (it in onStack || next[it] in visited) } &&
                                    (0..<n).every { (it in onStack) ==> (it in visited) } })
                        @Modifies({ [this.visited, this.onStack] })
                        @Decreases({ n - Sets.boundedCount(visited, n) })
                        @Ensures({ (u in visited) &&
                                   (0..<n).every { (it in visited) ==> (it in onStack || next[it] in visited) } &&
                                   (0..<n).every { (it in onStack) ==> (it in visited) } &&
                                   (0..<n).every { (it in onStack) == (it in old.onStack) } &&
                                   (0..<n).every { (it in old.visited) ==> (it in visited) } })
                        void visit(int u) {
                            if (u !in visited && Sets.boundedCount(visited, n) < n) {
                                visited.add(u)
                                onStack.add(u)
                                visit(next[u])
                                onStack.remove(u)
                            }
                        }
                        // The payoff: from an empty visited set and empty stack, one DFS leaves `visited`
                        // CLOSED under next — every visited node's successor is visited. When the stack is
                        // empty the closed-except-on-stack invariant *is* full closure. This is DFS
                        // *establishing* closure — the (a) half, the last piece of DFS completeness.
                        @Requires({ 0 <= start && start < n &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { it !in visited } &&
                                    (0..<n).every { it !in onStack } })
                        @Modifies({ [this.visited, this.onStack] })
                        @Ensures({ (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        void dfs(int start) {
                            visit(start)
                        }
                    }''')],
    ]
}
