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

/** 'P23 completeness' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G177_p23_completeness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A DFS closure invariant: closed ⇒ every successor is covered; marking a node breaks closure at the boundary.'

    static final List<Map> CASES = [

        // ---------- Phase 23: completeness — closure ⇒ reachable-covered, and the stack obstacle ----------
        // "visited is closed under next" — (0..<n).every { it∈visited ⟹ next[it]∈visited } — is the
        // completeness invariant. (b) closure ⇒ reachable-covered is provable; (a) DFS establishing closure
        // is the hard half (the stack). First, the one-step consequence: a closed set covers each successor.
        [group: 'P23 completeness', name: 'closure ⇒ successor covered (one step)', ok: true,
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n && (u in visited) &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        @Ensures({ next[u] in visited })
                        int f(int u) { 0 }
                    }''')],
        // (a) the obstacle, pinned cleanly via checkPath: simply MARKING a node breaks closure — the added
        // node's successor need not be visited yet. So closure is not preserved by a mark, which is exactly
        // why mark-then-recurse DFS cannot carry it as an invariant and completeness needs the frontier/stack
        // invariant (closure holds for everything *except nodes on the stack*). Refutes with a concrete u.
        [group: 'P23 completeness', name: 'marking a node breaks closure (boundary)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        @Modifies({ this.visited })
                        @Ensures({ (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        void mark(int u) { visited.add(u) }
                    }''')],
    ]
}
