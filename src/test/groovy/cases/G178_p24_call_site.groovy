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

/** 'P24 call-site' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G178_p24_call_site {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A callee\'s precondition is discharged at the call site against the post-mutation state.'

    static final List<Map> CASES = [
        // Phase 24 (call-site soundness): a recursive closure-threading DFS now REFUTES at the recursive
        // call. After `visited.add(u)`, the callee's closure precondition is checked against the post-add
        // set (closure broken at u), not the entry set. Before the fix this passed *spuriously* (the
        // intervening mutation wasn't threaded, and the formal/caller `u` were conflated).
        [group: 'P24 call-site', name: 'closure precondition is checked post-mutation', expect: 'Cannot prove precondition',
         src: tc('''class C {
                        Map<Integer,Integer> next
                        Set<Integer> visited
                        int n
                        @Requires({ 0 <= u && u < n &&
                                    (0..<n).every { 0 <= next[it] && next[it] < n } &&
                                    (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        @Modifies({ this.visited })
                        @Decreases({ n - Sets.boundedCount(visited, n) })
                        @Ensures({ (0..<n).every { (it in visited) ==> (next[it] in visited) } })
                        void visit(int u) {
                            if (u !in visited && Sets.boundedCount(visited, n) < n) {
                                visited.add(u)
                                visit(next[u])
                            }
                        }
                    }''')],
        // A straight-line mutation before a call is threaded: needs(s, k) requires `k in s`, and
        // `s.add(k)` right before the call establishes it — verified only because the add is now replayed.
        [group: 'P24 call-site', name: 'mutation before call establishes precondition', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ k in s })
                        void needs(int k) { }
                        @Modifies({ this.s })
                        void go(int k) { s.add(k); needs(k) }
                    }''')],
        // Soundness: without the add, the precondition isn't established → refuted (the threading is precise,
        // not vacuous).
        [group: 'P24 call-site', name: 'no mutation, precondition unmet', expect: 'Cannot prove precondition',
         src: tc('''class C { Set<Integer> s
                        @Requires({ k in s })
                        void needs(int k) { }
                        void go(int k) { needs(k) }
                    }''')],
        // Early-return narrowing: `if (k <= 0) return` before the call supplies `k > 0`, so callee's
        // @Requires({ k > 0 }) holds — a fact PathFacts (enclosing-if only) could not provide.
        [group: 'P24 call-site', name: 'early-return narrows the path', ok: true,
         src: tc('''class C {
                        @Requires({ k > 0 })
                        static int pos(int k) { k }
                        static int f(int k) {
                            if (k <= 0) return 0
                            return pos(k)
                        }
                    }''')],
    ]
}
