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

/** 'P42 mutation replay' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G163_p42_mutation_replay {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'After xs.add, an in-bounds read (xs[size-1]) passes the implicit bounds check.'

    static final List<Map> CASES = [

        // ---------- Phase 42: LemmaCall replay in implicit-obligation pass ----------
        // After xs.add(v), the implicit bounds check on xs[0] sees the new size — pre-Phase-42
        // the implicit pass didn't replay LemmaCalls so it would over-refute. The body-replay
        // and implicit-obligation passes now agree.
        [group: 'P42 mutation replay', name: 'add then in-bounds read passes implicit bounds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int firstAfterPush(List<Integer> xs, int v) {
                            xs.add(v)
                            xs[0]
                        }
                    }''')],
        // Same pattern but with xs.size() as the index — exercises the size oracle threading
        // through the implicit pass.
        [group: 'P42 mutation replay', name: 'add then xs[size-1] read passes bounds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int lastAfterPush(List<Integer> xs, int v) {
                            xs.add(v)
                            xs[xs.size() - 1]
                        }
                    }''')],
        // Two adds chain through the implicit pass too: after add(a); add(b), xs[1] is in bounds.
        [group: 'P42 mutation replay', name: 'two adds then xs[1] read passes bounds', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int secondAfterPushTwo(List<Integer> xs, int a, int b) {
                            xs.add(a)
                            xs.add(b)
                            xs[1]
                        }
                    }''')],
        // Source-order preserved: a mutation BEFORE a guarded branch lets the branch's implicit
        // obligations see the post-mutation state.
        [group: 'P42 mutation replay', name: 'add then guarded read inside branch', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int guardedAfterPush(List<Integer> xs, int v) {
                            xs.add(v)
                            if (xs.size() > 0) return xs[0]
                            return -1
                        }
                    }''')],
        // Soundness anchor: after removeLast, xs[oldSize-1] is out of bounds — the implicit pass
        // must see the size shrunk. Pre-Phase-42 it would have passed (size oracle unchanged from
        // the implicit-pass POV); post-Phase-42 it correctly refutes.
        [group: 'P42 mutation replay', name: 'removeLast then read at old-last refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int popThenRead(List<Integer> xs) {
                            int n = xs.size()
                            xs.removeLast()
                            xs[n - 1]
                        }
                    }''')],
        // Mutation effect on a downstream containsKey check.
        [group: 'P42 mutation replay', name: 'm.put then containsKey passes implicit check', ok: true,
         src: tc('''class C {
                        @Requires({ m != null })
                        @Ensures({ result == 1 })
                        static int putThenCheck(Map<String, Integer> m) {
                            m.put("k", 42)
                            m.containsKey("k") ? 1 : 0
                        }
                    }''')],
    ]
}
