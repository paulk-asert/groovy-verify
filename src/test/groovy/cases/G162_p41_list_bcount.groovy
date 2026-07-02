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

/** 'P41 list bcount' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G162_p41_list_bcount {

    static final List<Map> CASES = [

        // ---------- Phase 41: bounded count tracking for lists ----------
        // Append of a matching element raises xs.count(v) by exactly one — the bounded-count
        // analogue of the per-store count law, asserted on the boundary slot oldSize.
        [group: 'P41 list bcount', name: 'xs.add(v) raises xs.count(v) by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) + 1 })
                        void push(int v) { xs.add(v) }
                    }''')],
        // Append of a non-matching element preserves the count.
        [group: 'P41 list bcount', name: 'xs.add(v) leaves xs.count(w) unchanged when v != w', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && v != w })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(w) == old.xs.count(w) })
                        void push(int v, int w) { xs.add(v) }
                    }''')],
        // Soundness: claiming the wrong delta refutes — the bcount law is precise.
        [group: 'P41 list bcount', name: 'xs.add(v) wrong delta refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) + 2 })
                        void push(int v) { xs.add(v) }
                    }''')],
        // removeLast undoes the matching element's contribution.
        [group: 'P41 list bcount', name: 'removeLast of a matching tail decreases count by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 && xs[xs.size() - 1] == v })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) - 1 })
                        void popOne(int v) { xs.removeLast() }
                    }''')],
        // Push-then-pop round-trips count — the headline win from Phase 41 (today it would
        // refute because the unbounded count grows by 1 on the push and doesn't shrink back).
        [group: 'P41 list bcount', name: 'push-then-pop preserves count', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) })
                        void roundTrip(int v) { xs.add(v); xs.removeLast() }
                    }''')],
        // clear zeros every tracked count (the bcount-over-empty-range axiom asserted at clear time).
        [group: 'P41 list bcount', name: 'clear drops xs.count(v) to 0', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == 0 })
                        void reset(int v) { xs.clear() }
                    }''')],
        // Regression check: existing per-store count law on int[] arrays continues to use the
        // unbounded count (the permutation sort proofs rely on this). No change in behaviour.
        [group: 'P41 list bcount', name: 'int[] count law unchanged (regression anchor)', ok: true,
         src: tc('''class C {
                        int[] a
                        @Requires({ 0 <= k && k < a.length })
                        @Modifies({ this.a })
                        @Ensures({ a.count(v) == old.a.count(v) - (old.a[k] == v ? 1 : 0) + (newV == v ? 1 : 0) })
                        void put(int k, int newV, int v) { a[k] = newV }
                    }''')],
    ]
}
