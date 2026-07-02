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

/** 'P49 prefix-exits' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G091_p49_prefix_exits {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Early returns in a loop\'s prefix region (before the loop) are verified per path; a postcondition violation on an exit refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 49 (Slice A): early-return in loop prefix ----------
        // The headline shape: an early-return guard before the loop. The prefix exit's
        // @Ensures verifies on its own path (assumes the guard); the loop's establishment /
        // use checks fire on the no-exit path (assumes ¬guard).
        [group: 'P49 prefix-exits', name: 'single prefix early-return verifies', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            if (n == 0) return 7
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],
        // Stacked early-returns: each is verified independently with prior guards negated.
        [group: 'P49 prefix-exits', name: 'multiple stacked prefix early-returns', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            if (n == 0) return 1
                            if (n == 1) return 2
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],
        // Soundness: an early-return whose value violates the postcondition refutes.
        [group: 'P49 prefix-exits', name: 'early-return postcondition violation refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            if (n == 0) return -1
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],
        // Loop establishment USES the negated guard: the invariant after the prefix needs to
        // hold on the "no early-exit" path. Here the invariant assumes n >= 1, which only
        // holds when the early-exit didn't fire (n != 0).
        [group: 'P49 prefix-exits', name: 'loop invariant uses ¬prefix-guard', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 1 })
                        static int f(int n) {
                            if (n == 0) return 1
                            int i = 1
                            @Invariant({ 1 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],
        // Prior statements + early-return: the prior assignment runs, then the exit's @Ensures
        // is verified with that state.
        [group: 'P49 prefix-exits', name: 'prior assignment + early-return', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int x = n + 1
                            if (x == 1) return 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { i = i + 1 }
                            return i
                        }
                    }''')],
    ]
}
