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

/** 'P311 replaying to an obligation' — the state an obligation inside a loop body (or after a call-site prefix) is
 *  checked in. Shared import header and wrappers come from {@link CaseDsl}. */
class G356_p311_replay_to_obligation {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'An obligation is checked in the state at its own point: branch and short-circuit conditions are assumed where they are evaluated, an early-exit `if` narrows the path it leaves, and a statement the replay cannot model havocs what it writes instead of leaving stale values.'

    static final List<Map> CASES = [
        // ---------- Phase 311: replaying to an obligation ----------
        // An obligation after an early-exit `if` used to be checked against values from BEFORE later writes: the
        // replay stopped at the `if` (it could not model the `return`) and the `i = i + 1` after it never applied.
        // f([1] as int[]) reads a[1].
        [group: 'P311 replaying to an obligation', name: 'index after an early exit and a bump refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ a != null })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] == 7) return 1
                                i = i + 1
                                int x = a[i]
                            }
                            return 0
                        }
                    }''')],
        // ...and with the read guarded it proves: the early exit narrows the path (a[i] != 7) and the bump applies.
        [group: 'P311 replaying to an obligation', name: 'guarded index after an early exit and a bump proves', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] == 7) return 1
                                i = i + 1
                                if (i < a.length) { int x = a[i] }
                            }
                            return 0
                        }
                    }''')],
        // A branch condition holds at the `if`, after the statements before it — not at the start of the iteration.
        // Assuming the OLD i > 0 "proved" the divisor non-zero; f(1) bumps i to 1 and divides by zero.
        [group: 'P311 replaying to an obligation', name: 'branch condition after a bump is assumed at the branch',
         expect: 'ArithmeticException',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int i = 0
                            int x = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                i = i + 1
                                if (i > 0) { x = 10.intdiv(i - 1) }
                            }
                            return x
                        }
                    }''')],
        [group: 'P311 replaying to an obligation', name: 'branch condition that excludes zero proves', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int i = 0
                            int x = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                i = i + 1
                                if (i > 1) { x = 10.intdiv(i - 1) }
                            }
                            return x
                        }
                    }''')],
        // The same for a short-circuit guard.
        [group: 'P311 replaying to an obligation', name: 'short-circuit guard after a bump is assumed at the expression',
         expect: 'ArithmeticException',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static boolean f(int n) {
                            int i = 0
                            boolean ok = false
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                i = i + 1
                                ok = i > 0 && 10.intdiv(i - 1) > 0
                            }
                            return ok
                        }
                    }''')],
        [group: 'P311 replaying to an obligation', name: 'short-circuit guard that excludes zero proves', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static boolean f(int n) {
                            int i = 0
                            boolean ok = false
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                i = i + 1
                                ok = i > 1 && 10.intdiv(i - 1) > 0
                            }
                            return ok
                        }
                    }''')],
        // A call-site precondition replays the straight-line prefix; `i++` was missing from the write set the
        // replay havocs, so g saw the stale i == 0. h() calls g(1).
        [group: 'P311 replaying to an obligation', name: 'postfix increment before a call is not stale',
         expect: 'Cannot prove precondition of g',
         src: tc('''class C {
                        @Requires({ z == 0 })
                        static int g(int z) { z }
                        static int h() { int i = 0; i++; return g(i) }
                    }''')],
    ]
}
