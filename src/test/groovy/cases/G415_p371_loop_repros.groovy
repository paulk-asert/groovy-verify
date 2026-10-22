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

/**
 * 'P371 loop repros' — an obligation in a loop is checked at an arbitrary iteration (the invariant's, or for an
 * unannotated loop a summary's), so its model needn't be reachable: `fails on: f(0, 0)` for a body `n = 0` never
 * enters. A refutation's call is now sought along exact paths from entry, the first eight iterations of each loop on
 * the way, and withheld with a note when none gets there. And a soundness hole found doing it: an unannotated loop's
 * body was checked in the state BEFORE the loop, so a divisor or index the loop changes was proved from its first value.
 */
class G415_p371_loop_repros {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 371: a loop obligation\'s failing call is a run from entry (the first eight iterations of each loop on the way, earlier and nested loops unrolled too), else withheld with a note; and an unannotated loop\'s body is checked with what the loop writes havocked and its guard holding, not in the state before it.'

    static final List<Map> CASES = [

        // Before: compiled cleanly — the body was checked at i == 0, where the divisor is -3. f(4) throws.
        [group: "P371 loop repros", name: "an unannotated loop's body is checked at every iteration",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(4)"],
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            while (i < n) { s = 100.intdiv(i - 3); i++ }
                            s
                        }
                    }''')],

        // Before: compiled cleanly — a[0] is in bounds, a[1] isn't.
        [group: "P371 loop repros", name: "an index the loop moves",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f(new int[1])"],
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        static int f(int[] a) {
                            int s = 0
                            int i = 0
                            while (i < 10) { s = s + a[i]; i++ }
                            s
                        }
                    }''')],

        // Before: compiled cleanly — d is 1 before the loop, 0 on its second pass.
        [group: "P371 loop repros", name: "a divisor the loop writes",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(2)"],
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int d = 1
                            int i = 0
                            while (i < n) { s = 100.intdiv(d); d = d - 1; i++ }
                            s
                        }
                    }''')],

        // Before: compiled cleanly. A do-while's first pass runs before its guard.
        [group: "P371 loop repros", name: "a do-while's second pass",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(2)"],
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            do { s = 10.intdiv(i - 1); i++ } while (i < n)
                            s
                        }
                    }''')],

        [group: "P371 loop repros", name: "a body guard still discharges it", ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            while (i < n) { if (i != 3) s = 100.intdiv(i - 3); i++ }
                            s
                        }
                    }''')],

        // Before: `fails on: f(0, 0)` — n = 0 never enters the body.
        [group: "P371 loop repros", name: "the failing call enters the loop",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(1, 0)"], refute: "f(0, 0)",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n, int y) {
                            int s = 0
                            for (int i = 0; i < n; i++) { s = i % y }
                            s
                        }
                    }''')],

        // The invariant's arbitrary iteration happened to give a call that enters here; now it is one by construction.
        [group: "P371 loop repros", name: "an annotated loop's call enters it too",
         expect: ["Possible ArithmeticException: Math.floorMod(i, y) throws when y == 0", "fails on: f(1, 0)"], refute: "f(0, 0)",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n, int y) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) { s = Math.floorMod(i, y); i = i + 1 }
                            s
                        }
                    }''')],

        [group: "P371 loop repros", name: "a failure on a later iteration",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(2)"],
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) { s = 100.intdiv(i - 1); i = i + 1 }
                            s
                        }
                    }''')],

        // Before: `fails on: f(new int[0])`, which returns 0. The warning is the unannotated loop's over-strictness.
        [group: "P371 loop repros", name: "no run fails, so no call is shown",
         expect: ["Possible IndexOutOfBoundsException", "no failing call: the failure is at a loop iteration the check reaches through the loop's summary"],
         refute: "fails on",
         src: tc('''class A {
                        @Requires({ a != null })
                        static int f(int[] a) {
                            int s = 0
                            for (int i = 0; i < a.length; i++) { s = s + a[i] }
                            s
                        }
                    }''')],

        // The boundary: a failure first reached on the tenth iteration keeps its warning, without a call (before, the
        // invariant's model happened to give f(10), which does fail; one past the search is withheld, right or not).
        [group: "P371 loop repros", name: "a failure past the eighth iteration",
         expect: ["Possible ArithmeticException: Division by zero", "no failing call"], refute: "fails on",
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) { s = 100.intdiv(i - 9); i = i + 1 }
                            s
                        }
                    }''')],

        [group: "P371 loop repros", name: "after the loop, a run that leaves it",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f(new int[0], 0)"], refute: "(after a loop)",
         src: tc('''class A {
                        @Requires({ a != null && n >= 0 })
                        static int f(int[] a, int n) {
                            int i = 0
                            while (i < n) { i = i + 1 }
                            a[i]
                        }
                    }''')],
    ]
}
