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
 * 'P384 sum witness' — a false claim over an array's `.sum()` was "Could not decide", not refuted: saying so needs a model
 * of the sum function under its quantified base/step axioms, which the solver can't build in budget. An undecided query
 * with sums is now retried without those axioms, each sum term over at most three elements and defined as their
 * addition; a model of that, with the sum read as the true sum, is a model of the original (when no sum sits inside a
 * quantifier), so it is reported as an ordinary refutation with its failing call. Nothing here proves anything.
 */
class G427_p384_sum_witness {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 384: a false claim over an array's .sum() that the sum axioms left undecided is refuted by a bounded witness (arrays of up to three elements, the sum their addition), with its failing call; true claims still prove."

    static final List<Map> CASES = [

        // Before: `Could not decide postcondition of e (solver: timeout)`.
        [group: "P384 sum witness", name: "a sum the elements' bounds don't cap",
         expect: ["Cannot prove postcondition of e", "fails on: e([1] as int[])"],
         src: tc('''class A {
                        @Requires({ j != null && (0..<j.length).every { j[it] == 0 || j[it] == 1 } })
                        @Ensures({ result < j.length })
                        static int e(int[] j) { j.sum() }
                    }''')],

        // Before: undecided. A quantifier over part of the array leaves j[0] free.
        [group: "P384 sum witness", name: "a sum over elements the precondition doesn't bound",
         expect: ["Cannot prove postcondition of e", "fails on: e(["],
         src: tc('''class A {
                        @Requires({ j != null && j.length > 1 && (1..<j.length).every { j[it] >= 0 } })
                        @Ensures({ result >= 0 })
                        static int e(int[] j) { j.sum() }
                    }''')],

        // Before: undecided.
        [group: "P384 sum witness", name: "a sum after a store",
         expect: ["Cannot prove postcondition of e", "fails on: e(["],
         src: tc('''class A {
                        @Requires({ j != null && j.length > 0 && (0..<j.length).every { j[it] >= 0 } })
                        @Ensures({ result >= 0 })
                        static int e(int[] j) {
                            j[0] = -5
                            j.sum()
                        }
                    }''')],

        // Before: undecided. A callee's sum precondition the caller can't meet: the empty array.
        [group: "P384 sum witness", name: "a callee's sum precondition, unmet",
         expect: ["Cannot prove precondition of e0 at this call site", "fails on: e(new int[0])"],
         src: tc('''class A {
                        @Requires({ xs != null && 0 <= m && m <= xs.sum() })
                        static int e0(int[] xs, int m) { 0 }
                        @Requires({ j != null && (0..<j.length).every { j[it] == 0 || j[it] == 1 } })
                        static int e(int[] j) { e0(j, 1) }
                    }''')],

        // Before: undecided (the ClearSplit report's `m4`): bump adds one to the sum, so it isn't kept at 0.
        [group: "P384 sum witness", name: "a sum invariant a call breaks",
         expect: "Cannot prove loop invariant is preserved by the loop body in m4",
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result.length == a.length && result.sum() == a.sum() + 1 })
                        static int[] bump(int[] a) {
                            int[] r = new int[a.length]
                            for (int k = 0; k < a.length; k++) r[k] = a[k]
                            r[0] = r[0] + 1
                            r
                        }
                        @Requires({ n >= 1 && m > 0 })
                        static int[] m4(int n, int m) {
                            int[] v = new int[m]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.length == m && v.sum() == 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                v = bump(v)
                                i = i + 1
                            }
                            return v
                        }
                    }''')],

        // Before: undecided. A wrong body: its own sum postcondition, refuted with the arguments that show it.
        [group: "P384 sum witness", name: "a body whose sum is off",
         expect: ["Cannot prove postcondition of bump", "fails on: bump(["],
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result.length == a.length && result.sum() == a.sum() + 1 })
                        static int[] bump(int[] a) {
                            int[] r = new int[a.length]
                            r[0] = 1
                            r
                        }
                    }''')],

        // The true claims still prove: the witness never runs on them, and finds nothing if it did.
        [group: "P384 sum witness", name: "true sum bounds still prove",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null && (0..<j.length).every { j[it] == 0 || j[it] == 1 } })
                        @Ensures({ result <= j.length && result >= 0 })
                        static int e(int[] j) { j.sum() }
                    }''')],
    ]
}
