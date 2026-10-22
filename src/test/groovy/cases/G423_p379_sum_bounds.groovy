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
 * 'P379 sum bounds' — the ClearSplit port's third finding: a callee requiring both
 * `(0..<joined.length).every { joined[it] == 0 || joined[it] == 1 }` and `0 <= left && left <= joined.sum()` timed out
 * at a call with `left = 0`, though its caller assumed the same quantifier. The mix wasn't the cause: no element bound
 * ever reached a sum, even `(0..<j.length).every { j[it] >= 0 }` never gave `j.sum() >= 0`, which from the recursive sum
 * axioms takes induction. An `every` bounding each element by constants now bounds every sum over a range of that
 * array: `lb * (hi - lo) <= sum <= ub * (hi - lo)`.
 */
class G423_p379_sum_bounds {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 379: an every that bounds an array's elements by constants (over its indices, or its elements) bounds every sum over a range of it, so a callee needing `m <= xs.sum()` discharges from the caller's element bounds."

    /** The report's callee (the original Split.handOut) and its call with nothing left over. */
    static final String HAND_OUT = '''
                    @Requires({ shares != null && joined != null && shares.length == joined.length })
                    @Requires({ (0..<joined.length).every { joined[it] == 0 || joined[it] == 1 } && 0 <= left && left <= joined.sum() })
                    @Ensures({ result.length == shares.length && result.sum() == shares.sum() + left })
                    @Ensures({ (0..<shares.length).every { result[it] == shares[it] || (joined[it] == 1 && result[it] == shares[it] + 1) } })
                    static int[] handOut(int[] shares, int[] joined, int left) {
                        int n = shares.length
                        int[] result = new int[n]
                        int given = 0
                        int r = 0
                        int s = 0
                        int c = 0
                        int k = 0
                        @Invariant({ 0 <= k && k <= n && n == shares.length && n == joined.length && result.length == n })
                        @Invariant({ r == result[0..<k].sum(0) && s == shares[0..<k].sum(0) && c == joined[0..<k].sum(0) })
                        @Invariant({ given == (c < left ? c : left) && r == s + given })
                        @Invariant({ (0..<k).every { result[it] == shares[it] || (joined[it] == 1 && result[it] == shares[it] + 1) } })
                        @Decreases({ n - k })
                        while (k < n) {
                            if (given < left && joined[k] == 1) {
                                result[k] = shares[k] + 1
                                given = given + 1
                            } else {
                                result[k] = shares[k]
                            }
                            r = r + result[k]
                            s = s + shares[k]
                            c = c + joined[k]
                            k = k + 1
                        }
                        return result
                    }

                    @Requires({ joined != null && (0..<joined.length).every { joined[it] == 0 || joined[it] == 1 } })
                    @Ensures({ result.length == joined.length })
                    static int[] c(int[] joined) {
                        int[] shares = new int[joined.length]
                        handOut(shares, joined, 0)
                    }'''

    static final List<Map> CASES = [

        // Before: `Could not decide precondition of handOut at this call site` — the report's call, its callee whole.
        [group: "P379 sum bounds", name: "the reported call: a quantifier and a sum in one precondition",
         ok: true,
         src: tc("class A {${HAND_OUT}\n}")],

        // Before: timed out.
        [group: "P379 sum bounds", name: "a sum bounded below by its elements' bound",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null && (0..<j.length).every { j[it] >= 0 } })
                        @Ensures({ result >= 0 })
                        static int e(int[] j) { j.sum() }
                    }''')],

        // Before: timed out.
        [group: "P379 sum bounds", name: "… and above, for a 0/1 array",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null && (0..<j.length).every { j[it] == 0 || j[it] == 1 } })
                        @Ensures({ result <= j.length })
                        static int e(int[] j) { j.sum() }
                    }''')],

        // Before: timed out.
        [group: "P379 sum bounds", name: "an element-form every",
         ok: true,
         src: tc('''class A {
                        @Requires({ j != null && j.every { v -> v >= 2 } })
                        @Ensures({ result >= 2 * j.length })
                        static int e(int[] j) { j.sum() }
                    }''')],

        // Before: timed out. The callee's formal is tied to the actual by an equation: the bound crosses it.
        [group: "P379 sum bounds", name: "a callee's sum bound from the caller's element bound",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && 0 <= m && m <= xs.sum() })
                        static int e0(int[] xs, int m) { 0 }
                        @Requires({ j != null && (0..<j.length).every { j[it] == 0 || j[it] == 1 } })
                        static int e(int[] j) { e0(j, 0) }
                    }''')],

        // The bound is the elements': a 0/1 array may be all zeros, so `1 <= j.sum()` doesn't follow.
        [group: "P379 sum bounds", name: "a sum bound the elements don't give",
         expect: "precondition of e0",
         src: tc('''class A {
                        @Requires({ xs != null && 0 <= m && m <= xs.sum() })
                        static int e0(int[] xs, int m) { 0 }
                        @Requires({ j != null && (0..<j.length).every { j[it] == 0 || j[it] == 1 } })
                        static int e(int[] j) { e0(j, 1) }
                    }''')],

        // … nor a strict upper one.
        [group: "P379 sum bounds", name: "a strict bound the elements don't give",
         expect: "postcondition of e",
         src: tc('''class A {
                        @Requires({ j != null && (0..<j.length).every { j[it] == 0 || j[it] == 1 } })
                        @Ensures({ result < j.length })
                        static int e(int[] j) { j.sum() }
                    }''')],

        // A quantifier over part of the array bounds no sum over all of it.
        [group: "P379 sum bounds", name: "a quantifier over part of the array",
         expect: "postcondition of e",
         src: tc('''class A {
                        @Requires({ j != null && j.length > 1 && (1..<j.length).every { j[it] >= 0 } })
                        @Ensures({ result >= 0 })
                        static int e(int[] j) { j.sum() }
                    }''')],

        // The bound is of the array the quantifier read: after a store, it isn't that array.
        [group: "P379 sum bounds", name: "an array written after the quantifier",
         expect: "postcondition of e",
         src: tc('''class A {
                        @Requires({ j != null && j.length > 0 && (0..<j.length).every { j[it] >= 0 } })
                        @Ensures({ result >= 0 })
                        static int e(int[] j) {
                            j[0] = -5
                            j.sum()
                        }
                    }''')],
    ]
}
