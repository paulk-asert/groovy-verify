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
 * 'P378 sum fold' — the ClearSplit port's conservation theorem as a fold, `bal = afterExpenseRow(bal, …)` in a loop
 * with the invariant `bal.sum() == 0`, timed out instead of proving. Two causes. A zero-filled `new int[m]` never
 * established `bal.sum() == 0`: from the recursive sum axioms that needs induction over the length; a constant array's
 * sum is now ground. And the call's `result`, renamed to the caller's `bal` (Phase 375), collided with the callee's
 * formal `bal`, whose aliasing rebinds that name while the @Ensures is read: the result's facts landed on the argument.
 * The result is now assumed of its own fresh slot, then becomes the name's.
 */
class G422_p378_sum_fold {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 378: a zero-filled array's sum is 0 (a constant array's sum is ground), and a call's result is assumed of its own slot before it becomes the assigned name, so a callee formal of the same name no longer takes its facts: a sum-conserving fold over a contracted call proves."

    /** The report's row step: one expense's shares flat[o ..< o + bal.length] applied to the balances. */
    static final String ROW = '''
                        @Requires({ bal != null && flat != null && 0 <= o && o + bal.length <= flat.length && 0 <= payer && payer < bal.length })
                        @Ensures({ result != null && result.length == bal.length })
                        @Ensures({ flat[o..<o + bal.length].sum(0) == amount ==> result.sum() == bal.sum() })
                        static int[] afterExpenseRow(int[] bal, int payer, int amount, int[] flat, int o) {
                            int n = bal.length
                            int[] result = new int[n]
                            int r = 0
                            int b = 0
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && n == bal.length && result.length == n && 0 <= o && o + n <= flat.length && 0 <= payer && payer < n })
                            @Invariant({ r == result[0..<i].sum(0) && b == bal[0..<i].sum(0) && s == flat[o..<o + i].sum(0) })
                            @Invariant({ r == b + (payer < i ? amount : 0) - s })
                            @Decreases({ n - i })
                            while (i < n) {
                                result[i] = bal[i] + (i == payer ? amount : 0) - flat[o + i]
                                r = r + result[i]
                                b = b + bal[i]
                                s = s + flat[o + i]
                                i = i + 1
                            }
                            return result
                        }'''

    static final List<Map> CASES = [

        // Before: `Could not decide loop-invariant establishment` (the solver can't induct over m).
        [group: "P378 sum fold", name: "a new array's sum is zero",
         ok: true,
         src: tc('''class A {
                        @Requires({ m > 0 && n >= 0 })
                        @Ensures({ result.sum() == 0 })
                        static int[] f(int m, int n) {
                            int[] bal = new int[m]
                            int e = 0
                            @Invariant({ 0 <= e && e <= n && bal != null && bal.length == m && bal.sum() == 0 })
                            @Decreases({ n - e })
                            while (e < n) {
                                e = e + 1
                            }
                            return bal
                        }
                    }''')],

        // Before: timed out — the callee's formal `bal` took the result's facts.
        [group: "P378 sum fold", name: "a sum-conserving call whose formal shares the name",
         expect: "Skipped verification of postcondition for step", refute: ["Cannot prove", "Could not decide"],
         src: tc('''class A {
                        @Requires({ bal != null })
                        @Ensures({ result != null && result.length == bal.length && result.sum() == bal.sum() })
                        static int[] step(int[] bal) { bal.clone() }
                        @Requires({ m > 0 && n >= 0 })
                        @Ensures({ result.sum() == 0 })
                        static int[] f(int m, int n) {
                            int[] bal = new int[m]
                            int e = 0
                            @Invariant({ 0 <= e && e <= n && bal != null && bal.length == m && bal.sum() == 0 })
                            @Decreases({ n - e })
                            while (e < n) {
                                bal = step(bal)
                                e = e + 1
                            }
                            return bal
                        }
                    }''')],

        // Before: compiled cleanly — the clash read `result.length == bal.length + 1` of the argument alone, a
        // contradiction, so every claim after the call proved (Phase 375 opened this for arrays).
        [group: "P378 sum fold", name: "a growing call whose formal shares the name",
         expect: ["Cannot prove postcondition of f", "fails on: f(1)"],
         src: tc('''class A {
                        @Requires({ bal != null })
                        @Ensures({ result != null && result.length == bal.length + 1 })
                        static int[] grow(int[] bal) { new int[bal.length + 1] }
                        @Requires({ m > 0 })
                        @Ensures({ result == m })
                        static int f(int m) {
                            int[] bal = new int[m]
                            bal = grow(bal)
                            bal.length
                        }
                    }''')],

        // … whose true postcondition proves.
        [group: "P378 sum fold", name: "… and its true postcondition proves",
         ok: true,
         src: tc('''class A {
                        @Requires({ bal != null })
                        @Ensures({ result != null && result.length == bal.length + 1 })
                        static int[] grow(int[] bal) { new int[bal.length + 1] }
                        @Requires({ m > 0 })
                        @Ensures({ result == m + 1 })
                        static int f(int m) {
                            int[] bal = new int[m]
                            bal = grow(bal)
                            bal.length
                        }
                    }''')],

        // Before: compiled cleanly (the same vacuity, older: Phase 225's list route) — for a re-assigned list parameter …
        [group: "P378 sum fold", name: "a list call whose formal shares the name",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result != null && result.size() == xs.size() + 1 })
                        static List<Integer> grow(List<Integer> xs) { List<Integer> r = []; r.addAll(xs); r.add(0); r }
                        @Requires({ xs != null })
                        @Ensures({ result == 42 })
                        static int f(List<Integer> xs) {
                            xs = grow(xs)
                            xs.size()
                        }
                    }''')],

        // Before: compiled cleanly — … and for a new local named as the formal, though the argument is another list.
        [group: "P378 sum fold", name: "… and a local named as the formal",
         expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        @Requires({ xs != null })
                        @Ensures({ result != null && result.size() == xs.size() + 1 })
                        static List<Integer> grow(List<Integer> xs) { List<Integer> r = []; r.addAll(xs); r.add(0); r }
                        @Requires({ v != null })
                        @Ensures({ result == 42 })
                        static int f(List<Integer> v) {
                            List<Integer> xs = grow(v)
                            xs.size()
                        }
                    }''')],

        // Before: `Could not decide loop-invariant establishment`. The report's theorem: each expense's shares sum to
        // its amount, so the balances keep summing to zero.
        [group: "P378 sum fold", name: "the conservation fold proves",
         ok: true,
         src: tc("""class A {${ROW}
                        @Requires({ members > 0 && payer != null && amount != null && off != null && flat != null })
                        @Requires({ payer.length == amount.length && off.length == amount.length })
                        @Requires({ (0..<payer.length).every { 0 <= payer[it] && payer[it] < members && 0 <= off[it] && off[it] + members <= flat.length } })
                        @Requires({ (0..<payer.length).every { flat[off[it]..<off[it] + members].sum(0) == amount[it] } })
                        @Ensures({ result.sum() == 0 })
                        static int[] foldWith(int members, int[] payer, int[] amount, int[] flat, int[] off) {
                            int[] bal = new int[members]
                            int e = 0
                            @Invariant({ 0 <= e && e <= payer.length && payer.length == amount.length && off.length == amount.length })
                            @Invariant({ bal != null && bal.length == members && bal.sum() == 0 })
                            @Invariant({ (0..<payer.length).every { 0 <= payer[it] && payer[it] < members && 0 <= off[it] && off[it] + members <= flat.length } })
                            @Invariant({ (0..<payer.length).every { flat[off[it]..<off[it] + members].sum(0) == amount[it] } })
                            @Decreases({ payer.length - e })
                            while (e < payer.length) {
                                bal = afterExpenseRow(bal, payer[e], amount[e], flat, off[e])
                                e = e + 1
                            }
                            return bal
                        }
                    }""")],

        // Without that hypothesis it must not prove: refuted (Phase 384's bounded sum witness; before, undecided — a
        // refutation needed a model of the sum's axioms).
        [group: "P378 sum fold", name: "… and doesn't without its hypothesis",
         expect: "Cannot prove loop invariant is preserved by the loop body in foldWithout",   // Phase 384: refuted, was undecided
         src: tc("""class A {${ROW}
                        @Requires({ members > 0 && payer != null && amount != null && off != null && flat != null })
                        @Requires({ payer.length == amount.length && off.length == amount.length })
                        @Requires({ (0..<payer.length).every { 0 <= payer[it] && payer[it] < members && 0 <= off[it] && off[it] + members <= flat.length } })
                        @Ensures({ result.sum() == 0 })
                        static int[] foldWithout(int members, int[] payer, int[] amount, int[] flat, int[] off) {
                            int[] bal = new int[members]
                            int e = 0
                            @Invariant({ 0 <= e && e <= payer.length && payer.length == amount.length && off.length == amount.length })
                            @Invariant({ bal != null && bal.length == members && bal.sum() == 0 })
                            @Invariant({ (0..<payer.length).every { 0 <= payer[it] && payer[it] < members && 0 <= off[it] && off[it] + members <= flat.length } })
                            @Decreases({ payer.length - e })
                            while (e < payer.length) {
                                bal = afterExpenseRow(bal, payer[e], amount[e], flat, off[e])
                                e = e + 1
                            }
                            return bal
                        }
                    }""")],
    ]
}
