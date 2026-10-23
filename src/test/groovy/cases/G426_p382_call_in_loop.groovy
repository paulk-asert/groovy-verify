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
 * 'P382 call in a loop' — a callee's precondition at a call inside an annotated loop is checked under the loop's
 * invariant, with the body replayed up to the call; that replay had no call handler, so a contracted call before it
 * left its result's oracles fresh: `int[] owed = row(flat, off[e], members)` gave `owed` no length or non-nullity, and
 * `afterExpense(bal, p, amount[e], owed)` timed out on `shares != null` — though an `assert` of the same facts just
 * before it proved (the loop's own pass has the handler). The ClearSplit port's fourth finding.
 */
class G426_p382_call_in_loop {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 382: a call inside an annotated loop has its precondition checked with the loop body's earlier contracted calls framed (their @Ensures assumed), as the loop's own pass does."

    static final String HELPERS = '''
                        @Requires({ n >= 0 })
                        @Ensures({ result != null && result.length == n })
                        static int[] mk(int n) { new int[n] }
                        @Requires({ a != null && b != null && a.length == b.length })
                        static int use(int[] a, int[] b) { 0 }'''

    static final List<Map> CASES = [

        // Before: `Cannot prove precondition of use at this call site`, falsely — `w`'s oracles were fresh there.
        [group: "P382 call in a loop", name: "a contracted call's result reaches a later call's precondition",
         ok: true,
         src: tc("""class A {${HELPERS}
                        @Requires({ n >= 1 && m >= 0 })
                        static int f(int n, int m) {
                            int[] v = new int[m]
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.length == m })
                            @Decreases({ n - i })
                            while (i < n) {
                                int[] w = mk(m)
                                s = s + use(v, w)
                                i = i + 1
                            }
                            s
                        }
                    }""")],

        // The result's facts are the callee's: a length it doesn't promise isn't assumed.
        [group: "P382 call in a loop", name: "… and only what the callee promises",
         expect: "Cannot prove precondition of use at this call site",
         src: tc("""class A {${HELPERS}
                        @Requires({ n >= 1 && m >= 0 })
                        static int f(int n, int m) {
                            int[] v = new int[m]
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && v != null && v.length == m })
                            @Decreases({ n - i })
                            while (i < n) {
                                int[] w = mk(m + 1)
                                s = s + use(v, w)
                                i = i + 1
                            }
                            s
                        }
                    }""")],

        // Before: `Could not decide precondition of afterExpense at this call site` (line 89) — the report's repro.
        [group: "P382 call in a loop", name: "the reported fold: a row copied out, then passed on",
         ok: true,
         src: tc('''
                    class A {
                        /**
                         * The balances after an expense: the payer is owed the amount, and every member owes their
                         * share (Dafny's AddExpenseDelta). When the shares add up to the amount, no money is created
                         * or destroyed.
                         */
                        @Requires({ bal != null && shares != null && shares.length == bal.length && 0 <= payer && payer < bal.length })
                        @Ensures({ result != null && result.length == bal.length })
                        @Ensures({ (0..<bal.length).every { result[it] == bal[it] + (it == payer ? amount : 0) - shares[it] } })
                        @Ensures({ shares.sum() == amount ==> result.sum() == bal.sum() })
                        static int[] afterExpense(int[] bal, int payer, int amount, int[] shares) {
                            int n = bal.length
                            int[] result = new int[n]
                            int r = 0
                            int b = 0
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && n == bal.length && n == shares.length && result.length == n && 0 <= payer && payer < n })
                            @Invariant({ r == result[0..<i].sum(0) && b == bal[0..<i].sum(0) && s == shares[0..<i].sum(0) })
                            @Invariant({ r == b + (payer < i ? amount : 0) - s })
                            @Invariant({ (0..<i).every { result[it] == bal[it] + (it == payer ? amount : 0) - shares[it] } })
                            @Decreases({ n - i })
                            while (i < n) {
                                result[i] = bal[i] + (i == payer ? amount : 0) - shares[i]
                                r = r + result[i]
                                b = b + bal[i]
                                s = s + shares[i]
                                i = i + 1
                            }
                            return result
                        }
                    
                        /**
                         * The balances after member from pays member to: from is owed less, to owes less
                         * (Dafny's AddSettlementDelta), and the total is unchanged.
                         */
                        @Requires({ bal != null && 0 <= from && from < bal.length && 0 <= to && to < bal.length && from != to })
                        @Ensures({ result != null && result.length == bal.length && result.sum() == bal.sum() })
                        @Ensures({ (0..<bal.length).every { result[it] == bal[it] + (it == from ? amount : 0) - (it == to ? amount : 0) } })
                        static int[] afterSettlement(int[] bal, int from, int to, int amount) {
                            int n = bal.length
                            int[] result = new int[n]
                            int r = 0
                            int b = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && n == bal.length && result.length == n })
                            @Invariant({ 0 <= from && from < n && 0 <= to && to < n && from != to })
                            @Invariant({ r == result[0..<i].sum(0) && b == bal[0..<i].sum(0) })
                            @Invariant({ r == b + (from < i ? amount : 0) - (to < i ? amount : 0) })
                            @Invariant({ (0..<i).every { result[it] == bal[it] + (it == from ? amount : 0) - (it == to ? amount : 0) } })
                            @Decreases({ n - i })
                            while (i < n) {
                                result[i] = bal[i] + (i == from ? amount : 0) - (i == to ? amount : 0)
                                r = r + result[i]
                                b = b + bal[i]
                                i = i + 1
                            }
                            return result
                        }
                    
                        /**
                         * Everyone's balance after a history of expenses and then settlements, starting from zero:
                         * ClearSplit's conservation theorem. Expense e was paid by payer[e], cost amount[e] and its
                         * shares are flat[off[e] ..< off[e] + members]; settlement t paid paid[t] from from[t] to to[t].
                         * When every expense's shares add up to its amount, the balances always sum to zero.
                         */
                        @Requires({ members >= 0 && payer != null && amount != null && off != null && flat != null })
                        @Requires({ payer.length == amount.length && off.length == amount.length })
                        @Requires({ (0..<payer.length).every { 0 <= payer[it] && payer[it] < members && 0 <= off[it] && off[it] + members <= flat.length } })
                        @Requires({ (0..<payer.length).every { flat[off[it]..<off[it] + members].sum(0) == amount[it] } })
                        @Requires({ from != null && to != null && paid != null && from.length == to.length && paid.length == to.length })
                        @Requires({ (0..<from.length).every { 0 <= from[it] && from[it] < members && 0 <= to[it] && to[it] < members && from[it] != to[it] } })
                        @Ensures({ result.length == members && result.sum() == 0 })
                        static int[] of(int members, int[] payer, int[] amount, int[] flat, int[] off, int[] from, int[] to, int[] paid) {
                            int[] bal = new int[members]
                            int e = 0
                            @Invariant({ 0 <= e && e <= payer.length && payer.length == amount.length && off.length == amount.length })
                            @Invariant({ bal != null && bal.length == members && bal.sum() == 0 })
                            @Invariant({ (0..<payer.length).every { 0 <= payer[it] && payer[it] < members && 0 <= off[it] && off[it] + members <= flat.length } })
                            @Invariant({ (0..<payer.length).every { flat[off[it]..<off[it] + members].sum(0) == amount[it] } })
                            @Decreases({ payer.length - e })
                            while (e < payer.length) {
                                int p = payer[e]                                    // binding payer[e] didn't help either
                                int[] owed = row(flat, off[e], members)
                                assert 0 <= p && p < bal.length && owed.length == bal.length && owed.sum() == amount[e]
                                bal = afterExpense(bal, p, amount[e], owed)
                                e = e + 1
                            }
                            int t = 0
                            @Invariant({ 0 <= t && t <= from.length && from.length == to.length && paid.length == to.length })
                            @Invariant({ bal != null && bal.length == members && bal.sum() == 0 })
                            @Invariant({ (0..<from.length).every { 0 <= from[it] && from[it] < members && 0 <= to[it] && to[it] < members && from[it] != to[it] } })
                            @Decreases({ from.length - t })
                            while (t < from.length) {
                                bal = afterSettlement(bal, from[t], to[t], paid[t])
                                t = t + 1
                            }
                            return bal
                        }
                    
                        /** Row o ..< o + n of the flattened shares, as its own array. */
                        @Requires({ flat != null && n >= 0 && 0 <= o && o + n <= flat.length })
                        @Ensures({ result != null && result.length == n && result.sum() == flat[o..<o + n].sum(0) })
                        static int[] row(int[] flat, int o, int n) {
                            int[] result = new int[n]
                            int r = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && result.length == n && 0 <= o && o + n <= flat.length })
                            @Invariant({ r == result[0..<i].sum(0) && r == flat[o..<o + i].sum(0) })
                            @Decreases({ n - i })
                            while (i < n) {
                                result[i] = flat[o + i]
                                r = r + result[i]
                                i = i + 1
                            }
                            return result
                        }
                    }
''')],
    ]
}
