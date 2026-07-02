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

/** 'HE072 will_it_fly' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G249_he072_will_it_fly {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'HumanEval 072 — a list flies iff it is a palindrome and its sum <= w: a loop-built flag equals the content quantifier (0..<n).every { q[it]==q[n-1-it] }, an ends-only check refutes, the combined palindrome+sum proof, and forgetting the palindrome half refutes.'

    static final List<Map> CASES = [

        // ---------- will_it_fly (HumanEval/72) — a list flies iff it is a palindrome AND its sum <= w ----------
        // The palindrome predicate is the new shape: a loop-built boolean flag that must equal an array-content
        // quantifier `(0..<n).every { q[it] == q[n-1-it] }`. Rendered over the FULL range (like the Verus original),
        // so the loop invariant AT EXIT *is* the spec — no half-to-full quantifier step — and the early `return
        // false` witnesses the negation at the offending index.
        [group: 'HE072 will_it_fly', name: 'palindrome flag equals the content quantifier', ok: true,
         src: tc('''class C {
                        @Requires({ q != null })
                        @Ensures({ result == (0..<q.size()).every { q[it] == q[q.size() - 1 - it] } })
                        static boolean isPalindrome(List<Integer> q) {
                            int n = q.size()
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && n == q.size() && (0..<i).every { q[it] == q[n - 1 - it] } })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (q[i] != q[n - 1 - i]) return false
                                i = i + 1
                            }
                            return true
                        }
                    }''')],
        // Soundness: a check that only compares the two ENDS (q[0] == q[last]) is not a palindrome test — a list like
        // [1,2,3,1] passes the ends but isn't balanced — so claiming the full-palindrome spec refutes.
        [group: 'HE072 will_it_fly', name: 'ends-only check is not a palindrome (refutes)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ q != null })
                        @Ensures({ result == (0..<q.size()).every { q[it] == q[q.size() - 1 - it] } })
                        static boolean isPalindrome(List<Integer> q) {
                            return q.size() < 2 || q[0] == q[q.size() - 1]
                        }
                    }''')],
        // The full will_it_fly, both halves in one loop: a prefix-sum accumulator AND the palindrome flag, combined
        // into `palindrome && sum <= w`. (The Verus `break` once unbalanced is an optimisation only — the result
        // short-circuits on a non-palindrome regardless of the sum — so the break-free form computes the same value.)
        [group: 'HE072 will_it_fly', name: 'will_it_fly is palindrome AND within weight', ok: true,
         src: tc('''class C {
                        @Requires({ q != null })
                        @Ensures({ result == ((0..<q.size()).every { q[it] == q[q.size() - 1 - it] } && ((int) q.sum(0)) <= w) })
                        static boolean willItFly(List<Integer> q, int w) {
                            boolean palindrome = true
                            int sum = 0
                            int n = q.size()
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && n == q.size() &&
                                         sum == ((int) q[0..<i].sum(0)) &&
                                         (palindrome == (0..<i).every { q[it] == q[n - 1 - it] }) })
                            @Decreases({ n - i })
                            while (i < n) {
                                sum = sum + q[i]
                                if (q[i] != q[n - 1 - i]) palindrome = false
                                i = i + 1
                            }
                            return palindrome && sum <= w
                        }
                    }''')],
        // Soundness — and an honest boundary. Forgetting the palindrome half (returning just sum <= w) lets an
        // unbalanced-but-light list "fly" (the first doctest, will_it_fly([1,2], 5) == false), so the code is wrong.
        // The verifier soundly does NOT pass it — but the full spec conjoins TWO refute-hostile quantified facts (the
        // `every` palindrome and the `sum` aggregate), so finding a SAT model that violates the conjunction defeats
        // the solver: it soft-fails to "could not decide" rather than handing back a crisp counterexample. Same
        // prove-friendly / refute-hostile asymmetry as the gcd/recurrence helpers — never a false *pass*.
        [group: 'HE072 will_it_fly', name: 'forgetting the palindrome check is rejected (refute-hostile: could not decide)',
         ok: false, expect: 'Could not decide',
         src: tc('''class C {
                        @Requires({ q != null })
                        @Ensures({ result == ((0..<q.size()).every { q[it] == q[q.size() - 1 - it] } && ((int) q.sum(0)) <= w) })
                        static boolean willItFly(List<Integer> q, int w) {
                            return ((int) q.sum(0)) <= w
                        }
                    }''')],
    ]
}
