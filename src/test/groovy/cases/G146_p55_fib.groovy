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

/** 'P55 fib' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G146_p55_fib {

    static final List<Map> CASES = [
        [group: 'P55 fib', name: 'Fib.of(5) == 5', ok: true,
         src: tc('''class C {
                        @Ensures({ Fib.of(5) == 5 })
                        static void f() { }
                    }''')],
        // Non-vacuousness anchor (positive): the step law holds at a literal index. (Refuting a *false*
        // fib claim is the known weak direction — Z3 can't model the ∀ step axiom, so it returns honest
        // UNKNOWN rather than a counterexample.)
        [group: 'P55 fib', name: 'Fib step law at 6 holds', ok: true,
         src: tc('''class C {
                        @Ensures({ Fib.of(6) == Fib.of(5) + Fib.of(4) })
                        static void f() { }
                    }''')],
        // The textbook proof: an iterative Fibonacci provably equals the recursive definition. The
        // invariant carries the two-term recurrence (a == fib(i), b == fib(i+1)); the step axiom
        // re-establishes it across `b = a + b`. Terminates (`n - i`), unlike the outer prime_fib search.
        // (Bare `Fib.of` inside @Invariant resolves the import since GROOVY-12072 — no `verification.` FQN.)
        [group: 'P55 fib', name: 'iterative Fibonacci equals Fib.of(n)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == Fib.of(n) })
                        static int fibIter(int n) {
                            int a = 0
                            int b = 1
                            int i = 0
                            @Invariant({ 0 <= i && i <= n &&
                                         a == Fib.of(i) && b == Fib.of(i + 1) })
                            @Decreases({ n - i })
                            while (i < n) {
                                int t = a + b
                                a = b
                                b = t
                                i = i + 1
                            }
                            return a
                        }
                    }''')],
    ]
}
