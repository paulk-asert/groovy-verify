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
 * 'P356 a helper loop evaluated at constants' — the closed evaluator (Phase 8a's `PureEvaluator.tryEvaluate`) ran
 * straight-line code, `if` and recursion; a loop was not evaluable, so `total(4)` with every argument a constant
 * stayed an uninterpreted function unless a Phase 355 invariant summarised it. Loops now run for real — while,
 * do/while, a classic for, a forwards range for-in, an annotated loop from its LoopSpec, `break` and `continue` —
 * bounded by the step budget, now reset per evaluation. Compound assignments, `++` statements, `%` (REMAINDER),
 * `intdiv` and `Math.max`/`min`/`abs` evaluate too. A same-class helper is no longer shadowed by a GDK built-in of
 * the same name in a contract.
 */
class G400_p356_helper_loop_eval {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 356 a helper loop evaluated at constants: a contract-free helper called with constant arguments runs its loops (while, do/while, classic for, forwards range for-in, an annotated loop from its specification, break and continue) within a per-evaluation step budget, with compound assignment, increments, `%`, `intdiv` and `Math.max`/`min`/`abs`; past the budget the call falls back to the symbolic routes. Fixed: a same-class helper named like a GDK aggregation (`sum`) was shadowed in contracts, and one budget-exhausting call made every later evaluation in the method fail.'

    static final List<Map> CASES = [

        // Before: the closed evaluator ran straight-line code and recursion only, and the symbolic summary (Phase 355)
        // needs an @Invariant, so `total(4)` was an uninterpreted function. Now the loop runs, bounded by the step budget.
        [group: "P356 a helper loop evaluated at constants", name: "an unannotated loop runs at a constant argument", ok: true,
         src: tc('''class A {
                        static int total(int x) { int s = 0; for (int i = 0; i < x; i++) { s = s + i }; return s }
                        @Ensures({ result == 6 })
                        static int f() { total(4) }
                    }''')],
        [group: "P356 a helper loop evaluated at constants", name: "… and a wrong constant refutes", expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static int total(int x) { int s = 0; for (int i = 0; i < x; i++) { s = s + i }; return s }
                        @Ensures({ result == 7 })
                        static int f() { total(4) }
                    }''')],
        [group: "P356 a helper loop evaluated at constants", name: "a while with a break", ok: true,
         src: tc('''class A {
                        static int firstOver(int lim) { int n = 1; while (true) { if (n * n > lim) break; n++ }; return n }
                        @Ensures({ result == 4 })
                        static int f() { firstOver(10) }
                    }''')],
        [group: "P356 a helper loop evaluated at constants", name: "a continue in a classic for still runs the update", ok: true,
         src: tc('''class A {
                        static int evens(int x) { int c = 0; for (int i = 0; i < x; i++) { if (i % 2 != 0) continue; c++ }; return c }
                        @Ensures({ result == 3 })
                        static int f() { evens(6) }
                    }''')],
        [group: "P356 a helper loop evaluated at constants", name: "a do/while runs its body once", ok: true,
         src: tc('''class A {
                        static int atLeastOnce(int x) { int c = 0; do { c++ } while (c < x); return c }
                        @Ensures({ result == 1 })
                        static int f() { atLeastOnce(0) }
                    }''')],
        [group: "P356 a helper loop evaluated at constants", name: "a range for-in with a Math.max bound", ok: true,
         src: tc('''class A {
                        static int squares(int x) { int s = 0; int hi = Math.max(x, 0); for (int i in 0..<hi) { s += i * i }; return s }
                        @Ensures({ result == 5 })
                        static int f() { squares(3) }
                    }''')],
        // The raw loop statement carries groovy-contracts' woven invariant checks; the evaluator runs the captured
        // LoopSpec (init, guard, body, update) instead.
        [group: "P356 a helper loop evaluated at constants", name: "an annotated loop runs from its specification", ok: true,
         src: tc('''class A {
                        static int evensTo(int x) {
                            int hi = Math.max(x, 0)
                            int c = 0
                            @Invariant({ 0 <= i && i <= hi && c == 2 * i })
                            @Decreases({ hi - i })
                            for (int i = 0; i < hi; i++) { c += 2 }
                            return c
                        }
                        @Ensures({ result == 10 })
                        static int f() { evensTo(5) }
                    }''')],
        // Groovy 6 parses `%` as REMAINDER (Phase 343), which the evaluator didn't know: `x % 7` wasn't evaluable.
        [group: "P356 a helper loop evaluated at constants", name: "digit sum with % and intdiv", ok: true,
         src: tc('''class A {
                        static int digitSum(int x) { int s = 0; int n = x; while (n > 0) { s += n % 10; n = n.intdiv(10) }; return s }
                        @Ensures({ result == 6 })
                        static int f() { digitSum(123) }
                    }''')],
        [group: "P356 a helper loop evaluated at constants", name: "a call in a caller's precondition", ok: true,
         src: tc('''class A {
                        static int total(int x) { int s = 0; for (int i = 0; i < x; i++) { s = s + i }; return s }
                        @Requires({ k == total(4) })
                        @Ensures({ result == 6 })
                        static int f(int k) { k }
                    }''')],
        // Fixed: in a contract the call reads `this.sum(4)`, which the GDK aggregation handler took for a list fold over
        // `this` (heavy axioms, a solver timeout). A same-class or sibling contract-free helper now takes precedence.
        [group: "P356 a helper loop evaluated at constants", name: "a helper named sum in a contract is the helper", ok: true,
         src: tc('''class A {
                        static int sum(int x) { int s = 0; for (int i = 0; i < x; i++) { s = s + i }; return s }
                        @Ensures({ result == sum(4) })
                        static int f() { 6 }
                    }''')],
        // 100,000 iterations exceed the evaluator's 20,000 steps: not evaluable, so the call is uninterpreted (no
        // @Invariant for a Phase 355 summary). Sound; the claim is true but unproved.
        [group: "P356 a helper loop evaluated at constants", name: "an argument past the step budget falls back to the symbolic routes", expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static int cnt(int x) { int s = 0; for (int i = 0; i < x; i++) { s++ }; return s }
                        @Ensures({ result == 100000 })
                        static int f() { cnt(100000) }
                    }''')],
        // Fixed: the budget was one per evaluator (one per method), so the exhausted call above left `cnt(3)` unevaluable.
        [group: "P356 a helper loop evaluated at constants", name: "… and it doesn't use up the budget for a later call", ok: true,
         src: tc('''class A {
                        static int cnt(int x) { int s = 0; for (int i = 0; i < x; i++) { s++ }; return s }
                        @Ensures({ result == cnt(3) })
                        static int f() { int big = cnt(100000); return 3 }
                    }''')],
    ]
}
