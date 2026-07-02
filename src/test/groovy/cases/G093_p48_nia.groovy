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

/** 'P48 NIA' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G093_p48_nia {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Nonlinear integer arithmetic via Z3\'s NIA solver: multiplication commutativity, positive product, non-negative square.'

    static final List<Map> CASES = [

        // ---------- Phase 48: NIA — variable multiplication + div/mod ----------
        // Commutativity is a Z3 theory consequence — no axiom needed.
        [group: 'P48 NIA', name: 'multiplication commutativity', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f(int a, int b) { (a * b == b * a) ? 1 : 0 }
                    }''')],
        // Sign reasoning: positive × positive = positive.
        [group: 'P48 NIA', name: 'positive product is positive', ok: true,
         src: tc('''class C {
                        @Requires({ a > 0 && b > 0 })
                        @Ensures({ result > 0 })
                        static int f(int a, int b) { a * b }
                    }''')],
        // Squaring is non-negative — Z3 NIA handles this.
        [group: 'P48 NIA', name: 'square is non-negative', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int i) { i * i }
                    }''')],
        // Bounded squaring: i in [0, 10] gives i*i in [0, 100].
        [group: 'P48 NIA', name: 'bounded square stays bounded', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i && i <= 10 })
                        @Ensures({ result <= 100 })
                        static int f(int i) { i * i }
                    }''')],
        // Refute: unbounded square can exceed any specific bound.
        [group: 'P48 NIA', name: 'unbounded square can exceed 100',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result <= 100 })
                        static int f(int i) { i * i }
                    }''')],
        // Two-variable multiplication with bounds.
        [group: 'P48 NIA', name: 'bounded variable product', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= a && a < 100 && 0 <= b && b < 100 })
                        @Ensures({ result < 10000 })
                        static int f(int a, int b) { a * b }
                    }''')],
        // Division by variable. Groovy's {@code /} on ints promotes to BigDecimal, so the
        // test casts back to int — same dance the existing Phase 8a tests use. The verifier
        // collects {@code DivideSite} for the {@code b != 0} check; the value goes through
        // {@code intDiv}.
        [group: 'P48 NIA', name: 'division floor behaviour', ok: true,
         src: tc('''class C {
                        @Requires({ b > 0 && a >= 0 })
                        @Ensures({ result * b <= a })
                        static int f(int a, int b) { (int)(a / b) }
                    }''')],
        // Modulo bound: a % b is in [0, b) for non-negative a and positive b.
        [group: 'P48 NIA', name: 'modulo result in [0, b)', ok: true,
         src: tc('''class C {
                        @Requires({ a >= 0 && b > 0 })
                        @Ensures({ result >= 0 && result < b })
                        static int f(int a, int b) { a % b }
                    }''')],
        // Division identity, Groovy-faithful: a.intdiv(b) * b + (a % b) == a, for ALL b != 0
        // (intdiv truncates, % is the sign-of-dividend remainder — the pair Groovy guarantees).
        // NB: the BigDecimal form `(a / b) * b + a % b` does NOT equal a in Groovy
        // ((5/2)*2 + 5%2 == 6), so the identity must use intdiv, not `/`.
        [group: 'P48 NIA', name: 'division identity holds', ok: true,
         src: tc('''class C {
                        @Requires({ b != 0 })
                        @Ensures({ result == a })
                        static int f(int a, int b) { a.intdiv(b) * b + (a % b) }
                    }''')],
        // Soundness: division by zero is still caught — implicit DivideSite obligation.
        [group: 'P48 NIA', name: 'division by zero refutes',
         expect: 'Possible ArithmeticException: Division by zero',
         src: tc('''class C {
                        static int f(int a, int b) { (int)(a / b) }
                    }''')],
        // Even-number predicate via modulo: n % 2 == 0 holds for the even branch.
        [group: 'P48 NIA', name: 'even predicate via modulo', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && n % 2 == 0 })
                        @Ensures({ result == 1 })
                        static int f(int n) { (n % 2 == 0) ? 1 : 0 }
                    }''')],
    ]
}
