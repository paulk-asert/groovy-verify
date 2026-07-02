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

/** 'P44 overflow' — 16 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G165_p44_overflow {

    static final List<Map> CASES = [

        // ---------- Phase 44: opt-in 32-bit integer overflow checks (@CheckOverflow) ----------
        // Bounded inputs let the overflow obligation discharge.
        [group: 'P44 overflow', name: 'addition with bounded inputs verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a >= 0 && a < 1000 && b >= 0 && b < 1000 })
                        static int add(int a, int b) { a + b }
                    }''')],
        // Unguarded increment refutes — Z3 picks n = Integer.MAX_VALUE and the addition overflows.
        [group: 'P44 overflow', name: 'unguarded increment refutes',
         expect: 'addition overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        static int incr(int n) { n + 1 }   // refutes
                    }''')],
        // Bound the input to make the increment safe. {@code Integer.MAX_VALUE} folds to the
        // literal 2147483647 via the JDK-range-constant peephole, so users can write the natural
        // spelling rather than the magic number.
        [group: 'P44 overflow', name: 'increment with Integer.MAX_VALUE bound verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ n < Integer.MAX_VALUE })
                        static int incr(int n) { n + 1 }
                    }''')],

        // Same for Integer.MIN_VALUE on the negation side.
        [group: 'P44 overflow', name: 'subtraction with Integer.MIN_VALUE bound verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a > Integer.MIN_VALUE && b == 1 })
                        static int dec(int a, int b) { a - b }
                    }''')],
        // Unary minus overflow — -Integer.MIN_VALUE = 2147483648, one past INT_MAX.
        [group: 'P44 overflow', name: 'unary minus on unbounded int refutes',
         expect: 'negation overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        static int neg(int a) { -a }
                    }''')],
        // Guard against the only failing value (INT_MIN); negation then verifies.
        [group: 'P44 overflow', name: 'unary minus with guard verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a > Integer.MIN_VALUE })
                        static int neg(int a) { -a }
                    }''')],
        // Division overflow — the only arithmetic case where / overflows is INT_MIN / -1.
        // Unguarded refutes; Z3 picks the specific failure pair. Groovy promotes int/int to
        // BigDecimal at the source level, so the explicit (int) cast keeps the method's int
        // return type — but the inner BinaryExpression a/b is what the collector picks up.
        [group: 'P44 overflow', name: 'unguarded division refutes on INT_MIN / -1',
         expect: 'division overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ b != 0 })
                        static int div(int a, int b) { (int)(a / b) }
                    }''')],
        // Guard against either pair member; division verifies.
        [group: 'P44 overflow', name: 'division with guard verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ b != 0 && !(a == Integer.MIN_VALUE && b == -1) })
                        static int div(int a, int b) { (int)(a / b) }
                    }''')],
        // % is unaffected — Java spec: Integer.MIN_VALUE % -1 == 0. (% returns int directly so no cast.)
        [group: 'P44 overflow', name: 'modulo never flagged for INT_MIN/-1', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ b != 0 })
                        static int mod(int a, int b) { a % b }
                    }''')],
        // Subtraction overflow: a - b could underflow Integer.MIN_VALUE.
        [group: 'P44 overflow', name: 'unguarded subtraction refutes',
         expect: 'subtraction overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        static int sub(int a, int b) { a - b }
                    }''')],
        // Multiplication: a * b can overflow even for small magnitudes (50000 * 50000 = 2.5e9 > INT_MAX).
        [group: 'P44 overflow', name: 'multiplication with tight bounds verifies', ok: true,
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a >= 0 && a < 10000 && b >= 0 && b < 10000 })
                        static int mul(int a, int b) { a * b }
                    }''')],
        [group: 'P44 overflow', name: 'multiplication with loose bounds refutes',
         expect: 'multiplication overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a >= 0 && a < 100000 && b >= 0 && b < 100000 })
                        static int mul(int a, int b) { a * b }
                    }''')],
        // Sub-expression aware: (a+1)*(a+1) emits two obligations — inner add and outer mul.
        // The outer mul refutes for a near sqrt(INT_MAX) ≈ 46341.
        [group: 'P44 overflow', name: 'sub-expression: nested op refutes',
         expect: 'multiplication overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ a >= 0 && a < 1_000_000 })
                        static int sq1(int a) { (a + 1) * (a + 1) }
                    }''')],
        // Class-level @CheckOverflow propagates to every method.
        [group: 'P44 overflow', name: 'class-level @CheckOverflow propagates',
         expect: 'addition overflows 32-bit signed range',
         src: tc('''@CheckOverflow
                    class C {
                        static int incr(int n) { n + 1 }
                    }''')],
        // Regression anchor: without @CheckOverflow, the same method verifies as math-int.
        // This guards the default-math-int experience for all existing code.
        [group: 'P44 overflow', name: 'no @CheckOverflow: math-int default unchanged', ok: true,
         src: tc('''class C {
                        @Ensures({ result == a + b })
                        static int add(int a, int b) { a + b }
                    }''')],
        // Phase 44c — implicit size upper bound. A method that indexes xs[i + 1] for i in
        // [0, xs.size()-1) can't overflow into a wrap-around index, because xs.size() ≤ INT_MAX
        // is asserted on the size oracle. Verified WITHOUT @CheckOverflow — this closes a
        // small soundness gap unconditionally.
        [group: 'P44 overflow', name: 'index arithmetic never overflows (implicit size bound)', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i && i + 1 < a.length })
                        static int pair(int[] a, int i) { a[i] + a[i + 1] }
                    }''')],
    ]
}
