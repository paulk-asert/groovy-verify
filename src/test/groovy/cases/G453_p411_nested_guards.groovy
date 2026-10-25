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
 * 'P411 nested guards' — seen in Phase 410. An obligation is discharged under the guards the operators before it imply:
 * `&&`'s left operand for its right, a ternary's condition for an arm. But only a TOP-LEVEL `&&`, `||` or ternary was
 * split. Nested inside anything else (`1 + (…)`, a call's argument, a declaration's value) the whole expression was one
 * leaf, its arms' obligations checked unguarded, and the witness was false: `1 + (a != null && a.length > 0 ? a[0] : 0)`
 * "failed on" `f(new int[0])`, which returns 1. The collector now records, for each site, the guards it runs under
 * within the expression, and both the value-flow pass and the region pass assume them. Where the expression itself
 * writes (`(j = j - 1) + (… ? a[j] : 0)`), a guard read at the statement's state could be stale, so its sites stay
 * unguarded, as before.
 */
class G453_p411_nested_guards {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 411: a ternary arm or short-circuit operand nested in a larger expression is checked under its guard, as a top-level one is — `1 + (a.length > 0 ? a[0] : 0)` proves — in the value-flow pass and the region pass alike; an expression that itself writes keeps its sites unguarded."

    static final List<Map> CASES = [

        // A false positive before, with a false witness: `fails on: f(new int[0])`, which returns 1
        [group: "P411 nested guards", name: "a ternary inside a sum",
         ok: true,
         src: tc('''class C {
                        static int f(int[] a) { 1 + (a != null && a.length > 0 ? a[0] : 0) }
                    }''')],

        [group: "P411 nested guards", name: "… a short-circuit `&&` and `||`",
         ok: true,
         src: tc('''class C {
                        static int f(int[] a, int x) {
                            x + ((a != null && a.length > 0 && a[0] > 0) ? 1 : 0) +
                                ((a == null || a.length == 0 || a[0] > 0) ? 1 : 0)
                        }
                    }''')],

        [group: "P411 nested guards", name: "… a call's argument, a declaration, an assert",
         ok: true,
         src: tc('''class C {
                        static int f(int[] a) {
                            int r = 2 * (a != null && a.length > 0 ? a[0] : 0)
                            assert 0 <= (a != null && a.length > 0 ? a[0] * 0 : 0)
                            return r + Math.abs(a != null && a.length > 0 ? a[0] : 0)
                        }
                    }''')],

        // … on the region pass too (the re-assignment of `s` takes the body out of the value-flow fragment)
        [group: "P411 nested guards", name: "… when the value-flow pass bails",
         ok: true,
         src: tc('''class C {
                        static int f(int[] a) {
                            int s = 0
                            s = s + (a != null && a.length > 0 ? a[0] : 0)
                            return s
                        }
                    }''')],

        [group: "P411 nested guards", name: "… and in a loop body",
         ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static int f(int[] a, int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            while (i < n) { s = s + (a != null && i < a.length ? a[i] : 0); i = i + 1 }
                            return s
                        }
                    }''')],

        // The teeth: an obligation the guard doesn't cover refutes, with a call that really fails
        [group: "P411 nested guards", name: "the other arm is not guarded by the condition",
         expect: ["Possible IndexOutOfBoundsException", "fails on: f(new int[0])"],
         src: tc('''class C {
                        static int f(int[] a) { 1 + (a != null && a.length > 0 ? 0 : a[0]) }
                    }''')],

        [group: "P411 nested guards", name: "a guarded arm's own failure keeps a real call",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f(new int[1])"],
         refute: "IndexOutOfBoundsException",
         src: tc('''class C {
                        static int f(int[] a) { 1 + (a != null && a.length > 0 ? 10 % a[0] : 0) }
                    }''')],

        // Kept unguarded: the expression writes `j` before the condition reads it
        [group: "P411 nested guards", name: "an expression that writes keeps its sites unguarded",
         expect: "Possible IndexOutOfBoundsException",
         src: tc('''class C {
                        static int f(int[] a, int i) {
                            int j = i
                            (j = j - 1) + (a != null && j >= 0 && j < a.length ? a[j] : 0)
                        }
                    }''')],
    ]
}
