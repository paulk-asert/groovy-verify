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

/** 'P90 swap' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G106_p90_swap {

    static final List<Map> CASES = [
        // Phase 90 — bare multiple assignment / swap `(a, b) = [b, a]` on existing locals. The temp
        // captures the old state, so this is a correct *parallel* swap: a becomes 4, b becomes 3.
        // PROBE: user's int[] swap example (return a swapped array; @Ensures refs param elements).
        [group: 'P90 swap', name: 'array swap: return [from[1], from[0]] (with Requires)', ok: true,
         src: tc('''class C {
                        @Requires({ from != null && from.length >= 2 })
                        @Ensures({ result[0] == from[1] && result[1] == from[0] })
                        static int[] swap(int[] from) { [from[1], from[0]] }
                    }''')],
        [group: 'P90 swap', name: 'array swap without bounds Requires flags OOB', expect: 'out of bounds',
         src: tc('''class C {
                        @Ensures({ result[0] == from[1] && result[1] == from[0] })
                        static int[] swap(int[] from) { [from[1], from[0]] }
                    }''')],
        // PROBE: the user's second example — swap the params, relate result to old.b/old.a (property form
        // of `old` over PARAMETERS, unblocked at runtime by GROOVY-12078).
        [group: 'P90 swap', name: 'swap params: result.a == old.b (GROOVY-12078)', ok: true,
         src: tc('''class C {
                        @Ensures({ result.a == old.b && result.b == old.a })
                        static Map<String, Integer> swap(int a, int b) {
                            (a, b) = [b, a]
                            [a: a, b: b]
                        }
                    }''')],
        // SOUNDNESS: a wrong old.param relation (claims result.a == old.a, but it's old.b) must refute.
        [group: 'P90 swap', name: 'wrong old.param relation refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result.a == old.a && result.b == old.b })
                        static Map<String, Integer> swap(int a, int b) {
                            (a, b) = [b, a]
                            [a: a, b: b]
                        }
                    }''')],
        // README form 1 — 'final' params force the copy-into-locals (params stay immutable, so no 'old').
        [group: 'P90 swap', name: 'final params swap-locals (README form)', ok: true,
         src: tc('''class C {
                        @Ensures({ result.a == b && result.b == a })
                        static Map<String, Integer> swap(final int a, final int b) {
                            int x = a; int y = b
                            (x, y) = [y, x]   // parallel multiple assignment — RHS snapshotted before either write
                            [a: x, b: y]
                        }
                    }''')],

        // Dropping types works too — untyped params are fine; only the RETURN must be `Map` (not `def`),
        // so `result.a` resolves as a map-as-named-tuple read under @TypeChecked.
        [group: 'P90 swap', name: 'untyped params + raw Map return (result.a == old.b)', ok: true,
         src: tc('''class C {
                        @Ensures({ result.a == old.b && result.b == old.a })
                        static Map swap(a, b) {
                            (a, b) = [b, a]
                            [a: a, b: b]
                        }
                    }''')],

        [group: 'P90 swap', name: 'swap (a,b)=[b,a] reassigns in parallel', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 43 })
                        static int m() {
                            int a = 3; int b = 4
                            (a, b) = [b, a]
                            a * 10 + b
                        }
                    }''')],
        // Soundness: the parallel semantics matter. A *sequential* swap (`a = b; b = a`) would leave both
        // at 4 (== 44), so claiming 43 only proves if the RHS is captured before either store. The wrong
        // value refutes, confirming we model parallel (not sequential) assignment.
        [group: 'P90 swap', name: 'swap is parallel, not sequential (wrong value refutes)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 44 })
                        static int m() {
                            int a = 3; int b = 4
                            (a, b) = [b, a]
                            a * 10 + b
                        }
                    }''')],
        // Swap from a tuple factory, and a downstream read uses the swapped values.
        [group: 'P90 swap', name: 'swap via Tuple.tuple then use', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int m() {
                            int a = 5; int b = 9
                            (a, b) = Tuple.tuple(b, a)
                            a > b ? 1 : 0
                        }
                    }''')],
        // Swap feeding a CONTRACT (map-as-named-tuple result related to the inputs). The natural
        // spelling `(a, b) = [b, a]` on the *parameters* with `result.a == old.b` doesn't type-check /
        // isn't executable — `old` only snapshots `this`-class fields, not parameters (Phase 89 sl.2b),
        // and an untyped `def` return has no `.a` property. Reshaped to the executable form: swap
        // *locals*, so the params keep their entry values and `result.a == b` needs no `old`.
        [group: 'P90 swap', name: 'swap locals, map result relates to params', ok: true,
         src: tc('''class C {
                        @Ensures({ result.a == b && result.b == a })
                        static Map<String, Integer> swap(int a, int b) {
                            int x = a; int y = b
                            (x, y) = [y, x]
                            [a: x, b: y]
                        }
                    }''')],

        // 3-way parallel rotation: every element snapshotted before any write. a,b,c = 1,2,3 -> 3,1,2.
        [group: 'P90 swap', name: '3-way rotation (a,b,c)=[c,a,b]', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 312 })
                        static int m() {
                            int a = 1; int b = 2; int c = 3
                            (a, b, c) = [c, a, b]
                            a * 100 + b * 10 + c
                        }
                    }''')],
    ]
}
