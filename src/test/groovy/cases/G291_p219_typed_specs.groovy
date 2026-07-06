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

/** 'P219 typed specs' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G291_p219_typed_specs {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Typed lookup disambiguation (Phase 219): same-arity overload PAIRS in a spec skeleton are now safe — Math\'s long overloads (abs/max/min/floorDiv/floorMod/addExact over longs) ship alongside their int siblings. Three lookup paths, three treatments: obligations were already typed (onMethodSelection hands the resolved target\'s parameter types); the ASSUMPTION path threads STC-inferred actual types through resolveContractedCallee; the ADMISSION path gets confident encoder-side static inference (declared-type variables, literals, casts, unary minus, agreeing ternaries, arithmetic — long if either side is long; unknown shapes are wildcards, and a confident contradiction with the matched spec\'s formals DECLINES admission rather than mis-bind an int-edged fact to a long argument). The teeth case proves the routing: the abs(long) wrap counterexample is -9223372036854775808 — the LONG MIN_VALUE, not the int one. addExact(long) uses the rearranged-comparison overflow idiom (no wider type to widen into), wrap-free at runtime too.'

    static final List<Map> CASES = [

        // ---------- Phase 219: typed disambiguation + the Math long overloads ----------
        // the showpiece: BOTH overloads consumed in one method, each picked by its argument's type
        [group: 'P219 typed specs', name: 'both abs overloads in one method, each routed by argument type', ok: true,
         src: tc('''class C {
                        @Requires({ i != Integer.MIN_VALUE && l != Long.MIN_VALUE })
                        @Ensures({ result >= 0 })
                        static long f(int i, long l) {
                            return Math.abs(i) + Math.abs(l)
                        }
                    }''')],
        // long abs total spec: the wrap edge is a LONG fact, not the int one
        [group: 'P219 typed specs', name: 'abs(long) wrap teeth: the counterexample is the LONG MIN_VALUE', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static long f(long a) {
                            return Math.abs(a)
                        }
                    }''')],
        // int consumption unchanged: MIN_VALUE-1 must NOT be a counterexample, int MIN must be
        [group: 'P219 typed specs', name: 'abs(int) consumption unchanged (regression pin)', ok: true,
         src: tc('''class C {
                        @Requires({ a != Integer.MIN_VALUE })
                        @Ensures({ result >= 0 })
                        static int f(int a) {
                            return Math.abs(a)
                        }
                    }''')],
        [group: 'P219 typed specs', name: 'floorMod(long): divisor-sign range over longs', ok: true,
         src: tc('''class C {
                        @Requires({ n > 0 })
                        @Ensures({ 0 <= result && result < n })
                        static long wrap(long i, long n) {
                            return Math.floorMod(i, n)
                        }
                    }''')],
        [group: 'P219 typed specs', name: 'addExact(long): the rearranged-comparison overflow guard', ok: true,
         src: tc('''class C {
                        @Requires({ a >= 0 && a <= 1000000 && b >= 0 && b <= 1000000 })
                        @Ensures({ result == a + b })
                        static long f(long a, long b) {
                            return Math.addExact(a, b)
                        }
                    }''')],
    ]
}
