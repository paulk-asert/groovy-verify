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

/** 'P223 catch-reachability' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G295_p223_catch_reachability {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Caller-side catch-reachability (Phase 223): entering a handler means some try-block source threw the caught type, so when every source is arm-characterised, the DISJUNCTION of the matching @ThrowsIf arm conditions is a fact at catch entry — catch (ArithmeticException e) after Math.floorDiv(a, b) knows b == 0. Consumes the only-when / JML-signals direction, so the soundness gates are mandatory: matching arms must be fully exhaustive (a one-directional arm disclaims exactly this direction); every call in the try must resolve to a registry spec with at least one arm, whose arm TYPES are read as the complete throw-type story (the implicit signals_only of a skeleton — true of every shipped spec, monitored by the rung spec-throw category); native throw operators of the caught type (% and / for ArithmeticException, indexing for IOOBE) decline; NPE and broad catch types are never attempted; instantiated conditions must be prefix-independent (referencing no name assigned in the try or earlier on the path). Mechanically: a SoftAssume step at catch entry (assumed when expressible, dropped soundly when not), the fact built by formal-to-actual substitution unioned across arity-matching overloads. Both directions pinned: the fact proves the b == 0 handler branch and refutes its contradiction; the non-exhaustive (parseInt) and second-source (%) gates yield no fact.'

    static final List<Map> CASES = [

        // ---------- Phase 223: catch-entry facts from registry arms ----------
        // the flagship: in the handler, floorDiv's arm says b == 0
        [group: 'P223 catch-reachability', name: 'catch (ArithmeticException) knows the divisor was zero', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) {
                            try {
                                int q = Math.floorDiv(a, b)
                                return q >= 0 ? q : 0
                            } catch (ArithmeticException e) {
                                return b == 0 ? 0 : -1
                            }
                        }
                    }''')],
        // teeth: the fact is real — contradict it and refute
        [group: 'P223 catch-reachability', name: 'the catch fact is directional: contradicting it refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int a, int b) {
                            try {
                                int q = Math.floorDiv(a, b)
                                return q >= 0 ? q : 0
                            } catch (ArithmeticException e) {
                                return b == 0 ? -1 : 0
                            }
                        }
                    }''')],
        // gate: a non-exhaustive arm yields NO fact (parseInt in the try)
        [group: 'P223 catch-reachability', name: 'gating: a non-exhaustive arm yields no catch fact (parseInt)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(String s) {
                            try {
                                int v = Integer.parseInt(s)
                                return v >= 0 ? v : 0
                            } catch (NumberFormatException e) {
                                return s == null ? 0 : -1
                            }
                        }
                    }''')],
        // gate: a native `/` in the try defeats the fact (another Arithmetic source)
        [group: 'P223 catch-reachability', name: 'gating: a native % in the try is another source — no fact', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int a, int b, int c) {
                            try {
                                int q = Math.floorDiv(a, b)
                                int r = q % c
                                return r >= 0 ? r : 0
                            } catch (ArithmeticException e) {
                                return b == 0 ? 0 : -1
                            }
                        }
                    }''')],
        // checkIndex variant: the handler knows the index was out of range
        [group: 'P223 catch-reachability', name: 'catch (IndexOutOfBoundsException) knows the range violation', ok: true,
         src: tc('''class C {
                        @Requires({ n > 0 })
                        @Ensures({ result >= 0 })
                        static int f(int i, int n) {
                            try {
                                int j = java.util.Objects.checkIndex(i, n)
                                return j
                            } catch (IndexOutOfBoundsException e) {
                                return (i < 0 || i >= n) ? 0 : -1
                            }
                        }
                    }''')],
    ]
}
