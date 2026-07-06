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

/** 'P218 pure admission' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G290_p218_pure_admission {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = '@Pure admission: a registry-spec\'d JDK method marked @Pure becomes usable VOCABULARY inside contract expressions — @Ensures({ result == Math.abs(a) }) — modelled as an uninterpreted function whose defining axiom is the spec\'s own @Ensures, guarded by its @Requires (requires[a->E] ==> ensures[result->UF(E), a->E], asserted once per ground term; where the context admits a requires-violating argument no facts flow, keeping the MIN_VALUE edge honest). Purity is the admission gate twice over: statically an impure method is not a function (congruence would be unsound), dynamically groovy-contracts executes contract closures at runtime (the JDK method IS the runtime implementation — no shipped executable needed, unlike the spec-DSL helpers). Honest edges pinned: an ensures-free spec (floorDiv) yields an opaque UF — claims through it refuse to prove; an unspecced method (multiplyExact) stays a loud skip. v1 fragment: int-like signatures.'

    static final List<Map> CASES = [

        // ---------- Phase 218: @Pure admission — spec methods as contract vocabulary ----------
        [group: 'P218 pure admission', name: 'Math.abs as contract vocabulary: ensures proves', ok: true,
         src: tc('''class C {
                        @Requires({ a != Integer.MIN_VALUE })
                        @Ensures({ result == Math.abs(a) })
                        static int dist(int a) {
                            return a >= 0 ? a : -a
                        }
                    }''')],
        [group: 'P218 pure admission', name: 'wrong body refutes through the spec axiom', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != Integer.MIN_VALUE })
                        @Ensures({ result == Math.abs(a) })
                        static int dist(int a) {
                            return a >= 0 ? a : a
                        }
                    }''')],
        [group: 'P218 pure admission', name: 'signum in @Requires: sign fact derived from the axiom', ok: true,
         src: tc('''class C {
                        @Requires({ Integer.signum(x) == 1 })
                        @Ensures({ result > 0 })
                        static int f(int x) {
                            return x
                        }
                    }''')],
        [group: 'P218 pure admission', name: 'ensures-free spec is honestly opaque (floorDiv)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == Math.floorDiv(a, b) })
                        static int f(int a, int b) {
                            return 0
                        }
                    }''')],
        // (was floorMod until the post-218 expansion spec'd it — the boundary example must stay
        // genuinely unspecced, or the case flips from skip to spec-driven refute, as happened)
        [group: 'P218 pure admission', name: 'unspecced method stays a loud skip (multiplyExact)', expect: 'Skipped verification of postcondition',
         src: tc('''class C {
                        @Ensures({ result == Math.multiplyExact(a, b) })
                        static int f(int a, int b) {
                            return 0
                        }
                    }''')],
    ]
}
