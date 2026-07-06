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

/** 'P217 jdk specs' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G289_p217_jdk_specs {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The starter JDK specs artifact (Slice C): shipped skeletons for java.lang.Math (abs, negateExact with its true-iff @ThrowsIf at MIN_VALUE, floorDiv with its zero-divisor @ThrowsIf), java.lang.Integer (signum, sign-split ensures), and java.util.Objects (requireNonNull — @ThrowsIf(null) plus a non-null ensures, consumed under the Object-formal leniency rule: a spec\'s Object parameter accepts any reference actual). Chosen for provably-TRUE contracts: every @ThrowsIf arm is a genuine iff (negateExact throws exactly at the one unrepresentable point; floorDiv exactly at zero divisor) — Integer.parseInt is deliberately absent because its exact throw condition is outside the fragment and @ThrowsIf is an iff contract (one-directional signals-style arms are recorded future work). Consumers prove conditional ensures under caller guards and refute over-strong claims through the specs; all consumption is ledgered.'

    static final List<Map> CASES = [

        // ---------- Phase 217: the starter JDK specs (Slice C) ----------
        // Skeletons: src/main/resources/META-INF/groovy-verify/specs/{java.lang.Math,java.lang.Integer,java.util.Objects}.groovy
        [group: 'P217 jdk specs', name: 'Math.negateExact: conditional ensures under the caller guard', ok: true,
         src: tc('''class C {
                        @Requires({ a != Integer.MIN_VALUE })
                        @Ensures({ result == -a })
                        static int f(int a) {
                            return Math.negateExact(a)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Integer.signum: sign-split ensures consumed', ok: true,
         src: tc('''class C {
                        @Requires({ a > 0 })
                        @Ensures({ result == 1 })
                        static int f(int a) {
                            return Integer.signum(a)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'over-strong signum claim refutes through the spec', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f(int a) {
                            return Integer.signum(a)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Objects.requireNonNull: non-null ensures (Object-formal leniency)', ok: true,
         src: tc('''class C {
                        @Ensures({ result != null })
                        static Object f(Object x) {
                            return java.util.Objects.requireNonNull(x)
                        }
                    }''')],
    ]
}
