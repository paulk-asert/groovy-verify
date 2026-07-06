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

/** 'P215 external specs' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G288_p215_external_specs {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The external-specification registry (JML .jml, in the project dialect): a library class is spec-ed by an ordinary Groovy SKELETON — the class re-declared with gc annotations and empty bodies — discovered lazily as the classpath resource META-INF/groovy-verify/specs/<fqn>.groovy (VERIFY_SPECS dir overrides for local iteration), parsed AST-only (no STC, no codegen) with ContractExpansionTransform attaching @ContractSource exactly as for user code. Consumption is symmetric with in-code contracts: the spec\'s @Requires is an OBLIGATION at every call site (STC\'s onMethodSelection hands the resolved JDK target; the registry supplies the contract), and its @Ensures is ASSUMED for the call\'s result (via resolveContractedCallee\'s registry fallback, covering the return-hoist and local-assignment paths). Flagship: java.lang.Math#abs — requires a > Integer.MIN_VALUE, ensures the sign-split definition. Every registry spec is trusted by definition (nobody proves the JDK), recorded via SpecRegistry.consumed() for the ledger. Also fixed en route: call-site precondition sessions now assert the Phase-44c JVM int bounds (the solver previously refuted with a = MIN_VALUE - 1, a value the runtime cannot exhibit).'

    static final List<Map> CASES = [

        // ---------- Phase 215: the external-spec registry (JML .jml, our dialect) ----------
        // The spec skeleton lives at src/main/resources/META-INF/groovy-verify/specs/java.lang.Math.groovy.
        [group: 'P215 external specs', name: 'Math.abs total spec consumed: ensures proves the caller', ok: true,
         src: tc('''class C {
                        @Requires({ a != Integer.MIN_VALUE })
                        @Ensures({ result >= 0 })
                        static int f(int a) {
                            return Math.abs(a)
                        }
                    }''')],
        // The classic abs bug, caught by the TOTAL spec (adopted from the OpenJML corpus reading):
        // abs wraps at MIN_VALUE, so `result >= 0` is simply FALSE there — the ensures refutes it.
        [group: 'P215 external specs', name: 'the abs wrap bug: unguarded result >= 0 refutes at MIN_VALUE', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int a) {
                            return Math.abs(a)
                        }
                    }''')],
        // The TRUE-precondition style lives on java.util.Arrays#binarySearch (result UNDEFINED unless
        // sorted — the JDK's rarest contract kind): calling it on a possibly-unsorted array refutes
        // the spec's @Requires at the call site.
        [group: 'P215 external specs', name: 'binarySearch requires sorted: unsorted call site refutes', expect: 'Cannot prove precondition of binarySearch',
         src: tc('''class C {
                        static int find(int[] a, int key) {
                            return java.util.Arrays.binarySearch(a, key)
                        }
                    }''')],
        // ...and a caller that KNOWS sortedness discharges it.
        [group: 'P215 external specs', name: 'binarySearch obligation discharged by caller sortedness', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.indices.every { it == 0 || a[it - 1] <= a[it] } })
                        static int find(int[] a, int key) {
                            return java.util.Arrays.binarySearch(a, key)
                        }
                    }''')],
        // Ensures teeth: an over-strong caller claim refutes through the spec (abs(0) == 0).
        [group: 'P215 external specs', name: 'over-strong caller claim refutes through the spec (abs(0) == 0)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != Integer.MIN_VALUE })
                        @Ensures({ result > 0 })
                        static int f(int a) {
                            return Math.abs(a)
                        }
                    }''')],
        // Assign position (the `T t = f(args)` path).
        [group: 'P215 external specs', name: 'spec consumed via local assignment (the T t = f(args) path)', ok: true,
         src: tc('''class C {
                        @Requires({ a > 0 })
                        @Ensures({ result == a })
                        static int f(int a) {
                            int r = Math.abs(a)
                            return r
                        }
                    }''')],
    ]
}
