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

/** 'P118 dataflow' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G226_p118_dataflow {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A single-assignment dataflow network desugars to SSA and proves its computed value (a+b); a wrong value refutes.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — concurrency: the contract needs threads/scheduling, not a parameter grid'

    static final List<Map> CASES = [
        // ---------- P118 dataflow: the determinacy half via single-assignment ----------
        // A dataflow network's defining structural guarantee is single-assignment: every DataflowVariable
        // is bound exactly once, and a read blocks until the bind happens. That makes the network's *value*
        // independent of the order the async tasks actually run — the determinacy half of the concurrency
        // trick. We assume that scheduling guarantee (we do NOT prove deadlock-freedom or termination) and
        // desugar the network into straight-line SSA: `new DataflowVariable()` drops out, `x << v` is the
        // single binding `x = v`, and `x.get()`/`await(x)`/`x.val` are just `x`. The functional value then
        // proves sequentially. async{} blocks flatten inline — sound precisely because single-assignment
        // makes the result order-independent.
        [group: 'P118 dataflow', name: 'dataflow network computes a + b', ok: true,
         src: tc("""class C {
                        @Ensures({ result == a + b })
                        static int dataflowSum(int a, int b) {
                            groovy.concurrent.DataflowVariable<Integer> x = new groovy.concurrent.DataflowVariable<Integer>()
                            groovy.concurrent.DataflowVariable<Integer> y = new groovy.concurrent.DataflowVariable<Integer>()
                            groovy.concurrent.DataflowVariable<Integer> z = new groovy.concurrent.DataflowVariable<Integer>()
                            async { x << a }
                            async { y << b }
                            async { z << x.get() + y.get() }
                            return z.get()
                        }
                    }""")],
        // A wrong functional claim about the same network is still refuted with a counterexample — the
        // determinacy assumption buys structure, not a free pass on the arithmetic.
        [group: 'P118 dataflow', name: 'wrong dataflow value is refuted', ok: false, expect: 'result',
         src: tc("""class C {
                        @Ensures({ result == a })
                        static int dataflowSum(int a, int b) {
                            groovy.concurrent.DataflowVariable<Integer> x = new groovy.concurrent.DataflowVariable<Integer>()
                            groovy.concurrent.DataflowVariable<Integer> y = new groovy.concurrent.DataflowVariable<Integer>()
                            groovy.concurrent.DataflowVariable<Integer> z = new groovy.concurrent.DataflowVariable<Integer>()
                            async { x << a }
                            async { y << b }
                            async { z << x.get() + y.get() }
                            return z.get()
                        }
                    }""")],
        // A two-variable network with a different operator: the binds are still single-assignment, so the
        // product proves under the same SSA desugaring.
        [group: 'P118 dataflow', name: 'two-variable dataflow product', ok: true,
         src: tc("""class C {
                        @Ensures({ result == a * b })
                        static int dataflowProd(int a, int b) {
                            groovy.concurrent.DataflowVariable<Integer> x = new groovy.concurrent.DataflowVariable<Integer>()
                            groovy.concurrent.DataflowVariable<Integer> y = new groovy.concurrent.DataflowVariable<Integer>()
                            async { x << a }
                            async { y << b }
                            return x.get() * y.get()
                        }
                    }""")],
    ]
}
