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

/** 'P230 list interface specs' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G298_p230_list_interface_specs {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The java.util.List interface skeleton (Phase 230) — the LAST structural registry gap, closed with ZERO engine changes: the accumulated machinery (instance consumption, receiver-state substitution, element tying) composed to open the recorded gate on its own. Deliberately only what the native list oracles do not model exactly: indexOf/lastIndexOf(Object) with the receiver-state range ensures result >= -1 && result < size() — the String-indexOf twin, size() substituted onto the actual receiver at each site. The showpiece is the list indexOf-then-get idiom: the NATIVE list-get bounds obligation discharged by the REGISTRY fact plus the found-check; drop the check and the -1 sentinel refutes. java.util.Map needs no skeleton at all — membership, cardinality and getOrDefault are native, and keySet()/values() projections are outside the fragment (documented in the skeleton header).'

    static final List<Map> CASES = [

        // ---------- Phase 230: the List interface (the registry consumption story completes) ----------
        [group: 'P230 list interface specs', name: 'indexOf-then-get: the native bounds obligation discharged by the registry fact', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int findOrLast(List<Integer> xs, int v) {
                            int i = xs.indexOf(v)
                            if (i >= 0) {
                                return xs[i]
                            }
                            return xs[xs.size() - 1]
                        }
                    }''')],
        [group: 'P230 list interface specs', name: 'the -1 sentinel into get refutes without the found-check', expect: 'Possible IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int find(List<Integer> xs, int v) {
                            int i = xs.indexOf(v)
                            return xs[i]
                        }
                    }''')],
        [group: 'P230 list interface specs', name: 'lastIndexOf: the receiver-state upper bound in a caller ensures', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result < xs.size() })
                        static int f(List<Integer> xs, int v) {
                            return xs.lastIndexOf(v)
                        }
                    }''')],
    ]
}
