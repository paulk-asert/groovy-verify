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

/** 'GROOVY-12071' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G204_groovy_12071 {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Generic-typed tuple slots / map values / list elements keep their declared type in a contract, so arithmetic on them needs no cast (GROOVY-12071).'

    static final List<Map> CASES = [

        // ---------- Generic types restored in @Ensures closures (GROOVY-12071) ----------
        // Before GROOVY-12071, a generic-typed accessor inside a re-parsed contract closure erased to
        // `Object`, so *arithmetic* / *ordering* on a tuple slot, map value, or generic-list element
        // wouldn't type-check — forcing `(int)` casts and the "compare in the contract, compute in the
        // body" idiom (and `double[]` instead of `List<Double>`). With the fix the closure keeps the
        // declared generics, so these all type-check bare AND verify. These cases guard that dependency.
        [group: 'GROOVY-12071', name: 'tuple param slot arithmetic (no cast)', ok: true,
         src: tc('''class C {
                       @Requires({ t.v1 == 10 && t.v2 == 20 })
                       @Ensures({ result == t.v1 + t.v2 })
                       static int f(Tuple2<Integer, Integer> t) { 30 }
                   }''')],
        [group: 'GROOVY-12071', name: 'map param value arithmetic (no cast)', ok: true,
         src: tc('''class C {
                       @Requires({ m.x == 3 && m.y == 4 })
                       @Ensures({ result == m.x + m.y })
                       static int f(Map<String, Integer> m) { 7 }
                   }''')],
        [group: 'GROOVY-12071', name: 'nested tuple access in contract (no cast)', ok: true,
         src: tc('''class C {
                       @Requires({ t.v1.v2 == 5 })
                       @Ensures({ result == t.v1.v2 })
                       static int f(Tuple2<Tuple2<Integer, Integer>, Integer> t) { 5 }
                   }''')],
        [group: 'GROOVY-12071', name: 'List<Double> element predicate (no double[] workaround)', ok: true,
         src: tc('''class C {
                       @Requires({ xs != null && xs.size() > 0 && xs[0] >= 0.0d })
                       @Ensures({ result >= 0.0d })
                       static double f(List<Double> xs) { xs[0] }
                   }''')],
        // A wrong slot-arithmetic claim still refutes — the no-cast spec carries real proof obligations.
        [group: 'GROOVY-12071', name: 'tuple param slot arithmetic: wrong claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ t.v1 == 10 && t.v2 == 20 })
                       @Ensures({ result == t.v1 + t.v2 + 1 })
                       static int f(Tuple2<Integer, Integer> t) { 30 }
                   }''')],
    ]
}
