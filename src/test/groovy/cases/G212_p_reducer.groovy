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

/** 'P-reducer' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G212_p_reducer {

    static final List<Map> CASES = [

        // Phase 130 — a @Reducer/@Associative combiner *asserts* a monoid/semigroup; groovy-verify now derives and
        // discharges those laws automatically from the annotation + the combiner's equation (no spelled-out lemmas).
        [group: 'P-reducer', name: 'string concat monoid: @Reducer auto-proves assoc + identity', ok: true,
         src: tc('''class C {
                        @groovy.transform.Reducer(zero = '""')
                        @Ensures({ result == a + b })
                        static String glue(String a, String b) { a + b } }''')],
        [group: 'P-reducer', name: 'int sum monoid: @Reducer(zero=0) auto-proves', ok: true,
         src: tc('''class C {
                        @groovy.transform.Reducer(zero = '0')
                        @Ensures({ result == a + b })
                        static int add(int a, int b) { a + b } }''')],
        [group: 'P-reducer', name: '@Associative on subtraction refutes associativity', expect: 'Cannot prove @Reducer associativity',
         src: tc('''class C {
                        @groovy.transform.Associative
                        @Ensures({ result == a - b })
                        static int sub(int a, int b) { a - b } }''')],
        [group: 'P-reducer', name: 'wrong zero (1 for sum) refutes identity', expect: 'Cannot prove @Reducer identity',
         src: tc('''class C {
                        @groovy.transform.Reducer(zero = '1')
                        @Ensures({ result == a + b })
                        static int add(int a, int b) { a + b } }''')],
    ]
}
