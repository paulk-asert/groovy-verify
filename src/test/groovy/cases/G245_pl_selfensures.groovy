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

/** 'PL-selfensures' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G245_pl_selfensures {

    static final List<Map> CASES = [

        // ----- @SelfEnsures — the (single-expression) body IS the postcondition (prototype) -----
        // The body is lifted into `result == body`; it verifies (vacuous equality + real totality on the body).
        [group: 'PL-selfensures', name: 'self: expression body verifies (derived result == body)', ok: true,
         src: tc('''class C { @SelfEnsures static int dbl(int x) { x * 2 } }''')],
        // The derived equation feeds the @Reducer monoid-law proof — no hand-written @Ensures({ result == a + b }).
        [group: 'PL-selfensures', name: 'self: @Reducer reads the body equation, monoid laws prove', ok: true,
         src: tc('''class C {
                        @groovy.transform.Reducer(zero = '0')
                        @SelfEnsures
                        static int add(int a, int b) { a + b }
                    }''')],
        // A @SelfEnsures combiner used in another method's contract — equivalent to the @Ensures form.
        [group: 'PL-selfensures', name: 'self: combiner used in a contract (equivalent to @Ensures)', ok: true,
         src: tc('''class C {
                        @SelfEnsures
                        static String glue(String a, String b) { a + b }
                        @Ensures({ glue(s, t) == s + t })
                        static void check(String s, String t) { }
                    }''')],
        // The derived equation is genuinely used: a @SelfEnsures combiner whose body isn't associative is refuted
        // by the @Associative law — exactly as the hand-written @Ensures({ result == a - b }) form is.
        [group: 'PL-selfensures', name: 'self: @Associative on a subtraction body refutes (equation used)', expect: 'Cannot prove @Reducer associativity',
         src: tc('''class C {
                        @groovy.transform.Associative
                        @SelfEnsures
                        static int sub(int a, int b) { a - b }
                    }''')],
        // Loud error: @SelfEnsures on a non-expression (multi-statement) body — there's no single expression to lift.
        [group: 'PL-selfensures', name: 'self: non-expression body is a loud error', expect: '@SelfEnsures requires a single-expression body',
         src: tc('''class C { @SelfEnsures static int f(int x) { int y = x + 1; return y } }''')],
    ]
}
