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

/** 'P-strcat' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G210_p_strcat {

    static final List<Map> CASES = [

        // String concatenation lowers to Z3's Seq concat: associative, NOT commutative. The verifier proves the
        // law that holds for all strings and refutes the one that doesn't, naming a minimal counterexample.
        // The void @Ensures-over-params shapes are the verbatim README "String concatenation" example.
        [group: 'P-strcat', name: 'concat is associative (void @Ensures over params)', ok: true,
         src: tc('''class StringConcat {
                        @Ensures({ (a + b) + c == a + (b + c) })
                        static void associative(String a, String b, String c) { } }''')],
        [group: 'P-strcat', name: 'concat is NOT commutative (void) refutes', expect: 'Cannot prove postcondition of commutative',
         src: tc('''class StringConcat {
                        @Ensures({ a + b == b + a })
                        static void commutative(String a, String b) { } }''')],
        // Same two laws, phrased as a boolean-returning method whose body is the comparison (README notes this works too).
        [group: 'P-strcat', name: 'concat is associative (boolean result)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == true })
                        static boolean assoc(String a, String b, String c) { (a + b) + c == a + (b + c) } }''')],
        [group: 'P-strcat', name: 'concat is NOT commutative (boolean result) refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == true })
                        static boolean commut(String a, String b) { a + b == b + a } }''')],
    ]
}
