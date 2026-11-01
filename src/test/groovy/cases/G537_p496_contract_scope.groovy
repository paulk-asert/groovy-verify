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

/**
 * 'P496 contract scope' — a name in a contract written elsewhere is that contract's, not the method's. A foreign
 * class's invariant, assumed for a receiver {@code b}, read its collection field's nullity, size and elements (and a
 * reference field's nullity) as the CALLER's own same-named variable: {@code B}'s {@code xs != null} proved the
 * caller's {@code xs != null}. Only an int field was receiver-qualified ({@code b$count}). And a subscript isn't
 * arithmetic: Phase 492's "a number's arithmetic is never null" took any binary expression of a number type, so
 * {@code b.xs[0] != null} proved.
 */
class G537_p496_contract_scope {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 496: a foreign invariant's fields are the receiver's in every oracle — its `xs != null` no longer proves the caller's own `xs != null` — and a subscript read of a number may be null."

    static String foreign(String inv, String fields, String method) { """@Invariant({ ${inv} })
                    final class B { ${fields} }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${method}
                    }""" }

    static final List<Map> CASES = [

        // ---------- a foreign invariant's fields are the receiver's ----------
        [group: "P496 contract scope", name: "a foreign invariant's list is the receiver's", expect: ['Cannot prove postcondition'],
         src: tc(foreign('xs != null && xs.size() > 0', 'List<Integer> xs', '''@Requires({ b != null })
                        @Ensures({ result })
                        static boolean f(B b, List<Integer> xs) { xs != null }'''))],
        [group: "P496 contract scope", name: "… its size", expect: ['Cannot prove postcondition'],
         src: tc(foreign('xs != null && xs.size() > 0', 'List<Integer> xs', '''@Requires({ b != null && xs != null })
                        @Ensures({ result > 0 })
                        static int f(B b, List<Integer> xs) { xs.size() }'''))],
        [group: "P496 contract scope", name: "… its elements", expect: ['Cannot prove postcondition'],
         src: tc(foreign('xs != null && xs.size() > 0 && xs[0] == 3', 'List<Integer> xs', '''@Requires({ b != null && xs != null && xs.size() > 0 })
                        @Ensures({ result == 3 })
                        static Integer f(B b, List<Integer> xs) { xs[0] }'''))],
        [group: "P496 contract scope", name: "… a reference field's nullity", expect: ['Cannot prove postcondition'],
         src: tc(foreign('name != null', 'String name', '''@Requires({ b != null })
                        @Ensures({ result })
                        static boolean f(B b, String name) { name != null }'''))],
        [group: "P496 contract scope", name: "… as an int field's value was", expect: ['Cannot prove postcondition'],
         src: tc(foreign('count >= 0', 'int count', '''@Requires({ b != null })
                        @Ensures({ result })
                        static boolean f(B b, int count) { count >= 0 }'''))],

        // ---------- a subscript isn't arithmetic ----------
        // outside the fragment until Phase 500 modelled a receiver's list; refuted since, as the element may be null
        [group: "P496 contract scope", name: "a receiver's element read may be null", expect: ['Cannot prove postcondition', 'fails on: f(new B(xs: [null]))'],
         src: tc('''final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        @Requires({ b != null && b.xs != null && b.xs.size() > 0 })
                        @Ensures({ result })
                        static boolean f(B b) { b.xs[0] != null }
                    }''')],
    ]
}
