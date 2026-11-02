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
 * 'P514 literal membership null' — Phase 38 folds {@code x in [a, b]} (and {@code contains}, a map literal's keys and
 * values) to {@code x == a || x == b} on the values alone. A null's value is free, so {@code s in ['ab']} could be
 * true for a null {@code s}: a false alarm where a contract says it isn't. A null literal on either side didn't
 * translate. Now a null equals only a null, by the two sides' null flags.
 */
class G555_p514_literal_membership_null {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 514: a literal list's membership (`x in [a, b]`, `contains`, a map literal's keys or values) compares a null as Groovy does, equal only to a null."

    static final List<Map> CASES = [
        [group: "P514 literal membership null", name: "a null String in a literal list", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (s == 'ab') })
                        static boolean f(String s) { s in ['ab'] }
                    }''')],
        [group: "P514 literal membership null", name: "… by contains", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (s == 'ab') })
                        static boolean f(String s) { ['ab', 'cd'].contains(s) && s != 'cd' }
                    }''')],
        [group: "P514 literal membership null", name: "… against a null element", ok: true,
         src: tc('''class C {
                        @Requires({ t == null })
                        @Ensures({ result == (s == 'ab' || s == null) })
                        static boolean f(String s, String t) { s in ['ab', t] }
                    }''')],
        [group: "P514 literal membership null", name: "a null Integer in a literal list", ok: true,
         src: tc('''class C {
                        @Ensures({ n != null || !result })
                        static boolean f(Integer n) { n in [1, 2] }
                    }''')],
        [group: "P514 literal membership null", name: "a null literal in a literal list", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (s == null) })
                        static boolean f(String s) { null in ['ab', s] }
                    }''')],
        [group: "P514 literal membership null", name: "… a null element in a literal list", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (s == 'ab' || s == null) })
                        static boolean f(String s) { s in ['ab', null] }
                    }''')],
        [group: "P514 literal membership null", name: "a null String's membership, not its non-nullity", expect: ['Cannot prove postcondition', 'fails on: f('],
         src: tc('''class C {
                        @Ensures({ result == (s != null) })
                        static boolean f(String s) { s in ['ab'] }
                    }''')],
        [group: "P514 literal membership null", name: "a null Integer, not a member", expect: ['Cannot prove postcondition', 'fails on: f(null)'],
         src: tc('''class C {
                        @Requires({ n == null || n == 1 })
                        @Ensures({ result })
                        static boolean f(Integer n) { n in [1, 2] }
                    }''')],
        [group: "P514 literal membership null", name: "an int in a literal list, as before", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (v == 1 || v == 2) })
                        static boolean f(int v) { v in [1, 2] }
                    }''')],
        [group: "P514 literal membership null", name: "… a null not matched by a value", ok: true,
         src: tc('''class C {
                        @Requires({ s == null && t != null })
                        @Ensures({ !result })
                        static boolean f(String s, String t) { s in ['ab', t] }
                    }''')],
        [group: "P514 literal membership null", name: "a map literal's null key", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (s == 'a') })
                        static boolean f(String s) { s in [a: 1, b: 2] && s != 'b' }
                    }''')],
    ]
}
