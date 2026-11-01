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
 * 'P507 elvis on a boxed null' — Groovy truth of a boxed integral value ({@code Integer n}) is false for its null as
 * well as its zero. Phase 98b's truth was {@code n != 0} alone, and a null's int term is free, so {@code n ?: 5} on a
 * null {@code n} could be any value: {@code @Ensures({ n != null || result == 5 })} was refuted on {@code f(null)}.
 * The truth of a boxed one by a name is now non-null and non-zero, in an elvis and in {@code n as boolean}.
 */
class G548_p507_elvis_boxed_null {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 507: Groovy truth of a boxed integral value is false for its null (`n ?: 5` on a null `Integer n` is 5, `n as boolean` false)."

    static final List<Map> CASES = [

        // ---------- an elvis on a boxed null ----------
        [group: "P507 elvis on a boxed null", name: "an elvis on a null Integer", ok: true,
         src: tc('''class C {
                        @Ensures({ n != null || result == 5 })
                        static Integer f(Integer n) { n ?: 5 }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "… its value either way", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (n == null || n == 0 ? 5 : n) })
                        static Integer f(Integer n) { n ?: 5 }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "… a Long's", ok: true,
         src: tc('''class C {
                        @Ensures({ n != null || result == 5L })
                        static Long f(Long n) { n ?: 5L }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "… a local's", ok: true,
         src: tc('''class C {
                        @Ensures({ n != null || result == 5 })
                        static Integer f(Integer n) { Integer m = n; m ?: 5 }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "… in a contract", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (n ?: 5) })
                        static int f(Integer n) { n == null || n == 0 ? 5 : n }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "a boxed value as boolean", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (n != null && n != 0) })
                        static boolean f(Integer n) { n as boolean }
                    }''')],

        // ---------- still refuted where wrong ----------
        [group: "P507 elvis on a boxed null", name: "an elvis's null not kept", expect: ['Cannot prove postcondition', 'fails on: f(null)'],
         src: tc('''class C {
                        @Ensures({ result == n })
                        static Integer f(Integer n) { n ?: 5 }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "… nor its zero", expect: ['Cannot prove postcondition', 'fails on: f(0)'],
         src: tc('''class C {
                        @Ensures({ result == (n == null ? 5 : n) })
                        static Integer f(Integer n) { n ?: 5 }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "… nor a contract's", expect: ['Cannot prove postcondition', 'fails on: f(null)'],
         src: tc('''class C {
                        @Ensures({ result == (n ?: 5) })
                        static int f(Integer n) { n == null ? 7 : n == 0 ? 5 : n }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "… a contract's on a zero", expect: ['Cannot prove postcondition', 'fails on: f(0)'],
         src: tc('''class C {
                        @Ensures({ result == (n ?: 5) })
                        static int f(Integer n) { n == null ? 5 : n }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "a contract's negated boxed value", ok: true,
         src: tc('''class C {
                        @Ensures({ !n || result == n })
                        static Integer f(Integer n) { n ?: 5 }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "a boxed null as boolean, not true", expect: ['Cannot prove postcondition', 'fails on: f(null)'],
         src: tc('''class C {
                        @Ensures({ result == (n == null || n != 0) })
                        static boolean f(Integer n) { n as boolean }
                    }''')],

        // ---------- guards ----------
        [group: "P507 elvis on a boxed null", name: "an int's elvis, by its zero", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (n == 0 ? 5 : n) })
                        static int f(int n) { n ?: 5 }
                    }''')],
        [group: "P507 elvis on a boxed null", name: "an elvis's value, never zero, divided by", ok: true,
         src: tc('''class C {
                        static int f(Integer n) { int d = n ?: 1; 100.intdiv(d) }
                    }''')],
    ]
}
