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
 * 'P484 a literal's null element' — a local bound to a list literal is never null (Phase 277/386), and the dereference
 * check returned early for it — for an element read through it too, so {@code List<String> xs = [null]; xs[0].length()}
 * passed (Phase 483 found it, and narrowed the return for a map's value). A literal's elements had no null flags either
 * (Phase 477 bound their values only). Measured on Groovy 6.0.0: {@code [null][0].length()} throws "Cannot invoke method
 * length() on null object".
 */
class G525_p484_literal_null_element {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 484: a list literal's elements carry their nullity — `List<String> xs = [null]; xs[0].length()` fails (soundness: it passed, the local's never-null reaching its elements)."

    static final List<Map> CASES = [

        // ---------- a null element ----------
        [group: "P484 a literal's null element", name: "a null element's call", expect: ['Cannot invoke method length() on null object', 'obligation: xs[0] != null', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            List<String> xs = [null]
                            return xs[0].length()
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "… read by get", expect: ['Cannot invoke method length() on null object', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            List<String> xs = [null]
                            return xs.get(0).length()
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "… the second", expect: ['Cannot invoke method length() on null object', 'obligation: xs[1] != null', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            List<String> xs = ['a', null]
                            return xs[0].length() + xs[1].length()
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "… copied to a local", expect: ['Cannot invoke method length() on null object', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            List<String> xs = [null]
                            String y = xs[0]
                            return y.length()
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "… an assertion", expect: ['Assertion may not hold: (xs[0] != null)', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            List<String> xs = [null]
                            assert xs[0] != null
                            return 1
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "a parameter's element", expect: ['Cannot invoke method length() on null object', 'fails on: f(null)'],
         src: tc('''class A {
                        static int f(String s) {
                            List<String> xs = [s]
                            return xs[0].length()
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "a fresh collection's element", expect: ['Cannot invoke method length() on null object', 'obligation: r[0] != null'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<String> xs) {
                            List<String> r = xs.toList()
                            return r.size() > 0 ? r[0].length() : 0
                        }
                    }''')],

        // ---------- non-null elements still prove ----------
        [group: "P484 a literal's null element", name: "string elements", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            List<String> xs = ['a', 'bc']
                            return xs[0].length() + xs.get(1).length()
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "a parameter stated non-null", ok: true,
         src: tc('''class A {
                        @Requires({ s != null })
                        static int f(String s) {
                            List<String> xs = [s]
                            return xs[0].length()
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "a primitive's element", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> xs = [n]
                            assert xs[0] != null
                            return 1
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "a null element overwritten", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            List<String> xs = [null]
                            xs[0] = 'a'
                            return xs[0].length()
                        }
                    }''')],
        [group: "P484 a literal's null element", name: "a guard", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            List<String> xs = ['a', null]
                            return xs[1] != null ? xs[1].length() : xs[0].length()
                        }
                    }''')],
    ]
}
