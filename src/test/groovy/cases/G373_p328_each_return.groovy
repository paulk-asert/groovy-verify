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
 * 'P328 return in a .each closure' — a {@code return} in a {@code .each} / {@code .eachWithIndex} closure ends only
 * that element's call, so the iteration goes on: it is a {@code continue}. Phase 310 skipped it loudly; the capture
 * now rewrites a bare {@code return}, or one of a constant or variable, as a {@code continue}
 * (ContractExpansionTransform.eachReturnsAsContinue), which Phases 324–327 desugar.
 */
class G373_p328_each_return {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 328 return in a .each closure: a bare return, or a return of a constant or variable, in a .each / .eachWithIndex closure ends only that element\'s call, and is modelled as the continue it acts like, so the guard before it shapes what the rest of the element sees. A return that evaluates anything else, or sits in a nested loop, still skips loudly. Fixed alongside: an assert in an auto-bounds-only .each body, and eachWithIndex\'s own index, counted as writes, so a postcondition after such a loop skipped loudly.'

    static final List<Map> CASES = [

        [group: 'P328 return in a .each closure', name: 'a bare return skips the rest of the element', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        static void f(int[] a) {
                            a.each { int x ->
                                if (x < 0) return
                                assert x >= 0
                            }
                        }
                    }''')],
        [group: 'P328 return in a .each closure', name: 'a guard that misses a value is refuted', expect: 'Assertion may not hold: (x > 0)',
         src: tc('''class C {
                        @Requires({ a != null })
                        static void f(int[] a) {
                            a.each { int x ->
                                if (x < 0) return
                                assert x > 0
                            }
                        }
                    }''')],
        [group: 'P328 return in a .each closure', name: 'a return of a constant in an eachWithIndex', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        static void f(int[] a) {
                            a.eachWithIndex { int v, int i ->
                                if (v == i) return 0
                                assert v != i
                            }
                        }
                    }''')],
        [group: 'P328 return in a .each closure', name: 'a return over a list with the implicit it', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.every { it != null } })
                        static void f(List<Integer> xs) {
                            xs.each {
                                if (it < 0) return
                                assert it >= 0
                            }
                        }
                    }''')],
        // The method's postcondition after the loop is unaffected by the closure's returns.
        [group: 'P328 return in a .each closure', name: 'a postcondition after a .each that returns', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result == 7 })
                        static int f(int[] a) {
                            a.each { int v ->
                                if (v == 0) return
                                assert v != 0
                            }
                            return 7
                        }
                    }''')],

        // ---------- fixed alongside ----------
        // An assert writes nothing, and neither does eachWithIndex's index beyond its own step: both used to make
        // the loop "accumulating", so the postcondition skipped loudly.
        [group: 'P328 return in a .each closure', name: 'an assert in a .each body is not an accumulation', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 7 })
                        static int f(int[] a) { a.each { int v -> assert v == v }; return 7 }
                    }''')],
        [group: 'P328 return in a .each closure', name: 'an eachWithIndex index is not an accumulation', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 7 })
                        static int f(int[] a) { a.eachWithIndex { int v, int i -> if (v == i) assert true }; return 7 }
                    }''')],

        // ---------- still out ----------
        [group: 'P328 return in a .each closure', name: 'an accumulating .each with a return still skips loudly', expect: 'needs an @Invariant to frame it',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int s = 0
                            a.each { int x ->
                                if (x < 0) return
                                s = s + x
                            }
                            return s
                        }
                    }''')],
        [group: 'P328 return in a .each closure', name: 'a return that evaluates an expression skips loudly', expect: 'it is modelled as one only as a bare',
         src: tc('''class C {
                        @Requires({ a != null })
                        static void f(int[] a) {
                            a.each { int x ->
                                if (x < 0) return x + 1
                                assert x >= 0
                            }
                        }
                    }''')],
    ]
}
