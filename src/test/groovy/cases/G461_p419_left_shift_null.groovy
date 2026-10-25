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
 * 'P419 left shift null' — `xs << v` on a null throws as a call on it does ("Cannot invoke method leftShift() on null
 * object", measured for a list, set, map, StringBuilder and boxed Integer, dynamic and @TypeChecked), but it had no
 * null obligation: `f(List xs) { xs << 1 }` compiled cleanly and f(null) throws. It has its receiver's obligation now,
 * and, as a call does (Phase 418), leaves the receiver non-null after it. An `int`'s `<<` is a shift: nothing.
 *
 * A local declared with a list or map literal and never reassigned is never null, as one declared with a `new` is
 * (Phase 277): the loop that appends to it with `<<` doesn't keep its prefix's facts (Phase 349 bounds `<<` only for a
 * callee's writes), so `out = []`'s non-null didn't reach the body. The names are by name, so another declaration of
 * one (`… = null` in another block) now counts as a reassignment, for `new` too.
 */
class G461_p419_left_shift_null {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 419: `xs << v` carries its receiver's null obligation (on a list, set, map, StringBuilder or boxed number — not an `int`'s shift) and leaves it non-null after; a local declared with a list or map literal and never reassigned or redeclared is never null."

    static final List<Map> CASES = [

        [group: "P419 left shift null", name: "a parameter's << may be on null",
         expect: ["Cannot invoke method leftShift() on null object", "obligation: xs != null", "fails on: f(null)"],
         src: tc('''class A {
                        static void f(List<Integer> xs) { xs << 1 }
                    }''')],

        [group: "P419 left shift null", name: "… a precondition rules it out",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static void f(List<Integer> xs) { xs << 1 }
                    }''')],

        [group: "P419 left shift null", name: "… and so does a guard",
         ok: true,
         src: tc('''class A {
                        static void f(List<Integer> xs) { if (xs != null) xs << 1 }
                    }''')],

        [group: "P419 left shift null", name: "a builder's and a map's too",
         expect: ["Cannot invoke method leftShift() on null object", "obligation: sb != null", "obligation: m != null"],
         src: tc('''class A {
                        static void f(StringBuilder sb) { sb << 'a' }
                        static void g(Map<String, Integer> m) { m << [a: 1] }
                    }''')],

        // Reported at the << only, as a call statement is (Phase 418)
        [group: "P419 left shift null", name: "the receiver is non-null after it",
         expect: ["Cannot invoke method leftShift() on null object", "fails on: f(null)"],
         refute: "size()",
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            xs << 1
                            return xs.size()
                        }
                    }''')],

        [group: "P419 left shift null", name: "… in an assignment too",
         expect: ["Cannot invoke method leftShift() on null object"],
         refute: "size()",
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            def ys = xs << 1
                            return xs.size()
                        }
                    }''')],

        [group: "P419 left shift null", name: "a local assigned null",
         expect: ["Cannot invoke method leftShift() on null object", "obligation: xs != null"],
         src: tc('''class A {
                        static void f() {
                            List<Integer> xs = null
                            xs << 1
                        }
                    }''')],

        [group: "P419 left shift null", name: "an int's << is a shift",
         ok: true,
         src: tc('''class A {
                        static int f(int n) { n << 1 }
                    }''')],

        // ── a literal local ──

        [group: "P419 left shift null", name: "a literal local appended to in a loop",
         ok: true,
         src: tc('''class A {
                        @Requires({ n >= 0 })
                        static List<Integer> f(int n) {
                            List<Integer> out = []
                            int k = 0
                            @Invariant({ 0 <= k && k <= n })
                            @Decreases({ n - k })
                            while (k < n) { out << k; k = k + 1 }
                            return out
                        }
                    }''')],

        [group: "P419 left shift null", name: "… not once it's reassigned",
         expect: ["Cannot invoke method leftShift() on null object", "fails on: f(null)", "@ line 8"],
         refute: "@ line 6",
         src: tc('''class A {
                        static void f(List<Integer> p) {
                            List<Integer> m = []
                            m << 1
                            m = p
                            m << 2
                        }
                    }''')],

        // The exemptions are by name: the other block's `sb` is null
        [group: "P419 left shift null", name: "… nor redeclared in another block",
         expect: ["Cannot invoke method append() on null object", "obligation: sb != null"],
         src: tc('''class A {
                        static void f(boolean c) {
                            if (c) {
                                StringBuilder sb = new StringBuilder()
                                sb.append('a')
                            } else {
                                StringBuilder sb = null
                                sb.append('b')
                            }
                        }
                    }''')],
    ]
}
