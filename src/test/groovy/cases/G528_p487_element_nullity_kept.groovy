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
 * 'P487 element nullity kept' — where a list's or an array's element nullity flags (Phase 445) were fresh though the
 * value can't be null, ahead of checking a boxed element's unboxing (Phase 488): a primitive's value
 * ({@code xs.add(v)} with an int {@code v}, {@code a[0] = h(n)} with an int {@code h}), a number's arithmetic
 * ({@code out.add(2 * n)}; a null operand throws instead), a range's elements, and a {@code findAll}'s, which are its
 * source's; and an element equal to a number literal ({@code xs[0] == 4}; {@code null == 4} is false), as Phase 445
 * has a String element equal to a String literal. Each was a false alarm on a dereference of the element. And a failing call's list or array shows a null
 * element as {@code null}, not the value the model gave it ({@code f([4])} for {@code f([null])}).
 */
class G528_p487_element_nullity_kept {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 487: a list's element isn't taken as possibly null where it can't be — a primitive's value or a number's arithmetic added or stored, a range's element, a findAll's element of a source without nulls, an element equal to a number literal."

    static final List<Map> CASES = [

        // ---------- a primitive's value ----------
        [group: 'P487 element nullity kept', name: 'a primitive added', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 0 })
                        static int f(List<Integer> xs, int v) { xs.add(v); xs[0].intValue() }
                    }''')],
        [group: 'P487 element nullity kept', name: '… a boxed one', expect: ['Cannot invoke method intValue() on null object', 'obligation: xs[0] != null', 'fails on: f([], null)'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 0 })
                        static int f(List<Integer> xs, Integer v) { xs.add(v); xs[0].intValue() }
                    }''')],
        [group: 'P487 element nullity kept', name: "a primitive call's value stored", ok: true,
         src: tc('''class A {
                        static int f(int n) { List<Integer> a = [0, 0]; a[0] = h(n); a[0].intValue() }
                        static int h(int i) { i }
                    }''')],
        [group: 'P487 element nullity kept', name: "… a boxed call's", expect: ['Cannot invoke method intValue() on null object', 'obligation: a[0] != null', 'fails on: f(0)'],
         src: tc('''class A {
                        static int f(int n) { List<Integer> a = [0, 0]; a[0] = h(n); a[0].intValue() }
                        static Integer h(int i) { i > 0 ? i : null }
                    }''')],

        [group: 'P487 element nullity kept', name: "a number's arithmetic", ok: true,
         src: tc('''class A {
                        static int f(int n) { List<Integer> out = []; out.add(2 * n + 1); out[0].intValue() }
                    }''')],
        [group: 'P487 element nullity kept', name: "… a boxed element's", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != null })
                        static int f(List<Integer> xs) { List<Integer> out = []; out.add(-xs[0]); out[0].intValue() }
                    }''')],

        // ---------- what a list holds ----------
        [group: 'P487 element nullity kept', name: "a range's elements", ok: true,
         src: tc('''class A {
                        static int f() { List<Integer> r = (0<..3).toList(); r[0].intValue() }
                    }''')],
        [group: 'P487 element nullity kept', name: "a findAll's of a source with nulls", expect: ['Cannot invoke method intValue() on null object', 'obligation: ps[0] != null', 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() < 2 })
                        static int f(List<Integer> xs) {
                            List<Integer> ps = xs.findAll { it != 3 }
                            if (ps.size() == 0) return 0
                            ps[0].intValue()
                        }
                    }''')],
        [group: 'P487 element nullity kept', name: "… without", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.every { it != null } })
                        static int f(List<Integer> xs) {
                            List<Integer> ps = xs.findAll { it != 3 }
                            if (ps.size() == 0) return 0
                            ps[0].intValue()
                        }
                    }''')],

        // ---------- a number literal's equality ----------
        [group: 'P487 element nullity kept', name: "an element equal to a number literal", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] == 4 })
                        static int f(List<Integer> xs) { xs[0].intValue() }
                    }''')],
        [group: 'P487 element nullity kept', name: "… not equal", expect: ['obligation: xs[0] != null', 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs[0] != 4 })
                        static int f(List<Integer> xs) { xs[0].intValue() }
                    }''')],

        // ---------- a repro's null element ----------
        [group: 'P487 element nullity kept', name: "a repro's null element beside a value", expect: ['obligation: xs[0] != null', 'fails on: f([null, 7])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[1] == 7 })
                        static int f(List<Integer> xs) { xs[0].intValue() }
                    }''')],
        [group: 'P487 element nullity kept', name: "… an Integer[]'s", expect: ['obligation: a[0] != null', 'fails on: f([null, 7] as Integer[])'],
         src: tc('''class A {
                        @Requires({ a != null && a.length == 2 && a[1] == 7 })
                        static int f(Integer[] a) { a[0].intValue() }
                    }''')],

        // ---------- unchanged ----------
        [group: 'P487 element nullity kept', name: "an int[]'s comparison", ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 && a[0] < 3 })
                        @Ensures({ result < 3 })
                        static int f(int[] a) { a[0] }
                    }''')],
        [group: 'P487 element nullity kept', name: "a parameter's element", expect: ['Cannot invoke method intValue() on null object', 'obligation: xs[0] != null', 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { xs[0].intValue() }
                    }''')],
    ]
}
