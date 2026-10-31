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
 * 'P489 an element call unboxed' — a call that returns a list's or a boxed array's element, {@code xs.first()},
 * {@code xs.head()}, {@code xs.last()}, is null when that element is, and {@code xs.max()} / {@code xs.min()} when every
 * element is or there is none (measured on Groovy 6.0.0: they skip nulls, {@code [null, 3].min()} is 3, {@code [].max()}
 * null). Unboxed, a null throws as Phase 488's element does: {@code int f() { xs.first() }} on {@code [null]} is a
 * {@code GroovyCastException}, {@code xs.max() + 1} on {@code [null, null]} a {@code NullPointerException}.
 */
class G530_p489_element_call_unboxed {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 489: a list's or a boxed array's element returned by `first()`, `head()` or `last()`, or an extremum by `max()` / `min()`, unboxed where it's used must not be null: `int f() { xs.first() }` on `[null]` throws, and `xs.max()` is null only when every element is (or there is none)."

    static final List<Map> CASES = [

        // ---------- an element returned ----------
        [group: 'P489 an element call unboxed', name: 'a first', expect: ["Possible GroovyCastException: xs.first() is null for a null element, and a null can't be cast to int", 'obligation: xs.first() != null', 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { xs.first() }
                    }''')],
        [group: 'P489 an element call unboxed', name: '… a head', expect: ["Possible GroovyRuntimeException: xs.head() is null for a null element", 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { 1 + xs.head() }
                    }''')],
        [group: 'P489 an element call unboxed', name: '… a last', expect: ["Possible NullPointerException: xs.last() is null for a null element", 'fails on: f([0, null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 && xs[0] != null })
                        static int f(List<Integer> xs) { xs.last() * 2 }
                    }''')],
        [group: 'P489 an element call unboxed', name: "… an Integer[]'s", expect: ["Possible NullPointerException: a.first() is null for a null element", 'fails on: f(new Integer[1])'],
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        static int f(Integer[] a) { a.first() + 1 }
                    }''')],
        [group: 'P489 an element call unboxed', name: 'an element stated non-null', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 && xs.every { it != null } })
                        static int f(List<Integer> xs) { xs.first() + xs.last() }
                    }''')],
        [group: 'P489 an element call unboxed', name: '… the one it reads', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 1 && xs[xs.size() - 1] != null })
                        static int f(List<Integer> xs) { xs.last() + 1 }
                    }''')],
        [group: 'P489 an element call unboxed', name: "an int[]'s", ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.length > 0 })
                        static int f(int[] a) { a.first() + 1 }
                    }''')],
        [group: 'P489 an element call unboxed', name: 'a boxed result', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static Integer f(List<Integer> xs) { xs.first() }
                    }''')],

        // ---------- an extremum ----------
        [group: 'P489 an element call unboxed', name: 'a max', expect: ["Possible NullPointerException: xs.max() is null when every element is (or there is none), and a null operand throws", 'obligation: xs.max() != null', 'fails on: f([null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) { xs.max() + 1 }
                    }''')],
        [group: 'P489 an element call unboxed', name: "… a min's", expect: ["Possible GroovyCastException: xs.min() is null when every element is (or there is none)", 'fails on: f([null, null])'],
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() == 2 })
                        static int f(List<Integer> xs) { xs.min() }
                    }''')],
        [group: 'P489 an element call unboxed', name: '… one element not null', ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 1 && xs[1] != null })
                        static int f(List<Integer> xs) { xs.min() - xs.max() }
                    }''')],
    ]
}
