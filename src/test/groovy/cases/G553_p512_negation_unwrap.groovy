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
 * 'P512 negation unwrap' — a {@code NotExpression} IS-A {@code BooleanExpression}, and five more walks unwrapped one
 * as a plain wrapper (Phase 511 fixed {@code splitConjuncts}), so a negated condition was read as its operand:
 * a precondition's or an if's dereferences ({@code !(a.size() > 0 && b.size() > 0)} taken as dereferencing
 * {@code b}, which it needn't), a range's direction ({@code !(1 <= i) && (1..i).every …} taken as ascending), an
 * element bound ({@code a.every { !(it > 5) }} taken as {@code > 5} for a sum), a channel loop's total
 * ({@code while (!(m > j))}), and the element note on a refuted invariant.
 */
class G553_p512_negation_unwrap {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 512: a negated condition is read as negated wherever a walk unwraps one: a precondition's or an if's dereferences, a range's direction, an element bound, a channel loop's total, an invariant's element note."

    static String pair(String requires, String serverGuard, String serverInv) { G325_p261_finite_cycles.pair(requires, serverGuard, serverInv) }

    static final List<Map> CASES = [
        [group: "P512 negation unwrap", name: "pre deref under a negated and", expect: ['Possible NullPointerException', 'fails on: f([], null)'],
         src: tc('''class C {
                        @Requires({ a != null && !(a.size() > 0 && b.size() > 0) })
                        static int f(List<Integer> a, List<Integer> b) { b.size() }
                    }''')],
        [group: "P512 negation unwrap", name: "if deref under a negated and", expect: ['Possible NullPointerException', 'fails on: f([], null)'],
         src: tc('''class C {
                        @Requires({ a != null && (a.isEmpty() || b != null) })
                        static int f(List<Integer> a, List<Integer> b) { if (!(a.size() > 0 && b.size() > 0)) return b.size(); 0 }
                    }''')],
        [group: "P512 negation unwrap", name: "loop pre deref under a negated and", expect: ['Possible NullPointerException'],
         src: tc('''class C {
                        @Requires({ xs != null && a != null && !(a.size() > 0 && b.size() > 0) })
                        static int f(List<Integer> xs, List<Integer> a, List<Integer> b) { int t = 0; for (x in xs) { t += b.size() }; t }
                    }''')],
        [group: "P512 negation unwrap", name: "pre doubly negated or", expect: ['Possible NullPointerException', 'fails on: f([], null)'],
         src: tc('''class C {
                        @Requires({ a != null && !(!(a.isEmpty() || b.isEmpty())) })
                        static int f(List<Integer> a, List<Integer> b) { b.size() }
                    }''')],
        [group: "P512 negation unwrap", name: "pre negated or, both derefed", ok: true,
         src: tc('''class C {
                        @Requires({ !(a.isEmpty() || b.isEmpty()) })
                        static int f(List<Integer> a, List<Integer> b) { a.size() + b.size() }
                    }''')],
        [group: "P512 negation unwrap", name: "range under a negated lower bound", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        @Ensures({ result == (!(1 <= i) && (1..i).every { it > 5 }) })
                        static boolean f(int i) { i < 1 }
                    }''')],
        [group: "P512 negation unwrap", name: "element bound negated, int array", expect: ['Cannot prove postcondition'],
         src: tc('''class C {
                        @Requires({ a != null && a.length == 2 && a.every { !(it > 5) } })
                        @Ensures({ result > 10 })
                        static int f(int[] a) { a.sum() }
                    }''')],
        [group: "P512 negation unwrap", name: "channel guard negated", expect: ['element count is not static'],
         src: tc(pair('@Requires({ n == m && n >= 0 })', '!(m > j)', '0 <= j && j <= m'))],
        [group: "P512 negation unwrap", name: "invariant every negated, no element note", expect: ['loop invariant'], refute: 'the spec requires',
         src: tc('''class T {
                        @Requires({ n >= 1 })
                        static int[] fill(int n) {
                            int[] a = new int[n + 2]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && a.length == n + 2 && !(0..i).every { int k -> a[k] == 5 } })
                            @Decreases({ n - i })
                            while (i < n) { a[i] = 5; a[i + 1] = 5; i = i + 1 }
                            return a
                        }
                    }''')],
        [group: "P512 negation unwrap", name: "invariant element comparison negated, no element note", expect: ['loop invariant'], refute: 'the spec requires',
         src: tc('''class T {
                        @Requires({ n >= 1 })
                        static int[] fill(int n) {
                            int[] a = new int[n + 2]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && a.length == n + 2 && (0..i).every { int k -> !(a[k] == 7) } })
                            @Decreases({ n - i })
                            while (i < n) { a[i] = 7; i = i + 1 }
                            return a
                        }
                    }''')],
        [group: "P512 negation unwrap", name: "a negated call, derefed", ok: true,
         src: tc('''class C {
                        @Requires({ !a.isEmpty() })
                        static int f(List<Integer> a) { a.size() }
                    }''')],
        [group: "P512 negation unwrap", name: "an else branch's deref", expect: ['Possible NullPointerException', 'fails on: f([], null)'],
         src: tc('''class C {
                        @Requires({ a != null && (a.isEmpty() || b != null) })
                        static int f(List<Integer> a, List<Integer> b) { if (a.size() > 0 && b.size() > 0) return 0; b.size() }
                    }''')],
        [group: "P512 negation unwrap", name: "a range under a lower bound", ok: true,
         src: tc('''class C {
                        @Ensures({ result == (1 <= i && (1..i).every { it > 0 }) })
                        static boolean f(int i) { 1 <= i }
                    }''')],
        [group: "P512 negation unwrap", name: "an element bound", ok: true,
         src: tc('''class C {
                        @Requires({ a != null && a.length == 2 && a.every { it > 5 } })
                        @Ensures({ result > 10 })
                        static int f(int[] a) { a.sum() }
                    }''')],
    ]
}
