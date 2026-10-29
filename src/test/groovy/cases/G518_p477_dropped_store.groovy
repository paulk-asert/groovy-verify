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
 * 'P477 a store the check dropped' — two soundness holes, found probing an unknown value stored into a container.
 * A local bound to a list or array literal had its reads folded to the literal's elements (Phase 38's factory fold), and
 * only add/clear/removeLast dropped that record: after `List<Integer> a = [1, 1]; a[1] = 0`, `a[1]` still read 1, and
 * `100.intdiv(a[1])` proved. And the value-flow pass checks an if's arms on copies of the steps before it, going on
 * after the if from those: a store into an array, a field's write or a mutating call in an arm that falls through was
 * dropped there, so `a[1] = 1; if (n > 5) a[1] = 0; 100.intdiv(a[1])` proved. A literal's contents are now its array's
 * too, and a store drops the record; an arm writing past its own names sends the method to the region pass, which
 * merges both arms.
 */
class G518_p477_dropped_store {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 477 (soundness): a store into a list or array bound to a literal (`a[1] = 0`, `a.set(0, n)`) is read back — reads were folded to the literal's elements, so `[1, 1]` then `a[1] = 0` proved `100.intdiv(a[1])`; and a store, a field's write or a mutating call in an if's arm is seen after the if — the value-flow pass dropped it there."

    static final List<Map> CASES = [

        // ---------- a store into a literal-bound local: read back ----------
        [group: "P477 a store the check dropped", name: "a zero stored over a list literal's one", expect: ['Possible ArithmeticException', 'fails on: f('],
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> a = [1, 1]
                            a[1] = 0
                            return 100.intdiv(a[1])
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "… a parameter stored", expect: ['Possible ArithmeticException', 'fails on: f(0)'],
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> a = [1, 1]
                            a[1] = n
                            return 100.intdiv(a[1])
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "… by set, read by get", expect: ['Possible ArithmeticException', 'fails on: f(0)'],
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> a = [1]
                            a.set(0, n)
                            return 100.intdiv(a.get(0))
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "… an array literal", expect: ['Possible ArithmeticException', 'fails on: f(0)'],
         src: tc('''class A {
                        static int f(int n) {
                            int[] a = [1, 1] as int[]
                            a[1] = n
                            return 100.intdiv(a[1])
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "another slot keeps the literal's value", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            int[] a = [1, 1] as int[]
                            a[1] = n
                            return 100.intdiv(a[0])
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "a literal unwritten still folds", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> a = [1, 2]
                            return 100.intdiv(a[1]) + a.size()
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "a helper's unknown value in another slot", expect: ['Possible ArithmeticException', 'fails on: f(0)'],
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> a = [0, 0]
                            a[0] = h(n)
                            a[1] = n
                            return 100.intdiv(a[1])
                        }
                        static int h(int i) { new Random().nextInt() }
                    }''')],

        [group: "P477 a store the check dropped", name: "… in the slot read", expect: ['Possible ArithmeticException', 'what h(…) returns'], refute: 'fails on',
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> a = [0, 0]
                            a[1] = n
                            a[0] = h(n)
                            return 100.intdiv(a[0])
                        }
                        static int h(int i) { new Random().nextInt() }
                    }''')],

        // ---------- a write in an if's arm: seen after the if ----------
        [group: "P477 a store the check dropped", name: "an array store in an arm", expect: ['Possible ArithmeticException', 'fails on: f(6)'],
         src: tc('''class A {
                        static int f(int n) {
                            int[] a = new int[2]
                            a[1] = 1
                            if (n > 5) { a[1] = 0 } else { a[0] = 0 }
                            return 100.intdiv(a[1])
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "… into a list literal", expect: ['Possible ArithmeticException', 'fails on: f(6)'],
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> a = [1, 1]
                            if (n > 5) a[1] = 0
                            return 100.intdiv(a[1])
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "a field's write in an arm", expect: ['Possible ArithmeticException', 'fails on'],
         src: tc('''class A {
                        int x
                        @Requires({ x != 0 })
                        int f(int n) {
                            if (n > 5) x = 0
                            return 100.intdiv(x)
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "a mutating call in an arm", expect: ['Possible ArithmeticException', 'fails on: f(6)'],
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> a = [1]
                            if (n > 5) a.clear()
                            return 100.intdiv(a.size())
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "… in an if nested in an arm", expect: ['Possible ArithmeticException', 'fails on: f(6)'],
         src: tc('''class A {
                        static int f(int n) {
                            int[] a = new int[2]
                            a[1] = 1
                            if (n > 0) { if (n > 5) a[1] = 0 }
                            return 100.intdiv(a[1])
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "… last in a labelled block", expect: ['Possible ArithmeticException', 'fails on: f(6)'],
         src: tc('''class A {
                        static int f(int n) {
                            int[] a = new int[2]
                            a[1] = 1
                            blk: {
                                if (n > 5) a[1] = 0
                            }
                            return 100.intdiv(a[1])
                        }
                    }''')],

        [group: "P477 a store the check dropped", name: "an arm that returns: its store is dead after", ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            int[] a = new int[2]
                            a[1] = 1
                            if (n > 5) { a[1] = 0; return 0 }
                            return 100.intdiv(a[1])
                        }
                    }''')],
    ]
}
