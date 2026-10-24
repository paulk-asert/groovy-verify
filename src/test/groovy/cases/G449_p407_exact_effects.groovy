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
 * 'P407 exact effects' — a contract-free callee was known only by its frame: what it may write, not what it writes, so
 * `c.bump(); return c.count` couldn't follow from `count = count + 1`, and (Phase 406) a refutation over it showed no
 * call. A simple body — straight-line code and if/else; `=`, `op=`, `++` to its own fields and locals; one element store
 * per array; a final return — is read as the @Ensures it implies: `count == old.count + 1`, an `if` as a ternary, a
 * guarded store as that store under its guard with every other element unchanged, `result == E`. Each conjunct is
 * asserted where the call's frame havocs, so the location is pinned and a witness over it is a real run. A call in the
 * body, `/` or `%`, a second store to an array, or a read of an array after its store is more than this reads.
 */
class G449_p407_exact_effects {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 407: a simple contract-free callee's body is read as the @Ensures it implies — its field writes, a guarded element store, its return value — so what follows from the call proves, and a refutation over it shows a real failing call; a written array formal's @Ensures now reaches the actual."

    static final String COUNTER = '''
                    final class Counter {
                        int count
                        int other
                        void bump() { count = count + 1 }
                        void tick() { count++; other = 5 }
                    }'''

    static final List<Map> CASES = [

        // Before: "Cannot prove" (the frame only), and since Phase 406 with no call shown
        [group: "P407 exact effects", name: "a field the callee increments",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null && c.count == 5 })
                        @Ensures({ result == 6 })
                        static int f(Counter c) {
                            c.bump()
                            return c.count
                        }
                    }''' + COUNTER)],

        [group: "P407 exact effects", name: "… a wrong claim about it refutes with a real call",
         expect: ["Cannot prove postcondition of f", "fails on: f(new Counter(count: 5))"],
         src: tc('''class A {
                        @Requires({ c != null && c.count == 5 })
                        @Ensures({ result == 7 })
                        static int f(Counter c) {
                            c.bump()
                            return c.count
                        }
                    }''' + COUNTER)],

        [group: "P407 exact effects", name: "two writes, one an increment",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null && c.count == 1 })
                        @Ensures({ result == 7 })
                        static int f(Counter c) {
                            c.tick()
                            return c.count + c.other
                        }
                    }''' + COUNTER)],

        [group: "P407 exact effects", name: "a branch is a ternary (a shadowing setter's)",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ result >= 0 })
                        static int f(C c, int x) {
                            c.setAbs(x)
                            return c.v
                        }
                    }
                    final class C {
                        int v
                        void setAbs(int v) { if (v < 0) this.v = -v else this.v = v }
                    }''')],

        [group: "P407 exact effects", name: "a guarded store into an array argument, and the elements it leaves",
         ok: true,
         src: tc('''class A {
                        static void w(int[] b) { if (b != null && b.length > 0) b[0] = 1 }
                        @Requires({ a != null && a.length > 1 && a[1] == 3 })
                        @Ensures({ result == 4 })
                        static int f(int[] a) {
                            w(a)
                            return a[0] + a[1]
                        }
                    }''')],

        [group: "P407 exact effects", name: "the value a writer returns",
         ok: true,
         src: tc('''final class C {
                        int count
                        int next() { count = count + 1; return count }
                        @Requires({ count == 2 })
                        @Ensures({ result == 3 && count == 3 })
                        int f() {
                            int s = next()
                            return s
                        }
                    }''')],

        // Unproved before: a written array formal's own @Ensures was never tied to the actual
        [group: "P407 exact effects", name: "a written array formal's @Ensures reaches the actual",
         ok: true,
         src: tc('''class A {
                        @Requires({ b != null && b.length > 0 })
                        @Ensures({ b[0] == 5 })
                        static void w(int[] b) { b[0] = 5 }
                        @Requires({ a != null && a.length > 0 })
                        @Ensures({ result == 5 })
                        static int f(int[] a) {
                            w(a)
                            return a[0]
                        }
                    }''')],

        // The boundary: a body with a call is known by its frame only, and a witness over it is withheld
        [group: "P407 exact effects", name: "a body that calls out is known by its frame only",
         expect: ["Cannot prove postcondition of f", "no failing call: the failure rests on what a call leaves in 'c.count'"],
         src: tc('''class A {
                        @Requires({ c != null && c.count == 5 })
                        @Ensures({ result == 6 })
                        static int f(Counter2 c) {
                            c.bump()
                            return c.count
                        }
                    }
                    final class Counter2 {
                        int count
                        void bump() { count = Math.addExact(count, 1) }
                    }''')],

        // … and so is one that divides (Groovy's `/` is a BigDecimal division, not the contract language's)
        [group: "P407 exact effects", name: "… and one that divides",
         expect: ["Cannot prove postcondition of f", "no failing call"],
         src: tc('''class A {
                        @Requires({ c != null && c.count == 8 })
                        @Ensures({ result == 4 })
                        static int f(Half c) {
                            c.halve()
                            return c.count
                        }
                    }
                    final class Half {
                        int count
                        void halve() { count = count / 2 }
                    }''')],

        // An overridable callee's body isn't what runs: nothing is read from it (here its class's getter is open too)
        [group: "P407 exact effects", name: "an overridable callee is read by its frame, not its body",
         expect: "'Open' can be subclassed elsewhere",
         refute: "Cannot prove postcondition",
         src: tc('''class A {
                        @Requires({ c != null && c.count == 5 })
                        @Ensures({ result == 6 })
                        static int f(Open c) {
                            c.bump()
                            return c.count
                        }
                    }
                    class Open {
                        int count
                        void bump() { count = count + 1 }
                    }''')],
    ]
}
