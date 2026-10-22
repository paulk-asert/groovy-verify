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
 * 'P372 closure iteration' — a site inside a closure runs when the closure is called, not where it is written: later,
 * perhaps many times, after its own writes and the method's later ones. It was checked in the state at the closure, so
 * `int d = 1; 3.times { 100.intdiv(d); d-- }` proved its divisor from `d == 1`, and the second call throws — silently,
 * for `times`, `upto`, `step`, `collect`, `findAll`, `inject`, `any`, `every`, `sum`, a map's `each`, a stored closure.
 * Every captured name that can differ by then is now havocked, and the failing call withheld. (A `.each` the verifier
 * desugars into a loop, Phase 310, already was a loop.)
 */
class G416_p372_closure_iteration {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 372: a closure body\'s obligations are checked with every captured name it may read changed (its own writes, the method\'s writes after it, an enclosing loop\'s, other closures\') havocked, not in the state where it is written; its failing call is withheld; a closure literal local is never null.'

    static final List<Map> CASES = [

        // Before: compiled cleanly — the divisor was read as d == 1. The second call divides by zero.
        [group: "P372 closure iteration", name: "a closure that writes what it reads",
         expect: ["Possible ArithmeticException: Division by zero", "d (when the closure runs) = 0",
                  "no failing call: the failure is inside a closure"], refute: "fails on",
         src: tc('''class A {
                        static int f() {
                            int s = 0
                            int d = 1
                            3.times { s = 100.intdiv(d); d-- }
                            s
                        }
                    }''')],

        // Before: compiled cleanly.
        [group: "P372 closure iteration", name: "collect with a side effect",
         expect: "Possible ArithmeticException: Division by zero",
         src: tc('''class A {
                        @Requires({ xs != null })
                        static List<Integer> f(List<Integer> xs) {
                            int d = 1
                            xs.collect { Integer x -> int q = 100.intdiv(d); d = d - 1; q }
                        }
                    }''')],

        // Before: compiled cleanly.
        [group: "P372 closure iteration", name: "inject with a side effect",
         expect: "Possible ArithmeticException: Division by zero",
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) {
                            int d = 1
                            xs.inject(0) { int acc, Integer x -> d = d - 1; acc + 100.intdiv(d + 1) }
                        }
                    }''')],

        // Before: compiled cleanly — the closure is called after d is written.
        [group: "P372 closure iteration", name: "a stored closure called after a later write",
         expect: "Possible ArithmeticException: Division by zero",
         src: tc('''class A {
                        static int f() {
                            int d = 1
                            Closure<Integer> c = { 100.intdiv(d) }
                            d = 0
                            c()
                        }
                    }''')],

        // Before: compiled cleanly — clear() empties the list before the call.
        [group: "P372 closure iteration", name: "a call after the closure that mutates what it reads",
         expect: "Possible IndexOutOfBoundsException",
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) {
                            Closure<Integer> c = { xs.get(0) }
                            xs.clear()
                            c()
                        }
                    }''')],

        // Before: a null-dereference warning on `c()` (a closure literal local, below).
        [group: "P372 closure iteration", name: "nothing written after it, nothing havocked", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null && xs.size() > 0 })
                        static int f(List<Integer> xs) {
                            Closure<Integer> c = { xs.get(0) }
                            c()
                        }
                    }''')],

        [group: "P372 closure iteration", name: "a captured value nothing writes", ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) {
                            int s = 0
                            int d = 1
                            xs.each { Integer x -> s = 100.intdiv(d) }
                            s
                        }
                    }''')],

        // Before: `fails on: f()`, which never fails — the closure's k is only 0 and 1. Phase 372 kept the warning (k was
        // free); Phase 380 bounds a `times` closure's parameter, so it proves.
        [group: "P372 closure iteration", name: "a closure parameter is bounded by its range",
         ok: true,
         src: tc('''class A {
                        static int f() {
                            int s = 0
                            2.times { int k -> s = 100.intdiv(k - 3) }
                            s
                        }
                    }''')],

        // … and where the range does reach the zero (k = 2), the warning stays, its call withheld.
        [group: "P372 closure iteration", name: "… a range that reaches it still warns, no call shown",
         expect: ["Possible ArithmeticException: Division by zero", "no failing call: the failure is inside a closure"],
         refute: "fails on",
         src: tc('''class A {
                        static int f() {
                            int s = 0
                            3.times { int k -> s = 100.intdiv(k - 2) }
                            s
                        }
                    }''')],

        // Before: `Possible NullPointerException: Cannot invoke method call() on null object`.
        [group: "P372 closure iteration", name: "a closure literal local is never null", ok: true,
         src: tc('''class A {
                        static int f() {
                            Closure<Integer> c = { 1 }
                            c()
                        }
                    }''')],

        // The `.each` desugar is a loop already (Phase 310): its call stands, from entry.
        [group: "P372 closure iteration", name: "an each loop keeps its failing call",
         expect: ["Possible ArithmeticException: Division by zero", "fails on: f([null, null])"],
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            int s = 0
                            int d = 1
                            xs.each { int x -> s = 100.intdiv(d); d = d - 1 }
                            s
                        }
                    }''')],
    ]
}
