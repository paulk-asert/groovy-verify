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
 * 'P370 a spec's @ThrowsIf is an obligation' — a registry spec's @ThrowsIf arm was only a survival fact (Phase 222):
 * past the call, its condition is false. So `Math.floorDiv(x, y)` drew no diagnostic where `x.intdiv(y)` did, and
 * `floorDiv(x, 0)`, which always throws, drew none either. Each arm is now an obligation at the call, discharged as a
 * division's is: by @Requires, a guard, or a handler covering its exception. A call whose throw is its purpose
 * (`requireNonNull`, `checkIndex`, the `*Exact` family) is a deliberate throw, as a `throw` statement is. And the
 * method's own @ThrowsIf: a woven guard runs at entry, so its condition is false in the body, and a declared throw is
 * the method's contract.
 */
class G414_p370_spec_throws {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 370: a registry spec\'s @ThrowsIf is an obligation at the call (Math.floorDiv(x, y) throws when y == 0, Collections.max(xs) when xs.isEmpty(), nCopies when n < 0), discharged by @Requires, guards and covering handlers; deliberate throwers (requireNonNull, checkIndex, *Exact) are exempt; a method\'s own woven @ThrowsIf guard is an entry fact, and a declared throw is its contract.'

    static final List<Map> CASES = [

        // Before: compiled cleanly — a spec's arm was only assumed false after the call.
        [group: "P370 spec throws", name: "floorDiv by a possibly-zero divisor",
         expect: ["Possible ArithmeticException: Math.floorDiv(x, y) throws when y == 0", "obligation: !(y == 0)"],
         src: tc('''class A {
                        static int f(int x, int y) { Math.floorDiv(x, y) }
                    }''')],

        // Before: compiled cleanly — a call that always throws.
        [group: "P370 spec throws", name: "floorDiv by zero always throws",
         expect: "Possible ArithmeticException: Math.floorDiv(x, 0) throws when 0 == 0",
         src: tc('''class A {
                        static int f(int x) { Math.floorDiv(x, 0) }
                    }''')],

        [group: "P370 spec throws", name: "a precondition discharges it", ok: true,
         src: tc('''class A {
                        @Requires({ y > 0 })
                        @Ensures({ result >= 0 && result < y })
                        static int f(int x, int y) { Math.floorMod(x, y) }
                    }''')],

        [group: "P370 spec throws", name: "a guard discharges it", ok: true,
         src: tc('''class A {
                        static int f(int x, int y) {
                            if (y == 0) return 0
                            Math.floorMod(x, y)
                        }
                    }''')],

        [group: "P370 spec throws", name: "a handler of the exception covers it", ok: true,
         src: tc('''class A {
                        static int f(int x, int y) {
                            try { return Math.floorDiv(x, y) } catch (ArithmeticException e) { return 0 }
                        }
                    }''')],

        // Before: compiled cleanly. A supertype handler covers it; an unrelated one doesn't.
        [group: "P370 spec throws", name: "max of a possibly-empty collection",
         expect: ["Possible NoSuchElementException: Collections.max(xs) throws when xs.isEmpty()", "fails on: f([])"],
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            try { return (int) Collections.max(xs) } catch (NullPointerException e) { return 0 }
                        }
                    }''')],

        [group: "P370 spec throws", name: "max under a RuntimeException handler", ok: true,
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            try { return (int) Collections.max(xs) } catch (RuntimeException e) { return 0 }
                        }
                    }''')],

        [group: "P370 spec throws", name: "max of a non-empty collection", ok: true,
         src: tc('''class A {
                        @Requires({ !xs.isEmpty() })
                        static Object f(List<Integer> xs) { Collections.max(xs) }
                    }''')],

        // Before: compiled cleanly. The call is shown as written, its string argument quoted.
        [group: "P370 spec throws", name: "nCopies of a possibly-negative count",
         expect: "Possible IllegalArgumentException: Collections.nCopies(n, 'a') throws when n < 0",
         src: tc('''class A {
                        static int f(int n) { Collections.nCopies(n, 'a').size() }
                    }''')],

        [group: "P370 spec throws", name: "a deliberate thrower carries no obligation", ok: true,
         src: tc('''class A {
                        @Ensures({ result != null })
                        static Object f(Object o) { Objects.requireNonNull(o) }
                        static int g(int a, int b) { Math.addExact(a, b) }
                        static int h(int i, int n) { Objects.checkIndex(i, n) }
                    }''')],

        [group: "P370 spec throws", name: "a declared throw is the method's contract", ok: true,
         src: tc('''class A {
                        @ThrowsIf(value = { y == 0 }, exception = ArithmeticException, woven = false, direct = false)
                        static int f(int x, int y) { Math.floorDiv(x, y) }
                    }''')],

        [group: "P370 spec throws", name: "a declared throw of another exception is not",
         expect: "Possible ArithmeticException: Math.floorDiv(x, y) throws when y == 0",
         src: tc('''class A {
                        @ThrowsIf(value = { y == 0 }, exception = IllegalStateException, woven = false, direct = false)
                        static int f(int x, int y) { Math.floorDiv(x, y) }
                    }''')],

        // Before: `Possible ArithmeticException: Division by zero` — the woven guard throws first, at entry.
        [group: "P370 spec throws", name: "a woven guard is an entry fact", ok: true,
         src: tc('''class A {
                        @ThrowsIf(value = { y == 0 }, exception = IllegalArgumentException)
                        static int f(int x, int y) { return x % y }
                    }''')],

        [group: "P370 spec throws", name: "in a loop body, under the invariant", ok: true,
         src: tc('''class A {
                        @Requires({ y != 0 && n >= 0 })
                        static int f(int n, int y) {
                            int s = 0
                            for (int i = 0; i < n; i++) { s = Math.floorMod(i, y) }
                            s
                        }
                    }''')],
    ]
}
