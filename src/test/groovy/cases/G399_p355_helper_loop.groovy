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
 * 'P355 a loop in a helper' — Phases 353/354 folded a contract-free helper's straight-line body into its defining
 * expression; a loop still left the call an uninterpreted function. A loop with an @Invariant and a proven variant is
 * now summarised by its exit state: each variable it writes becomes a fresh name, and its invariants and negated
 * guard over those names are asserted with the call's definition, guarded by the path condition that reaches the loop.
 * The helper's own loop verification is what makes that sound (it runs for every method, contracted or not); a loop
 * that breaks, returns, mutates anything but plain variables, or has no variant keeps the call opaque.
 */
class G399_p355_helper_loop {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 355 a loop in a helper: a contract-free helper whose loop carries an @Invariant and a proven variant (an explicit @Decreases or a range for-in) is summarised by its exit state, fresh names for the variables it writes satisfying the invariants and the negated guard, guarded by the path to the loop; sequential loops and loops in branches compose; a loop that breaks, returns, mutates a collection or array, or has no variant leaves the call opaque. The helper loop is verified for every input, so its invariant must hold for all arguments (`hi = Math.max(x, 0)` is the idiom).'

    static final List<Map> CASES = [

        // Before: any loop left the call an uninterpreted function. Now the loop's exit state is fresh names satisfying
        // its invariant and its negated guard — sound because the helper's own loop verification proves the invariant and the
        // variant for every input (the helper has no @Requires: it would be a contracted method then).
        [group: "P355 a loop in a helper", name: "a helper's loop is summarised by its invariant at exit", ok: true,
         src: tc('''class A {
                        static int sum(int x) {
                            int s = 0
                            @Invariant({ 0 <= i && (x < 0 || i <= x) && s >= 0 })
                            @Decreases({ x - i })
                            for (int i = 0; i < x; i++) { s = s + i }
                            return s
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int k) { sum(k) }
                    }''')],
        [group: "P355 a loop in a helper", name: "… and a claim the invariant doesn't give refutes", expect: ["Cannot prove postcondition of f", "fails on: f(0)"],
         src: tc('''class A {
                        static int sum(int x) {
                            int s = 0
                            @Invariant({ 0 <= i && (x < 0 || i <= x) && s >= 0 })
                            @Decreases({ x - i })
                            for (int i = 0; i < x; i++) { s = s + i }
                            return s
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result > 0 })
                        static int f(int k) { sum(k) }
                    }''')],
        // `hi = Math.max(x, 0)` keeps the invariant true for every input, as a contract-free helper's must be.
        [group: "P355 a loop in a helper", name: "an exact invariant gives the closed form", ok: true,
         src: tc('''class A {
                        static int count(int x) {
                            int hi = Math.max(x, 0)
                            int c = 0
                            @Invariant({ 0 <= i && i <= hi && c == i })
                            @Decreases({ hi - i })
                            for (int i = 0; i < hi; i++) { c++ }
                            return c
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result == k })
                        static int f(int k) { count(k) }
                    }''')],
        [group: "P355 a loop in a helper", name: "… at a constant argument", ok: true,
         src: tc('''class A {
                        static int count(int x) {
                            int hi = Math.max(x, 0)
                            int c = 0
                            @Invariant({ 0 <= i && i <= hi && c == i })
                            @Decreases({ hi - i })
                            for (int i = 0; i < hi; i++) { c++ }
                            return c
                        }
                        @Ensures({ result == 5 })
                        static int f() { count(5) }
                    }''')],
        [group: "P355 a loop in a helper", name: "two sequential loops", ok: true,
         src: tc('''class A {
                        static int two(int x) {
                            int hi = Math.max(x, 0)
                            int c = 0
                            @Invariant({ 0 <= i && i <= hi && c == i })
                            @Decreases({ hi - i })
                            for (int i = 0; i < hi; i++) { c++ }
                            @Invariant({ 0 <= j && j <= hi && c == hi + j })
                            @Decreases({ hi - j })
                            for (int j = 0; j < hi; j++) { c++ }
                            return c
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result == 2 * k })
                        static int f(int k) { two(k) }
                    }''')],
        [group: "P355 a loop in a helper", name: "a while loop counting down", ok: true,
         src: tc('''class A {
                        static int down(int x) {
                            int n = x
                            int steps = 0
                            @Invariant({ (x < 0 ? n == x && steps == 0 : n >= 0 && steps == x - n) })
                            @Decreases({ n })
                            while (n > 0) { n--; steps++ }
                            return steps
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result == k })
                        static int f(int k) { down(k) }
                    }''')],
        [group: "P355 a loop in a helper", name: "a range for-in, its variant automatic", ok: true,
         src: tc('''class A {
                        static int count(int x) {
                            int hi = Math.max(x, 0)
                            int c = 0
                            @Invariant({ 0 <= i && i <= hi && c == i })
                            for (int i in 0..<hi) { c++ }
                            return c
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result == k })
                        static int f(int k) { count(k) }
                    }''')],
        // The loop's establishment was proven under `x > 0`, so its exit facts are guarded by it: asserted unconditionally,
        // `i == x` with `0 <= i` would contradict at x = -3 and make every claim provable.
        [group: "P355 a loop in a helper", name: "a loop in a branch: its facts hold only on that branch", ok: true,
         src: tc('''class A {
                        static int pos(int x) {
                            int c = 0
                            if (x > 0) {
                                @Invariant({ 0 <= i && i <= x && c == i })
                                @Decreases({ x - i })
                                for (int i = 0; i < x; i++) { c++ }
                            }
                            return c
                        }
                        @Ensures({ result == 0 })
                        static int f() { pos(-3) }
                    }''')],
        [group: "P355 a loop in a helper", name: "… so the other branch proves nothing extra", expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static int pos(int x) {
                            int c = 0
                            if (x > 0) {
                                @Invariant({ 0 <= i && i <= x && c == i })
                                @Decreases({ x - i })
                                for (int i = 0; i < x; i++) { c++ }
                            }
                            return c
                        }
                        @Ensures({ result == 1 })
                        static int f() { pos(-3) }
                    }''')],
        // Termination is what guarantees an exit state exists: without it, `¬guard` could contradict a variable the loop
        // doesn't write (a vacuous caller proof). The claim is true; it just isn't proved.
        [group: "P355 a loop in a helper", name: "without a variant the call stays opaque", expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static int count(int x) {
                            int c = 0
                            int i = 0
                            @Invariant({ 0 <= i && (x < 0 || i <= x) && c == i })
                            while (i < x) { c++; i++ }
                            return c
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result == k })
                        static int f(int k) { count(k) }
                    }''')],
        // A break leaves with the guard still true: the exit isn't `inv && !guard`.
        [group: "P355 a loop in a helper", name: "a loop that breaks stays opaque", expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static int firstBig(int x) {
                            int c = 0
                            @Invariant({ 0 <= i && (x < 0 || i <= x) && c >= 0 })
                            @Decreases({ x - i })
                            for (int i = 0; i < x; i++) { if (i > 3) break; c++ }
                            return c
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int k) { firstBig(k) }
                    }''')],
        // Only plain variables get fresh exit names; `l`'s contents would be read at their entry value.
        [group: "P355 a loop in a helper", name: "a loop that mutates a list stays opaque", expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        static int n(int x) {
                            List<Integer> l = []
                            @Invariant({ 0 <= i && (x < 0 || i <= x) })
                            @Decreases({ x - i })
                            for (int i = 0; i < x; i++) { l.add(i) }
                            return l.size()
                        }
                        @Requires({ k >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int k) { n(k) }
                    }''')],
        [group: "P355 a loop in a helper", name: "a wrong invariant is reported at the helper", expect: "Cannot prove loop invariant is preserved by the loop body in sum",
         src: tc('''class A {
                        static int sum(int x) {
                            int s = 0
                            @Invariant({ s == i })
                            @Decreases({ x - i })
                            for (int i = 0; i < x; i++) { s = s + i }
                            return s
                        }
                    }''')],
        [group: "P355 a loop in a helper", name: "… and so is a variant that doesn't decrease", expect: "Cannot prove loop variant decreases and stays >= 0 in count",
         src: tc('''class A {
                        static int count(int x) {
                            int hi = Math.max(x, 0)
                            int c = 0
                            @Invariant({ 0 <= i && i <= hi && c == i })
                            @Decreases({ hi + i })
                            for (int i = 0; i < hi; i++) { c++ }
                            return c
                        }
                    }''')],
        // A contract-free helper is called with any argument: `i <= x` fails on entry for a negative x.
        [group: "P355 a loop in a helper", name: "… and an invariant that fails for some input", expect: ["Cannot prove loop invariant holds on entry in count", "fails on: count(-"],
         src: tc('''class A {
                        static int count(int x) {
                            int c = 0
                            @Invariant({ 0 <= i && i <= x && c == i })
                            @Decreases({ x - i })
                            for (int i = 0; i < x; i++) { c++ }
                            return c
                        }
                    }''')],
    ]
}
