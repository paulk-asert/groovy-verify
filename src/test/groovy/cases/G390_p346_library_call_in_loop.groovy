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
 * 'P346 a library call in a loop body' — a registry-specced call over a local (Math.abs(i), Math.max(s, i)) was
 * untranslatable wherever the local's width was unknown, since abs(int)/abs(long) need it to pick an overload, so a
 * loop body havocked the result and refuted with a call that does not fail. Encoder.staticNumericKind now falls back
 * to integralNames (Phase 333). A value the encoder can't translate is havocked as `x (unmodelled)`, and a failing
 * call that rests on one is withheld with a note.
 */
class G390_p346_library_call_in_loop {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 346 a library call in a loop body: a registry-specced call over an int or long local (Math.abs(i), Math.max(s, i)) picks its overload from the local\'s declared width, in loop bodies, guards, after a loop and in straight-line code, so its spec is used where it had been havocked. A value the encoder cannot translate shows as x (unmodelled), and a failing call resting on one is withheld with a note.'

    static final List<Map> CASES = [

        // Math.abs(i) with i a local: abs(int) and abs(long) are both specced, and i's width came only from scalarTypes (params and fields), so the lookup declined and s was havocked: a false refutation with a call, f(1), that does not fail.
        [group: 'P346 a library call in a loop body', name: 'Math.abs in a loop body', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= x })
                        @Ensures({ result == x })
                        static int g(int x) { x }
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = s + Math.abs(i)
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P346 a library call in a loop body', name: 'its result in a body local', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= x })
                        @Ensures({ result == x })
                        static int g(int x) { x }
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                int t = Math.abs(i)
                                s = s + t
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P346 a library call in a loop body', name: 'Math.max in a loop body', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= x })
                        @Ensures({ result == x })
                        static int g(int x) { x }
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = Math.max(s, i)
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        [group: 'P346 a library call in a loop body', name: 'a library call returned after a loop', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= x })
                        @Ensures({ result == x })
                        static int g(int x) { x }
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                i = i + 1
                            }
                            return Math.abs(i)
                        }
                    }''')],
        [group: 'P346 a library call in a loop body', name: 'a library call in a loop guard', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= x })
                        @Ensures({ result == x })
                        static int g(int x) { x }
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < Math.abs(n)) {
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // The for variable is declared by the loop, not by a declaration: integralNames now notes it.
        [group: 'P346 a library call in a loop body', name: 'a library call in a range for-in', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= x })
                        @Ensures({ result == x })
                        static int g(int x) { x }
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            for (int i in 0..<n) { s = s + Math.abs(i) }
                            return s
                        }
                    }''')],
        [group: 'P346 a library call in a loop body', name: 'Math.abs over an int local in straight-line code', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int k = n + 1
                            int s = Math.abs(k)
                            return s
                        }
                    }''')],
        [group: 'P346 a library call in a loop body', name: 'a claim the spec does not give refutes', expect: ['Cannot prove loop invariant is preserved', 'fails on: f(1)'],
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s == i })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = s + Math.abs(i)
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        // Phase 346 havocked g's result here (and withheld the failing call); since Phase 347 a same-class call in a loop
        // body is framed and its @Ensures assumed, so `result == x` under `0 <= i` keeps `s >= 0`.
        [group: 'P346 a library call in a loop body', name: "a contracted call's @Ensures reaches a loop body (Phase 347)", ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= x })
                        @Ensures({ result == x })
                        static int g(int x) { x }
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = s + g(i)
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
    ]
}
