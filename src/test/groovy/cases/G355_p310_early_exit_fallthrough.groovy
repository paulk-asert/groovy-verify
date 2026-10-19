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

/** 'P310 early exits and the fall-through path' — what the path that leaves a loop normally may assume about the
 *  loop's early exits. Shared import header and wrappers come from {@link CaseDsl}. */
class G355_p310_early_exit_fallthrough {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The path that leaves a loop normally no longer assumes an early-return guard was false in the post-loop state — a guard over the counter or a zero-iteration loop refutes — and a `return` inside a `.each` closure (which only ends that element) skips loudly instead of being read as a method return.'

    static final List<Map> CASES = [
        // ---------- Phase 310: early exits and the fall-through path ----------
        // On the natural post-loop path, checkUse assumed every early-return guard FALSE in the state AFTER the
        // loop. An in-body guard ran against earlier iterations' values: `if (i == 3) return 0` never sees i == 3
        // when n == 3 (the loop stops first), so assuming i != 3 at exit ruled out f(3), which returns 3.
        [group: 'P310 early exits and the fall-through path', name: 'in-body guard over the counter does not hold at exit',
         expect: 'fails on: f(3)',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result != 3 })
                        static int f(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                if (i == 3) return 0
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // A zero-iteration loop never evaluates its in-body guard at all, even one over a parameter.
        [group: 'P310 early exits and the fall-through path', name: 'zero-iteration loop never evaluates its in-body guard',
         expect: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f(int m, int n) {
                            int i = 0
                            @Invariant({ 0 <= i && (m < 0 || i <= m) })
                            @Decreases({ m - i })
                            while (i < m) {
                                if (n == 0) return 2
                                i = i + 1
                            }
                            return n == 0 ? 5 : 2
                        }
                    }''')],
        // A PREFIX guard on a value nothing later changes still carries: past `if (n == 0) return 2`, n != 0.
        [group: 'P310 early exits and the fall-through path', name: 'prefix guard on an unchanged parameter still carries', ok: true,
         src: tc('''class C {
                        @Requires({ m >= 0 })
                        @Ensures({ result == 2 })
                        static int f(int m, int n) {
                            if (n == 0) return 2
                            int i = 0
                            @Invariant({ 0 <= i && i <= m })
                            @Decreases({ m - i })
                            while (i < m) { i = i + 1 }
                            return n == 0 ? 5 : 2
                        }
                    }''')],
        // ...but not one the loop changes: assuming j != 0 after a loop that drives j to 0 made the fall-through path
        // contradictory, so ANY postcondition "proved" there. f(1) returns 5.
        [group: 'P310 early exits and the fall-through path', name: 'prefix guard on a variable the loop changes does not carry',
         expect: 'fails on: f(1)',
         src: tc('''class C {
                        @Requires({ k >= 0 })
                        @Ensures({ result == 2 })
                        static int f(int k) {
                            int j = k
                            if (j == 0) return 2
                            @Invariant({ j >= 0 })
                            @Decreases({ j })
                            while (j > 0) { j = j - 1 }
                            return j == 0 ? 5 : 2
                        }
                    }''')],
        // In a `.each` closure `return` ends only that element's call — the iteration continues — so it must not
        // be read as a method return. f(new int[0], 0) returns 5; this used to "prove" result == 2.
        [group: 'P310 early exits and the fall-through path', name: 'return inside a .each closure is not a method return',
         expect: 'acts like `continue`',
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f(int[] a, int n) { a.each { if (n == 0) return 2 }; return n == 0 ? 5 : 2 }
                    }''')],
        // The same holds for .eachWithIndex, and for a true claim (previously a spurious refute with result = 8).
        [group: 'P310 early exits and the fall-through path', name: 'return inside a .eachWithIndex closure skips loudly',
         expect: 'acts like `continue`',
         src: tc('''class C {
                        @Ensures({ result == 7 })
                        static int f(int[] a) { a.eachWithIndex { int v, int i -> if (v == i) return }; return 7 }
                    }''')],
    ]
}
