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
 * 'P410 obligations as written' — found drafting the blog post's refresh. An overflow or divisor obligation brackets its
 * operand, but the AST's text already brackets an operation and a negation's operand, so Bloch's midpoint read
 * `Integer.MIN_VALUE <= ((low + high)) && ((low + high)) <= Integer.MAX_VALUE`, `-n` read `(-(n))` and a divisor `x`
 * read `(x) != 0` — not what the README, the tour or the blog quoted (none of those quotes was pinned to its case).
 * An operand is bracketed now only when it doesn't read as one already, and the quotes are pinned.
 */
class G452_p410_obligations_as_written {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 410: an overflow or divisor obligation shows its operand as written — `(low + high)`, `-n`, `a.intdiv(b)`, `x != 0`, `a[0] != 0` — bracketed only when it doesn't read as one operand already."

    static final List<Map> CASES = [

        // Before: `Integer.MIN_VALUE <= ((low + high)) && ((low + high)) <= Integer.MAX_VALUE`
        [group: "P410 obligations as written", name: "an addition is bracketed once",
         expect: "obligation: Integer.MIN_VALUE <= (low + high) && (low + high) <= Integer.MAX_VALUE",
         src: tc('''class C {
                        @CheckOverflow
                        @Requires({ 0 <= low && low <= high })
                        static int mid(int low, int high) { (low + high).intdiv(2) }
                    }''')],

        // Before: `(-(n))`, and `(-((a + b)))`
        [group: "P410 obligations as written", name: "a negation reads as written",
         expect: "obligation: Integer.MIN_VALUE <= -n && -n <= Integer.MAX_VALUE",
         src: tc('''class C {
                        @CheckOverflow
                        static int abs(int n) { n < 0 ? -n : n }
                    }''')],

        [group: "P410 obligations as written", name: "… and so does a negated sum",
         expect: ["obligation: Integer.MIN_VALUE <= -(a + b) && -(a + b) <= Integer.MAX_VALUE",
                  "obligation: Integer.MIN_VALUE <= (a + b) && (a + b) <= Integer.MAX_VALUE"],
         src: tc('''class C {
                        @CheckOverflow
                        static int f(int a, int b) { -(a + b) }
                    }''')],

        // Before: `!((a.intdiv(b)) is Integer.MIN_VALUE / -1)`
        [group: "P410 obligations as written", name: "a call is one operand",
         expect: "obligation: !(a.intdiv(b) is Integer.MIN_VALUE / -1)",
         src: tc('''class C {
                        @CheckOverflow
                        static int f(int a, int b) { b == 0 ? 0 : a.intdiv(b) }
                    }''')],

        // Before: `(x) != 0`, `((y - 1)) != 0`, `(a[0]) != 0`
        [group: "P410 obligations as written", name: "divisors: a name, an expression, an element",
         expect: ["obligation: x != 0", "obligation: (y - 1) != 0", "obligation: a[0] != 0"],
         src: tc('''class C {
                        static int f(int x, int y, int[] a) { 10 % x + 10 % (y - 1) + 10 % a[0] }
                    }''')],
    ]
}
