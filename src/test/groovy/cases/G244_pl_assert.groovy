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

/** 'PL-assert' — 14 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G244_pl_assert {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A bare Groovy assert is discharged at compile time: a false constant refutes, one provable from @Requires verifies.'

    static final List<Map> CASES = [

        // ----- Inline `assert` as a compile-time obligation (Dafny-style) -----
        // The motivating example: a constant-true assert compiles, a constant-false one refuses to compile.
        [group: 'PL-assert', name: 'assert: true constant verifies', ok: true,
         src: tc('''class C { static void f() { assert 2 < 3 } }''')],
        [group: 'PL-assert', name: 'assert: false constant refuted at compile time', expect: 'Assertion may not hold',
         src: tc('''class C { static void f() { assert 3 < 2 } }''')],
        // The substance: an assert over program state, proved from the @Requires.
        [group: 'PL-assert', name: 'assert: provable from @Requires verifies', ok: true,
         src: tc('''class C {
                        @Requires({ x > 5 })
                        static void f(int x) { assert x > 0 }
                    }''')],
        // …and refuted when the context doesn't justify it (counterexample x = 0). Because the assertion is over
        // a parameter, the diagnostic nudges toward @Requires (a precondition written as a runtime check).
        [group: 'PL-assert', name: 'assert: unjustified over a parameter refuted, suggests @Requires', expect: 'declare it as @Requires',
         src: tc('''class C {
                        static void f(int x) { assert x > 0 }
                    }''')],
        // An unprovable assertion *not* over a parameter (a bare local) refutes without the @Requires nudge.
        [group: 'PL-assert', name: 'assert over a local refutes without the @Requires hint', expect: 'Assertion may not hold',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        static int pick(int n) {
                            int y = n - n - 1     // y == -1
                            assert y > 0          // refuted; y is a local, not a parameter → no @Requires hint
                            return y
                        }
                    }''')],
        // Proved from a preceding assignment (value-flow), not just a guard.
        [group: 'PL-assert', name: 'assert: provable from a preceding assignment verifies', ok: true,
         src: tc('''class C {
                        static void f() { int y = 7; assert y > 0 }
                    }''')],
        // An assert provable from the @Requires sits alongside a verified array access — both checked, clean.
        // (A sound assert must itself be provable; an `assert i < a.length` with an unconstrained `i` correctly
        // refutes, exactly as Dafny would.)
        [group: 'PL-assert', name: 'assert provable from @Requires, beside a verified array access', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && i >= 0 && i < a.length })
                        static int f(int[] a, int i) { assert i < a.length; return a[i] }
                    }''')],
        // THE WART FIX: an assert in a contracted body no longer skips the @Ensures — it is now checked (and here
        // the @Ensures holds, so the method verifies cleanly with the assert present).
        [group: 'PL-assert', name: 'assert in body no longer disables the @Ensures', ok: true,
         src: tc('''class C {
                        @Requires({ x > 0 })
                        @Ensures({ result == x })
                        static int f(int x) { assert x > 0; return x }
                    }''')],
        // …and the @Ensures is genuinely checked alongside the assert: a wrong @Ensures still refutes.
        [group: 'PL-assert', name: 'assert present, wrong @Ensures still refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ x > 0 })
                        @Ensures({ result == x + 1 })
                        static int f(int x) { assert x > 0; return x }
                    }''')],
        // Step 3 — an @Ensures may now USE a proven assert (it is assumed downstream, assume/enforce).
        [group: 'PL-assert', name: 'step3: @Ensures uses a proven assert', ok: true,
         src: tc('''class C {
                        @Requires({ x >= 2 && y >= 2 })
                        @Ensures({ result >= 4 })
                        static int f(int x, int y) { assert x * y >= 4; return x * y }
                    }''')],
        // Soundness — a *false* assert is loudly reported; the @Ensures is not silently vacuously passed under it.
        [group: 'PL-assert', name: 'step3: a false assert is reported, not silently assumed', expect: 'Assertion may not hold',
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f(int x) { assert x == 5; return x }
                    }''')],
        // An assert in a body outside the value-flow fragment (here a double-assignment) is *loudly skipped*
        // rather than silently unchecked — and is not assumed in the postcondition either.
        [group: 'PL-assert', name: 'assert outside the value-flow fragment skips loudly', expect: 'Skipped assertion safety check',
         src: tc('''class C {
                        static int f() { int y = 1; assert y > 0; y = 2; return y }
                    }''')],
        // `assert false` is the unreachability idiom: it VERIFIES on a path whose conditions are contradictory
        // (genuinely dead code) — here `x > 0 ∧ x < 0`.
        [group: 'PL-assert', name: 'assert false on a contradictory (dead) path verifies', ok: true,
         src: tc('''class C {
                        @Requires({ x > 0 })
                        static void f(int x) { if (x < 0) { assert false } }
                    }''')],
        // …and REFUTES when the point is actually reachable (an AssertionError could be thrown there).
        [group: 'PL-assert', name: 'assert false on a reachable path refuted', expect: 'Assertion may not hold',
         src: tc('''class C { static void f(int x) { assert false } }''')],
    ]
}
