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

/** 'P47i reverse' — 10 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G089_p47i_reverse {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Literal String.reverse folds and a palindrome reverses to itself; a wrong reversal refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 47i: String.reverse() (algebraic, literal-pinning) ----------
        // Literal pinning at mint: "abc".reverse() folds to "cba".
        [group: 'P47i reverse', name: 'literal reverse folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "cba" })
                        static String f() { "abc".reverse() }
                    }''')],
        // Palindrome reverses to itself.
        [group: 'P47i reverse', name: 'palindrome reverses to itself', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "racecar" })
                        static String f() { "racecar".reverse() }
                    }''')],
        // Wrong reversal refutes.
        [group: 'P47i reverse', name: 'wrong reversal refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == "abc" })
                        static String f() { "abc".reverse() }
                    }''')],
        // Literal involution: reverse(reverse("abc")) == "abc" — falls out of bidirectional pinning.
        [group: 'P47i reverse', name: 'literal involution reverse(reverse(x))==x', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "abc" })
                        static String f() { "abc".reverse().reverse() }
                    }''')],
        // Chains with case folding: reverse pins "cba", then toUpperCase's ensure-fn retroactively
        // case-pins "cba" -> "CBA"; congruence (reverse("abc")=="cba") composes the two.
        [group: 'P47i reverse', name: 'reverse composes with toUpperCase', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "CBA" })
                        static String f() { "abc".reverse().toUpperCase() }
                    }''')],
        // Order-independent: whichever ensure-fn runs second retroactively pins what the first minted,
        // so toUpperCase-then-reverse folds to the same "CBA" ("ABC" reverse-pins to "CBA").
        [group: 'P47i reverse', name: 'toUpperCase composes with reverse (other order)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "CBA" })
                        static String f() { "abc".toUpperCase().reverse() }
                    }''')],
        // Literal length-preservation: a theory consequence of the pinned reversed literal.
        [group: 'P47i reverse', name: 'literal reverse preserves length', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 5 })
                        static int f() { "hello".reverse().length() }
                    }''')],
        // Reflexive: reverse applied to the same symbolic arg is syntactically identical, so equality
        // holds without any axiom (the two terms are the same Z3 expression).
        [group: 'P47i reverse', name: 'reverse(s) == reverse(s) reflexive', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == 1 })
                        static int f(String s) { s.reverse() == s.reverse() ? 1 : 0 }
                    }''')],
        // PROBE (symbolic, NOT reachable without universals — documents the boundary): symbolic
        // involution `s.reverse().reverse() == s` has no per-literal pin to lean on, so it does not
        // prove — the slice skips/soft-fails rather than asserting the universal Z3 can't model.
        // BOUNDARY (symbolic, NOT reachable — documents the limit confirmed by probe): symbolic
        // involution `s.reverse().reverse() == s` has no per-literal pin to lean on. The universal
        // that would prove it poisons the refute direction (Phase 47g / probe), so it's omitted and
        // this soft-fails cleanly rather than stalling the solver.
        [group: 'P47i reverse', name: 'symbolic involution does NOT prove (boundary)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s })
                        static String f(String s) { s.reverse().reverse() }
                    }''')],
        // BOUNDARY (symbolic length): `s.reverse().length() == s.length()` likewise needs the
        // length-preservation universal, omitted for the same reason — does not prove.
        [group: 'P47i reverse', name: 'symbolic length-preservation does NOT prove (boundary)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s.length() })
                        static int f(String s) { s.reverse().length() }
                    }''')],
    ]
}
