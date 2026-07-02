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

/** 'P105 string-seq' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G238_p105_string_seq {

    static final List<Map> CASES = [
        // ---------- P105 string-sequence: read-only per-character proofs (Slice 1) ----------
        // Read-only string iteration under a quantified loop invariant — the string analogue of the array
        // "every element satisfies P" proofs — is carried by Z3's seq theory (`seq.nth` e-matching under
        // the forall). The developer-facing spelling is `s.charAt(i)` (an int code point) compared against
        // `('a' as char)`: Groovy has no primitive char literal, so the cast is the idiomatic char, and
        // Phase 105 folds it to its code so the comparison is over code points. Each positive has a refute
        // control proving non-vacuity.
        [group: 'P105 string-seq', name: 'all-lowercase loop verifies', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ !result || Forall.range(0, s.length()) { int i -> s.charAt(i) >= ('a' as char) && s.charAt(i) <= ('z' as char) } })
                        static boolean allLower(String s) {
                            @Invariant({ 0 <= j && j <= s.length() && Forall.range(0, j) { int i -> s.charAt(i) >= ('a' as char) && s.charAt(i) <= ('z' as char) } })
                            @Decreases({ s.length() - j })
                            for (int j = 0; j < s.length(); j++) {
                                if (s.charAt(j) < ('a' as char) || s.charAt(j) > ('z' as char)) return false
                            }
                            return true
                        }
                    }''')],
        // Refute control: the loop guarantees only >= 'a', so claiming >= 'b' must refute (counterexample 'a').
        [group: 'P105 string-seq', name: 'too-strong char bound refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ !result || Forall.range(0, s.length()) { int i -> s.charAt(i) >= ('b' as char) && s.charAt(i) <= ('z' as char) } })
                        static boolean allLower(String s) {
                            @Invariant({ 0 <= j && j <= s.length() && Forall.range(0, j) { int i -> s.charAt(i) >= ('a' as char) && s.charAt(i) <= ('z' as char) } })
                            @Decreases({ s.length() - j })
                            for (int j = 0; j < s.length(); j++) {
                                if (s.charAt(j) < ('a' as char) || s.charAt(j) > ('z' as char)) return false
                            }
                            return true
                        }
                    }''')],
        // Forall-assumption instantiation at a constant index — the precondition's per-char fact fires at i==3.
        [group: 'P105 string-seq', name: 'charAt fact from forall precondition', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 5 && Forall.range(0, s.length()) { int i -> s.charAt(i) >= ('a' as char) && s.charAt(i) <= ('z' as char) } })
                        @Ensures({ result >= ('a' as char) && result <= ('z' as char) })
                        static int third(String s) { return (int) s.charAt(3) }
                    }''')],
        // Refute control: the precondition only constrains [0,3), so position 3 is unconstrained — must refute.
        [group: 'P105 string-seq', name: 'unconstrained position refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 5 && Forall.range(0, 3) { int i -> s.charAt(i) >= ('a' as char) && s.charAt(i) <= ('z' as char) } })
                        @Ensures({ result >= ('a' as char) && result <= ('z' as char) })
                        static int third(String s) { return (int) s.charAt(3) }
                    }''')],
    ]
}
