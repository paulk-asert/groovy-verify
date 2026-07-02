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

/** 'P106 char-seq' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G237_p106_char_seq {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Building a char[] buffer char-by-char (the Int-element-array route for string construction), e.g. functional ChangeCase; a wrong-char claim refutes.'

    static final List<Map> CASES = [
        // ---------- P106 char-sequence: ChangeCase via the array theory (Slice 2) ----------
        // The spike showed string *construction*-content invariants time out on Z3's seq theory (`str.++`),
        // but the same content invariants discharge on the *array* theory. So model the char buffer as a
        // `char[]` (an Int-element array — `char` is `isIntLikeType`) and ChangeCase falls out of the existing
        // array-store + quantified-loop-invariant machinery with no new engine code beyond Phase 105's char-cast
        // fold. `('X' as char)` is the idiomatic char literal; char arithmetic is spelled `(char)((int) a[i] - 32)`
        // so it type-checks (char[] subscript arithmetic boxes to Number).
        [group: 'P106 char-seq', name: 'fill char[] with a constant char', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ (0..<a.length).every { a[it] == ('X' as char) } })
                        static char[] fillX(char[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length && (0..<i).every { a[it] == ('X' as char) } })
                            @Decreases({ a.length - i })
                            while (i < a.length) { a[i] = ('X' as char); i = i + 1 }
                            return a
                        }
                    }''')],
        // Refute control: the fill stores 'X', so claiming 'Y' must refute (counterexample any non-empty array).
        [group: 'P106 char-seq', name: 'fill wrong-char claim refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ (0..<a.length).every { a[it] == ('Y' as char) } })
                        static char[] fillX(char[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length && (0..<i).every { a[it] == ('X' as char) } })
                            @Decreases({ a.length - i })
                            while (i < a.length) { a[i] = ('X' as char); i = i + 1 }
                            return a
                        }
                    }''')],
        // Full functional ChangeCase: read `a`, build a new `r`, prove result is the upper-cased copy
        // element-by-element (no `old` needed — `a` is read-only). The OpenJML ChangeCase, via char[].
        [group: 'P106 char-seq', name: 'functional ChangeCase (upper) verifies', ok: true,
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result.length == a.length && (0..<a.length).every { result[it] == ((a[it] >= ('a' as char) && a[it] <= ('z' as char)) ? (char)((int) a[it] - 32) : a[it]) } })
                        static char[] upper(char[] a) {
                            char[] r = new char[a.length]
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length && r.length == a.length &&
                                (0..<i).every { r[it] == ((a[it] >= ('a' as char) && a[it] <= ('z' as char)) ? (char)((int) a[it] - 32) : a[it]) } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] >= ('a' as char) && a[i] <= ('z' as char)) r[i] = (char)((int) a[i] - 32)
                                else r[i] = a[i]
                                i = i + 1
                            }
                            return r
                        }
                    }''')],
        // Refute control: dropping the lowercase guard from the spec (claim *every* element is shifted -32)
        // must refute — a non-lowercase element (e.g. 'A') is copied unchanged, not shifted.
        [group: 'P106 char-seq', name: 'unconditional-shift claim refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ a != null })
                        @Ensures({ result.length == a.length && (0..<a.length).every { result[it] == (char)((int) a[it] - 32) } })
                        static char[] upper(char[] a) {
                            char[] r = new char[a.length]
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length && r.length == a.length &&
                                (0..<i).every { r[it] == ((a[it] >= ('a' as char) && a[it] <= ('z' as char)) ? (char)((int) a[it] - 32) : a[it]) } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] >= ('a' as char) && a[i] <= ('z' as char)) r[i] = (char)((int) a[i] - 32)
                                else r[i] = a[i]
                                i = i + 1
                            }
                            return r
                        }
                    }''')],
    ]
}
