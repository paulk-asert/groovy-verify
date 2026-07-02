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

/** 'P-seqconcat' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G211_p_seqconcat {

    static final List<Map> CASES = [

        // Phase 129 — a String/sequence operand reaching the integer arithmetic/comparison dispatch used to
        // throw (a ClassCastException to ArithExpr in `plus`, or a Z3 sort-mismatch in `mkEq`) and could crash
        // the whole compile. The encoder now routes `+` on two sequences to concatenation and skips loudly on a
        // lone-sequence operand, so these degrade gracefully (prove / refute / loud-skip) — never crash.
        [group: 'P-seqconcat', name: 'straight-line local string concat proves', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 'ax' })
                        static String f() { String acc = 'a'; acc = acc + 'x'; return acc } }''')],
        [group: 'P-seqconcat', name: 'combiner inline (string params) in postcondition proves', ok: true,
         src: tc('''class C {
                        @Ensures({ result == a + b })
                        static String glue(String a, String b) { a + b }
                        @Ensures({ glue(s, t) == s + t })
                        static void check(String s, String t) { } }''')],
        [group: 'P-seqconcat', name: 'string combiner call in return position skips (no crash)', expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == a + b })
                        static String glue(String a, String b) { a + b }
                        @Ensures({ result == s + t })
                        static String join2(String s, String t) { return glue(s, t) } }''')],
        [group: 'P-seqconcat', name: 'string accumulator folded in while loop refutes cleanly (no crash)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == a + b })
                        static String glue(String a, String b) { a + b }
                        @Ensures({ result != null })
                        static String fold(String[] parts) {
                            String acc = ''
                            int i = 0
                            @Invariant({ 0 <= i && i <= parts.length })
                            @Decreases({ parts.length - i })
                            while (i < parts.length) { acc = glue(acc, parts[i]); i = i + 1 }
                            return acc } }''')],

        // Phase 130 — combiner inlining lost a String formal's binding when the formal's name collided with a
        // surrounding String variable (the env/sortedEnv split); `varForOfSort` now honours the env binding first.
        [group: 'P-seqconcat', name: 'combiner-inline identity with colliding param name proves', ok: true,
         src: tc('''class C {
                        @Ensures({ result == a + b })
                        static String glue(String a, String b) { a + b }
                        @Ensures({ glue(a, '') == a && glue('', a) == a })
                        static void id(String a) { } }''')],
    ]
}
