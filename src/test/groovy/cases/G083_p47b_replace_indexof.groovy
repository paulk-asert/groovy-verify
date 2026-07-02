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

/** 'P47b replace/indexOf' — 9 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G083_p47b_replace_indexof {

    static final List<Map> CASES = [

        // ---------- Phase 47b: replace + indexOf ----------
        // Literal replace folds via the *real* Groovy method — `replace` is replace-ALL, so both
        // 'l's go: "hello".replace("l","P") == "hePPo" (NOT the first-occurrence "hePlo"; that's
        // `replaceFirst`, below). Claiming "hePlo" now refutes — the Phase-47b soundness fix.
        [group: 'P47b replace/indexOf', name: 'literal replace folds (replace-all, both occurrences)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "hePPo" })
                        static String f() { "hello".replace("l", "P") }
                    }''')],
        [group: 'P47b replace/indexOf', name: 'replace-all over first-occurrence refutes (was the unsound case)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == "hePlo" })
                        static String f() { "hello".replace("l", "P") }
                    }''')],
        // replaceFirst IS first-occurrence (regex, here a plain-literal pattern) — only the first 'l'.
        [group: 'P47b replace/indexOf', name: 'literal replaceFirst folds (first occurrence only)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "hePlo" })
                        static String f() { "hello".replaceFirst("l", "P") }
                    }''')],
        // Symbolic replaceFirst with a plain-literal pattern: first-occurrence model. With the target
        // absent (guarded), the first-occurrence replace is a no-op, so the result is the input.
        [group: 'P47b replace/indexOf', name: 'symbolic replaceFirst absent-pattern is a no-op', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && !s.contains("XYZQ") })
                        @Ensures({ result == s })
                        static String f(String s) { s.replaceFirst("XYZQ", "A") }
                    }''')],
        // Replace identity: replacing a non-occurring substring is a no-op (requires a
        // {@code !contains} precondition so the verifier knows the substring isn't present).
        [group: 'P47b replace/indexOf', name: 'replace non-occurring is no-op', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && !s.contains("XYZQ") })
                        @Ensures({ result == s })
                        static String f(String s) { s.replace("XYZQ", "A") }
                    }''')],
        // indexOf literal: position is exact.
        [group: 'P47b replace/indexOf', name: 'literal indexOf folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 })
                        static int f() { "hello".indexOf("l") }
                    }''')],
        // indexOf with fromIndex: skipping past first occurrence finds the second.
        [group: 'P47b replace/indexOf', name: 'indexOf from-index finds later occurrence', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { "hello".indexOf("l", 3) }
                    }''')],
        // indexOf not-found returns -1.
        [group: 'P47b replace/indexOf', name: 'indexOf returns -1 when absent', ok: true,
         src: tc('''class C {
                        @Ensures({ result == -1 })
                        static int f() { "hello".indexOf("X") }
                    }''')],
        // Cross-string indexOf bound: indexOf result is always >= -1.
        [group: 'P47b replace/indexOf', name: 'indexOf result is always >= -1', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null })
                        @Ensures({ result >= -1 })
                        static int f(String s, String t) { s.indexOf(t) }
                    }''')],
    ]
}
