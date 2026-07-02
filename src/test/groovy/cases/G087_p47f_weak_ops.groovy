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

/** 'P47f weak ops' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G087_p47f_weak_ops {

    static final List<Map> CASES = [

        // ---------- Phase 47f: replaceAll + lastIndexOf as uninterpreted ----------
        // replaceAll on a non-occurring substring is a no-op (axiom 1).
        [group: 'P47f weak ops', name: 'replaceAll non-occurring is no-op', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && !s.contains("XYZ") })
                        @Ensures({ result == s })
                        static String f(String s) { s.replaceAll("XYZ", "A") }
                    }''')],
        // replaceAll preserves length when old and new have equal length (axiom 2).
        [group: 'P47f weak ops', name: 'replaceAll preserves length under equal-length swap', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s.length() })
                        static int f(String s) { s.replaceAll("a", "b").length() }
                    }''')],
        // Soundness: replaceAll content beyond the axioms isn't claimable. Unequal-length
        // replacement doesn't preserve length, so claiming it does refutes.
        [group: 'P47f weak ops', name: 'replaceAll length under unequal-length swap not provable',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s.length() })
                        static int f(String s) { s.replaceAll("a", "bc").length() }
                    }''')],
        // A *constant* replaceAll — even with a real regex pattern — folds via the actual JDK method,
        // so the character class resolves exactly: "hello".replaceAll("[aeiou]","X") == "hXllX".
        [group: 'P47f weak ops', name: 'constant regex replaceAll folds exactly', ok: true,
         src: tc('''class C {
                        @Ensures({ result == "hXllX" })
                        static String f() { "hello".replaceAll("[aeiou]", "X") }
                    }''')],
        // Soundness: a *symbolic* receiver with a regex (metacharacter) pattern can't be modelled as a
        // literal substring — it skips loudly instead of mis-firing the no-op axiom. (Before the fix
        // the literal `contains(s, "[aeiou]")` was false, so `result == s` wrongly *verified*.)
        [group: 'P47f weak ops', name: 'symbolic regex-pattern replaceAll skips (no literal-contains misfire)',
         expect: 'Skipped verification of postcondition',
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result == s })
                        static String f(String s) { s.replaceAll("[aeiou]", "X") }
                    }''')],
        // lastIndexOf result is always >= -1.
        [group: 'P47f weak ops', name: 'lastIndexOf >= -1', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null })
                        @Ensures({ result >= -1 })
                        static int f(String s, String t) { s.lastIndexOf(t) }
                    }''')],
        // lastIndexOf is -1 when sub doesn't occur.
        [group: 'P47f weak ops', name: 'lastIndexOf -1 when absent', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && t != null && !s.contains(t) })
                        @Ensures({ result == -1 })
                        static int f(String s, String t) { s.lastIndexOf(t) }
                    }''')],
    ]
}
