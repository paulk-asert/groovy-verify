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

/** 'P221 receiver-state specs' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G293_p221_receiver_state_specs {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Receiver-STATE spec ensures (Phase 221): an instance spec may now reference receiver state — String#indexOf(int) ships @Ensures({ result >= -1 && result < length() }), and at each consumption site the implicit-this call is SUBSTITUTED onto the actual receiver (length() becomes s.length()), translating through the native seq/oracle machinery. Decline stays the default for unsupported shapes (implicit-this calls with arguments, bare field names); requires-side receiver state remains strict. En route: the obligation-replay walk was missing checkPath\'s scalar call-assign branch, so `int i = s.indexOf(c)` left i unconstrained in implicit-obligation sessions — mirrored, and now the showpiece proves: the indexOf-then-charAt idiom discharges a NATIVE charAt bounds obligation from a REGISTRY fact plus the found-check branch; drop the check and the -1 sentinel refutes it. The String skeleton stays deliberately minimal — only what the native seq theory does not already model exactly.'

    static final List<Map> CASES = [

        // ---------- Phase 221: receiver-state ensures (String#indexOf) ----------
        // the showpiece: a NATIVE charAt bounds obligation discharged by a REGISTRY receiver-state fact
        [group: 'P221 receiver-state specs', name: 'indexOf-then-charAt: a native bounds obligation discharged by a registry fact', ok: true,
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 0 })
                        static char findOrLast(String s) {
                            int i = s.indexOf(120)
                            if (i >= 0) {
                                return s.charAt(i)
                            }
                            return s.charAt(s.length() - 1)
                        }
                    }''')],
        // teeth: forget the found-check and the -1 sails into charAt
        [group: 'P221 receiver-state specs', name: 'the -1 sentinel sails into charAt without the found-check (refutes)', expect: 'Possible IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ s != null && s.length() > 0 })
                        static char find(String s) {
                            int i = s.indexOf(120)
                            return s.charAt(i)
                        }
                    }''')],
        // the substituted ensures verbatim
        [group: 'P221 receiver-state specs', name: 'substituted receiver-state ensures verbatim (result < s.length())', ok: true,
         src: tc('''class C {
                        @Requires({ s != null })
                        @Ensures({ result < s.length() })
                        static int f(String s) {
                            return s.indexOf(120)
                        }
                    }''')],
    ]
}
