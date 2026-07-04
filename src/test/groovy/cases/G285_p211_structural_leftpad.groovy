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

/** 'P211 structural leftpad' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G285_p211_structural_leftpad {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The COMPLETE functional leftpad (all three lets-prove-leftpad properties, no loops, no mutation), enabled by String-valued pure helpers (Phase 211: the f# machinery declares UFs and defining equations in the helper\'s declared sorts — String params arrive as String terms, a String-valued ternary body translates in the String sort, and a same-class pure String call is a String receiver). The spec is STRUCTURAL: result == pads(pad, n - s.length()) + s, where pads is a recursive builder — this single equality pins the prefix and suffix exactly; the length property is DERIVED Verus-style by a theorem method from the structural ensures plus a pads-length lemma. The recursion prepends to the RESULT (leftpad(pad, n-1, s)) — the accumulator form (leftpad(pad, n, pad+s)) needs a commutation lemma the structural induction avoids. Teeth: a structurally-wrong claim (s + pads) refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 211: the complete functional leftpad — structural spec + derived length ----------
        // pads(pad, k) is the recursive padding builder; the structural ensures pins prefix AND suffix in
        // one equality; padsLen (induction over pads) bridges to the length property in lengthTheorem
        // (the Verus proof-fn shape: call the lemma, return the value, let the ensures close).
        [group: 'P211 structural leftpad', name: 'functional leftpad: all three properties (structural + derived length)', ok: true,
         src: tc('''class C {
                       @Requires({ pad != null && s != null && pad.length() == 1 })
                       @Ensures({ (s.length() >= n ==> result == s) &&
                                  (s.length() < n ==> result == pads(pad, n - s.length()) + s) })
                       @Decreases({ n - s.length() })
                       static String leftpad(String pad, int n, String s) {
                           s.length() >= n ? s : pad + leftpad(pad, n - 1, s)
                       }
                       static String pads(String pad, int k) {
                           k <= 0 ? '' : pad + pads(pad, k - 1)
                       }
                       @Requires({ pad != null && pad.length() == 1 && k >= 0 })
                       @Ensures({ pads(pad, k).length() == k })
                       @Decreases({ k })
                       static void padsLen(String pad, int k) {
                           if (k > 0) { padsLen(pad, k - 1) }
                       }
                       @Requires({ pad != null && s != null && pad.length() == 1 && s.length() < n })
                       @Ensures({ result.length() == n })
                       static String lengthTheorem(String pad, int n, String s) {
                           padsLen(pad, n - s.length())
                           return leftpad(pad, n, s)
                       }
                   }''')],
        // Teeth: the structurally-wrong claim (padding appended on the wrong side) refutes.
        [group: 'P211 structural leftpad', name: 'padding on the wrong side refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ pad != null && s != null && pad.length() == 1 })
                       @Ensures({ (s.length() >= n ==> result == s) &&
                                  (s.length() < n ==> result == s + pads(pad, n - s.length())) })
                       @Decreases({ n - s.length() })
                       static String leftpad(String pad, int n, String s) {
                           s.length() >= n ? s : pad + leftpad(pad, n - 1, s)
                       }
                       static String pads(String pad, int k) {
                           k <= 0 ? '' : pad + pads(pad, k - 1)
                       }
                       @Requires({ pad != null && pad.length() == 1 && k >= 0 })
                       @Ensures({ pads(pad, k).length() == k })
                       @Decreases({ k })
                       static void padsLen(String pad, int k) {
                           if (k > 0) { padsLen(pad, k - 1) }
                       }
                       @Requires({ pad != null && s != null && pad.length() == 1 && s.length() < n })
                       @Ensures({ result.length() == n })
                       static String lengthTheorem(String pad, int n, String s) {
                           padsLen(pad, n - s.length())
                           return leftpad(pad, n, s)
                       }
                   }''')],
        // Teeth: an off-by-one length theorem never proves (canary: refute or timeout, verify fails loudly).
        [group: 'P211 structural leftpad', name: 'off-by-one length theorem never proves (canary)', expect: 'postcondition of lengthTheorem',
         src: tc('''class C {
                       @Requires({ pad != null && s != null && pad.length() == 1 })
                       @Ensures({ (s.length() >= n ==> result == s) &&
                                  (s.length() < n ==> result == pads(pad, n - s.length()) + s) })
                       @Decreases({ n - s.length() })
                       static String leftpad(String pad, int n, String s) {
                           s.length() >= n ? s : pad + leftpad(pad, n - 1, s)
                       }
                       static String pads(String pad, int k) {
                           k <= 0 ? '' : pad + pads(pad, k - 1)
                       }
                       @Requires({ pad != null && pad.length() == 1 && k >= 0 })
                       @Ensures({ pads(pad, k).length() == k })
                       @Decreases({ k })
                       static void padsLen(String pad, int k) {
                           if (k > 0) { padsLen(pad, k - 1) }
                       }
                       @Requires({ pad != null && s != null && pad.length() == 1 && s.length() < n })
                       @Ensures({ result.length() == n + 1 })
                       static String lengthTheorem(String pad, int n, String s) {
                           padsLen(pad, n - s.length())
                           return leftpad(pad, n, s)
                       }
                   }''')],
    ]
}
