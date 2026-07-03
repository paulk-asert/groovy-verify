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

/** 'P206 functional leftpad' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G281_p206_functional_leftpad {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The FUNCTIONAL leftpad (the lets-prove-leftpad "dafny (functional)" sibling): a String-returning recursion prepending one pad character per step, with @Decreases(n - s.length()) and the self-call @Ensures as the induction hypothesis — identity and length prove over Z3\'s native seq theory (length-of-concat is a theorem, not an axiom). The prefix character clause ALONE refutes — it is not individually inductive (index n-|s|-1 needs the suffix clause in the hypothesis), which is exactly why the Dafny entry states all four clauses together; the full four-clause spec is a solver boundary (seq-nth quantifiers + induction time out) pinned as a never-cleanly-proves canary. Teeth: a wrong length claim refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 206: functional leftpad — recursion + induction, no loops, no mutation ----------
        // The functional skeleton: identity (already long enough) and length (max) by structural
        // induction; length-of-concat comes free from the native seq theory.
        [group: 'P206 functional leftpad', name: 'identity + length by induction', ok: true,
         src: tc('''class C {
                       @Requires({ pad != null && s != null && pad.length() == 1 })
                       @Ensures({ (s.length() >= n ==> result == s) &&
                                  (s.length() < n ==> result.length() == n) })
                       @Decreases({ n - s.length() })
                       static String leftpad(String pad, int n, String s) {
                           s.length() >= n ? s : leftpad(pad, n, pad + s)
                       }
                   }''')],
        // INSTRUCTIVE refute: the pad-prefix clause alone is NOT inductive — the index n-|s|-1 of this
        // call's result is covered by the RECURSIVE call's suffix clause, absent from this hypothesis.
        // (The reason Dafny's functional entry states all four ensures together.)
        [group: 'P206 functional leftpad', name: 'prefix clause alone is not inductive (refutes)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ pad != null && s != null && pad.length() == 1 })
                       @Ensures({ (s.length() >= n ==> result == s) &&
                                  (s.length() < n ==> result.length() == n) &&
                                  (s.length() < n ==> (0..<(n - s.length())).every { int i -> result.charAt(i) == pad.charAt(0) }) })
                       @Decreases({ n - s.length() })
                       static String leftpad(String pad, int n, String s) {
                           s.length() >= n ? s : leftpad(pad, n, pad + s)
                       }
                   }''')],
        // The full mutually-inductive four-clause spec is a solver boundary: seq-nth quantifiers plus
        // the induction defeat the timeout. Pinned canary-style — refute or timeout both match; a clean
        // verify (a future solver/engine win) fails this case loudly so it gets flipped to ok: true.
        [group: 'P206 functional leftpad', name: 'full four-clause spec never cleanly proves (boundary)', expect: 'postcondition of leftpad',
         src: tc('''class C {
                       @Requires({ pad != null && s != null && pad.length() == 1 })
                       @Ensures({ (s.length() >= n ==> result == s) &&
                                  (s.length() < n ==> result.length() == n) &&
                                  (s.length() < n ==> (0..<(n - s.length())).every { int i -> result.charAt(i) == pad.charAt(0) }) &&
                                  (s.length() < n ==> (0..<s.length()).every { int i -> result.charAt(n - s.length() + i) == s.charAt(i) }) })
                       @Decreases({ n - s.length() })
                       static String leftpad(String pad, int n, String s) {
                           s.length() >= n ? s : leftpad(pad, n, pad + s)
                       }
                   }''')],
        // Teeth: a wrong length claim refutes through the same induction.
        [group: 'P206 functional leftpad', name: 'wrong length claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       @Requires({ pad != null && s != null && pad.length() == 1 })
                       @Ensures({ s.length() < n ==> result.length() == n + 1 })
                       @Decreases({ n - s.length() })
                       static String leftpad(String pad, int n, String s) {
                           s.length() >= n ? s : leftpad(pad, n, pad + s)
                       }
                   }''')],
    ]
}
