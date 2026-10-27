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

/**
 * 'P437 assumed cells unshown' — Phase 436 shows a field read through the identity map at its entry value, so the call
 * builds it. The other parameter's class invariant, assumed at entry, reads that parameter's fields too, so a failure
 * about `a` showed `b.n = 7719` and built it into the call: true (the invariant constrains it), but noise. A cell read
 * only by an entry assumption isn't shown now; one the body, a contract or the exit's re-proof reads still is.
 */
class G479_p437_assumed_cells_quiet {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 437: a field of a shared-class parameter read only by its assumed class invariant is left out of the counterexample and the failing call (`g(new C(n: 0), new C(), -1)`, not `new C(n: 7719)`); a field the body reads is still shown."

    static final List<Map> CASES = [

        // It showed `b.n = 7719` and called `g(new C(n: 0), new C(n: 7719), -1)`
        [group: "P437 assumed cells unshown", name: "the other's invariant-only field isn't shown",
         expect: ["Cannot prove class invariant of C holds for 'a' at exit of g", "fails on: g(new C(n: 0), new C(), -"],
         refute: "b.n",
         src: tc('''class A {
                        @Requires({ a != null && b != null })
                        static void g(C a, C b, int p) { a.n = p }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],

        [group: "P437 assumed cells unshown", name: "… a field the body reads is",
         expect: ["Cannot prove postcondition of h", "b.n = 0", "fails on: h(new C(n: 0), new C(n: 0))"],
         src: tc('''class A {
                        @Requires({ a != null && b != null })
                        @Ensures({ result > 0 })
                        static int h(C a, C b) { return a.n + b.n }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],
    ]
}
