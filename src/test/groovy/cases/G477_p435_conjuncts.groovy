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
 * 'P435 conjuncts' — an `@Ensures` conjunction is one goal, so two claims each of which proves could time out together:
 * `!result.startsWith(" ") && !result.endsWith(" ")` over a trim (Phase 427's recorded limit) was `Could not decide`.
 * An undecided conjunction is now asked conjunct by conjunct on the same path, the whole proving when each does, and a
 * conjunct that still fails reporting on its own. A refuted conjunction names the conjuncts its model breaks, when not
 * all of them (`broken conjunct: …`).
 */
class G477_p435_conjuncts {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 435: an @Ensures conjunction the solver can't decide whole is checked conjunct by conjunct (so a trim's no-leading-and-no-trailing-space claim proves), and a refuted conjunction names the conjunct its counterexample breaks."

    static final List<Map> CASES = [

        // `Could not decide` before (Phase 427)
        [group: "P435 conjuncts", name: "an undecided conjunction proves part by part",
         ok: true,
         src: tc('''class A {
                        @Requires({ s != null })
                        @Ensures({ !result.startsWith(" ") && !result.endsWith(" ") })
                        static String f(String s) { return s.trim() }
                    }''')],

        [group: "P435 conjuncts", name: "a refutation names the conjunct it breaks",
         expect: ["Cannot prove postcondition of f", "broken conjunct: !(result.endsWith('x'))", "fails on: f(\"x\")"],
         src: tc('''class A {
                        @Requires({ s != null })
                        @Ensures({ !result.startsWith(' ') && !result.endsWith(' ') && !result.endsWith('x') })
                        static String f(String s) { return s.trim() }
                    }''')],

        [group: "P435 conjuncts", name: "… several",
         expect: ["Cannot prove postcondition of g", "broken conjuncts: (result > 0), (result > 1)"],
         src: tc('''class A {
                        @Requires({ p == 0 })
                        @Ensures({ result >= 0 && result > 0 && result > 1 })
                        static int g(int p) { return p }
                    }''')],

        // Every conjunct broken: the ensured line says it all
        [group: "P435 conjuncts", name: "… and none when the model breaks them all",
         expect: ["Cannot prove postcondition of g", "ensured: ((result > 0) && (result > 1))"],
         refute: "broken conjunct",
         src: tc('''class A {
                        @Ensures({ result > 0 && result > 1 })
                        static int g() { return 0 }
                    }''')],
    ]
}
