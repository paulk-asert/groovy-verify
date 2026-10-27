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
 * 'P438 a cached refutation's model' — a check identical to an earlier one is answered from the VC cache (Phase 34),
 * which keeps the verdict and counterexample but no model. A note read from the model was missing on a hit: Phase 435's
 * `broken conjunct:`, Phase 433's naming of the parameter whose invariant broke (Phase 437 patched the one-invariant
 * case), Phase 126's offending elements — so the same failure read differently depending on what was checked first.
 *
 * A model is recovered on demand, when a note asks for one: the query re-solved with the cached counterexample's
 * values pinned, so the note describes the failure shown.
 */
class G480_p438_cached_model {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 438: a refutation answered from the solver cache recovers a model (pinned to the cached counterexample) when a note needs one, so `broken conjunct:` and a parameter's invariant attribution read the same whichever check came first."

    static final List<Map> CASES = [

        // f and g are one query: g's is a cache hit, and had no `broken conjunct:` line
        [group: "P438 a cached refutation's model", name: "a cache hit names the broken conjunct too",
         expect: ["broken conjunct: (result > 1)\n    fails on: f(1)", "broken conjunct: (result > 1)\n    fails on: g(1)"],
         src: tc('''class A {
                        @Requires({ p == 1 })
                        @Ensures({ result > 0 && result > 1 })
                        static int f(int p) { return p }
                        @Requires({ p == 1 })
                        @Ensures({ result > 0 && result > 1 })
                        static int g(int p) { return p }
                    }''')],

        // Two invariants owed, the one-invariant patch of Phase 437 doesn't apply: the model names which
        [group: "P438 a cached refutation's model", name: "a cache hit names the parameter whose invariant broke",
         expect: ["Cannot prove class invariant of C holds for 'a' at exit of f", "Cannot prove class invariant of C holds for 'a' at exit of g"],
         refute: ["holds for 'b'", "holds at method exit"],
         src: tc('''class A {
                        @Requires({ a != null && b != null && a !== b })
                        static void f(C a, C b) { a.n = -1; b.n = 1 }
                        @Requires({ a != null && b != null && a !== b })
                        static void g(C a, C b) { a.n = -1; b.n = 1 }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],
    ]
}
