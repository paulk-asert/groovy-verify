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
 * 'P406 call-havoc witnesses' — found probing Phase 403. A call's frame havocs what it may write, and the model picks
 * any value its @Ensures allows there: `c$other (after a call) = 6`. The failing call was printed from that model
 * whatever the callee does — `fails on: f(new Counter(other: 5))` though `bump()` sets `other` to 5 and the claim
 * holds. A value nothing pins is a witness taint now (on the session, copied onto its verdict): a refutation resting on
 * one shows no call, saying why. One the callee's @Ensures fixes (`count == old.count + 1`) keeps its call, and so does
 * a failure that doesn't rest on the call.
 */
class G448_p406_call_havoc_witnesses {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 406: a refutation resting on what a call's frame left unknown shows no failing call (the model's value there is no run's); one the callee's @Ensures fixes, or a failure that doesn't rest on the call, keeps its call."

    static final List<Map> CASES = [

        // Before: `fails on: f(new Counter(other: 5))` — which returns 5. The claim holds; the verifier can't tell
        [group: "P406 call-havoc witnesses", name: "a claim over what a call leaves, unknown to the verifier, shows no call",
         expect: ["Cannot prove postcondition of f", "no failing call: the failure rests on what a call leaves in 'c.other'"],
         refute: "fails on",
         src: tc('''class A {
                        @Requires({ c != null && c.other == 5 })
                        @Ensures({ result == 5 })
                        static int f(Counter c) {
                            c.bump()
                            return c.other
                        }
                    }
                    final class Counter {
                        int count
                        int other
                        void bump() { other = 5 }
                    }''')],

        // … an array a helper writes, too
        [group: "P406 call-havoc witnesses", name: "… or in an array a helper writes",
         expect: ["Cannot prove postcondition of f", "no failing call: the failure rests on what a call leaves in 'a'"],
         refute: "fails on",
         src: tc('''class A {
                        static void w(int[] b) { if (b != null && b.length > 0) b[0] = 1 }
                        @Requires({ a != null && a.length > 0 && a[0] == 1 })
                        @Ensures({ result == 1 })
                        static int f(int[] a) {
                            w(a)
                            return a[0]
                        }
                    }''')],

        [group: "P406 call-havoc witnesses", name: "a value the callee's @Ensures fixes keeps the call",
         expect: ["Cannot prove postcondition of f", "fails on: f(new Counter(count: 5))"],
         src: tc('''class A {
                        @Requires({ c != null && c.count == 5 })
                        @Ensures({ result == 7 })
                        static int f(Counter c) {
                            c.bump()
                            return c.count
                        }
                    }
                    final class Counter {
                        int count
                        @Ensures({ count == old.count + 1 })
                        void bump() { count = count + 1 }
                    }''')],

        [group: "P406 call-havoc witnesses", name: "a failure that doesn't rest on the call keeps it",
         expect: ["Cannot prove postcondition of f", "fails on: f(new Counter(), "],
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ result == 1 })
                        static int f(Counter c, int n) {
                            c.bump()
                            return n
                        }
                    }
                    final class Counter {
                        int other
                        void bump() { other = 5 }
                    }''')],
    ]
}
