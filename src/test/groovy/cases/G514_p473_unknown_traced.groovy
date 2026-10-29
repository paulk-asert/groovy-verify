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
 * 'P473 an unknown value traced through the check' — Phase 472 withholds any check's failing call whose model gives a
 * helper's unknown value one (a value no run is known to produce): conservative, since a value merely bound to a local
 * is in the model too, and `int r = h(n); return 100.intdiv(n)` no longer named `f(0)`, which fails whatever h returns.
 * The session now tells a definition (a local bound to a value) and a range every int has from the rest: the value
 * passes through definitions to the locals bound to it, and only another assertion mentioning one — a path condition,
 * the obligation — is a dependence. With none, the call is named again.
 */
class G514_p473_unknown_traced {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 473: a check's failing call is withheld over a helper's unknown value only when the value — or a local bound to it, through any chain of locals — reaches a path condition or the obligation; one merely bound on the path names its call again (`int r = h(n); 100.intdiv(n)` fails on f(0))."

    static final String UNKNOWN = 'which the verifier can\'t evaluate'

    static final List<Map> CASES = [

        // ---------- the value decides nothing: the call named ----------
        [group: "P473 an unknown value traced through the check", name: "a value bound and unread", expect: ['Possible ArithmeticException', 'fails on: f(0)'],
         src: tc('''class A {
                        static int f(int n) {
                            int r = h(n)
                            return 100.intdiv(n)
                        }
                        static int h(int i) { new Random().nextInt() }
                    }''')],

        [group: "P473 an unknown value traced through the check", name: "… through a chain of locals, unread", expect: ['Possible ArithmeticException', 'fails on: f(0)'],
         src: tc('''class A {
                        static int f(int n) {
                            int r = h(n)
                            int t = r + 1
                            return 100.intdiv(n)
                        }
                        static int h(int i) { new Random().nextInt() }
                    }''')],

        // ---------- the value decides it: the call withheld ----------
        [group: "P473 an unknown value traced through the check", name: "a local of it in the condition", expect: ['Possible ArithmeticException', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        static int f(int n) {
                            int r = h(n)
                            if (r > 0) return 100.intdiv(n)
                            return 0
                        }
                        static int h(int i) { new Random().nextInt() }
                    }''')],

        [group: "P473 an unknown value traced through the check", name: "… through a chain of locals", expect: ['Possible ArithmeticException', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        static int f(int n) {
                            int r = h(n)
                            int t = r + 1
                            if (t > 0) return 100.intdiv(n)
                            return 0
                        }
                        static int h(int i) { new Random().nextInt() }
                    }''')],

        [group: "P473 an unknown value traced through the check", name: "the value in the obligation", expect: ['Possible ArithmeticException', 'what h(…) returns', UNKNOWN], refute: 'fails on',
         src: tc('''class A {
                        static int f(int n) {
                            return 100.intdiv(h(n))
                        }
                        static int h(int i) { new Random().nextInt() }
                    }''')],
    ]
}
