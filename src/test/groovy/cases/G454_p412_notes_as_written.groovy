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
 * 'P412 notes as written' — found bringing examples/repros.md up to date. Phase 408's note named the conjuncts it left
 * out in no particular order (the witness taints were a HashSet), bracketed as the AST prints them, and with a singular
 * verb: `the precondition's '(h.arr.length > 0)', '(h.arr != null)' is outside …`. They come in source order now, as
 * written, and the verb agrees.
 */
class G454_p412_notes_as_written {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 412: a withheld call's note names the precondition parts it left out in source order and as written — `'h.arr != null', 'h.arr.length > 0' are outside …`, `'c.count == 5' is outside …`."

    static final List<Map> CASES = [

        [group: "P412 notes as written", name: "one part left out: as written, and 'is'",
         expect: ["Possible ArithmeticException: Division by zero",
                  "no failing call: the precondition's 'c.count == 5' is outside what the verifier models"],
         refute: "fails on",
         src: tc('''class A {
                        @Requires({ c != null && c.count == 5 })
                        static int f(Open c, int x) {
                            10 % x
                        }
                    }
                    class Open {
                        int count
                        void bump() { count = count + 1 }
                    }''')],

        [group: "P412 notes as written", name: "two parts left out: in source order, and 'are'",
         expect: "no failing call: the precondition's 'h.arr != null', 'h.arr.length > 0' are outside what the verifier models",
         refute: "fails on",
         src: tc('''class A {
                        @Requires({ h != null && h.arr != null && h.arr.length > 0 })
                        static int f(Holder h, int x) {
                            10 % x
                        }
                    }
                    final class Holder {
                        int[] arr
                    }''')],
    ]
}
