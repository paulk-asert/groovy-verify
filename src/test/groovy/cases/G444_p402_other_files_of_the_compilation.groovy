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
 * 'P402 other files of the compilation' — found re-porting groovy6-functional's demos: a static on a class in ANOTHER
 * file of the same compilation (`ISqrt.isqrt` from `ISqrt.groovy`, called in `GoodCalls.groovy`) was read as a class
 * compiled elsewhere — the sibling-class rules (Phase 350) looked only at the caller's own file — so its frame was
 * unknown, every helper calling it was unbounded, and Phase 400's hoisting threw out of the whole value-flow pass:
 * every assert in the method skipped as "outside the value-flow fragment (a re-assignment or loop)". A static's body
 * in the same compilation is the one that runs, so it is read like a same-file sibling's; and an assert whose call
 * can't be hoisted now skips alone, saying why. (`extraSources` compiles the other files in the same unit, as groovyc
 * does a source set.)
 */
class G444_p402_other_files_of_the_compilation {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 402: a static on a class from another file of the same compilation is framed and evaluated like a same-file sibling's, and an assert whose call can't be hoisted skips alone, naming why."

    static final String ISQRT_ENSURED = '''import groovy.contracts.Ensures
import groovy.contracts.Requires
class ISqrt {
    @Requires({ x >= 0 })
    @Ensures({ result >= 0 && (long) result * result <= x && x < ((long) result + 1) * (result + 1) })
    static int isqrt(int x) {
        (int) Math.sqrt((double) x)
    }
}
'''

    static final String ISQRT_BARE = '''import groovy.contracts.Requires
class ISqrt {
    @Requires({ x >= 0 })
    static int isqrt(int x) {
        (int) Math.sqrt((double) x)
    }
}
'''

    static final String VIA = '''class GoodCalls {
                        static int viaLiteral() {
                            ISqrt.isqrt(5)
                        }
                        static int viaIfCondition(int n) {
                            if (n >= 0) {
                                return ISqrt.isqrt(n)
                            }
                            -1
                        }
                        static void main(String[] args) {
                            assert viaLiteral() == 2
                            assert viaIfCondition(9) == 3
                            assert viaIfCondition(-1) == -1
                        }
                    }'''

    static final List<Map> CASES = [

        // Before: all three `Skipped assertion safety check (the method body is outside the value-flow fragment …)`.
        [group: "P402 other files of the compilation", name: "a static in another file is framed and its contract used",
         ok: true, extraSources: ['ISqrt.groovy': ISQRT_ENSURED],
         src: tc(VIA)],

        // Without isqrt's @Ensures the root claims can't follow, but the branch that never calls it proves, and nothing
        // reads as "outside the value-flow fragment"
        [group: "P402 other files of the compilation", name: "… without its contract, only what follows anyway",
         expect: ["Assertion may not hold: (GoodCalls.viaLiteral() == 2)", "Assertion may not hold: (GoodCalls.viaIfCondition(9) == 3)"],
         refute: "value-flow fragment", extraSources: ['ISqrt.groovy': ISQRT_BARE],
         src: tc(VIA)],

        // A call whose writes can't be bounded (an unknown library static) skips its own assert, saying why; the
        // assert beside it still proves
        [group: "P402 other files of the compilation", name: "an assert over an unboundable call skips alone, naming why",
         expect: ["Skipped assertion safety check (condition '(A.t() == 3)' is outside fragment (call 't(…)' whose writes can't be bounded"],
         refute: ["value-flow fragment", "A.inc(41) == 42"],
         src: tc('''class A {
                        @Ensures({ result == x + 1 })
                        static int inc(int x) { x + 1 }
                        static int t() { System.identityHashCode(null) }
                        static void main(String[] args) {
                            assert inc(41) == 42
                            assert t() == 3
                        }
                    }''')],
    ]
}
