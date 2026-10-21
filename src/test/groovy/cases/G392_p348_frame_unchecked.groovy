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
 * 'P348 an unchecked frame is loud' — a declared @Modifies is trusted at every call site (Phase 13/347), so the frame
 * check is the only thing standing between a wrong declaration and an unsound proof. Phase 347 checked it against the
 * inferred write set but, when the body's writes couldn't be bounded, fell back to the old partial visitor in silence.
 * Now the collector records the first construct it gave up on (VerifyChecker.unbounded), the frame check reports it
 * — naming the construct, with whatever the partial visitor can still see — and the Phase 347 call-site skip names
 * the same construct.
 */
class G392_p348_frame_unchecked {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 348 an unchecked frame is loud: a method whose declared @Modifies cannot be checked because its body has a construct whose writes cannot be bounded (a multiple assignment, a synchronized block, a call to a sibling-class static or to a helper that is itself unbounded, a writer passed an argument that is not a named variable) is reported, naming the construct and any write the partial check can still see outside the clause. Callers keep trusting the declaration (sound by declaration), so the report is the one place a wrong one would be caught. The Phase 347 call-site skip names the same construct.'

    static final List<Map> CASES = [

        // A multiple assignment is a construct the collector doesn't follow, so the body's writes can't be bounded: before
        // Phase 348 the frame passed on the partial visitor alone (silently), while every caller trusted the clause.
        // (These cases used `l << x` until Phase 349 gave `<<` a bounded reading.)
        [group: 'P348 an unchecked frame is loud', name: 'a declared frame over an unbounded body is flagged, naming the construct', expect: ["Cannot check the @Modifies clause [count] of 'bump': its body's writes can't be bounded", "multiple assignment 'def (a, b) = [x, x]'"],
         src: tc('''class C {
                        int count = 0
                        @Modifies({ this.count })
                        void bump(int x) { def (a, b) = [x, x]; count = a + b }
                    }''')],
        [group: 'P348 an unchecked frame is loud', name: 'the same body with plain assignments is bounded and checked', ok: true,
         src: tc('''class C {
                        int count = 0
                        @Modifies({ this.count })
                        void bump(int x) { int a = x; int b = x; count = a + b }
                    }''')],
        [group: 'P348 an unchecked frame is loud', name: 'a helper it calls carries its own reason up', expect: ["Cannot check the @Modifies clause [count] of 'bump': its body's writes can't be bounded", "call 'weird(…)': multiple assignment 'def (a, b) = [x, x]'"],
         src: tc('''class C {
                        int count = 0
                        static int weird(int x) { def (a, b) = [x, x]; return a + b }
                        @Modifies({ this.count })
                        void bump(int x) { count = weird(x) }
                    }''')],
        // STC keeps one error per anchor, so the violation the old visitor can still see rides in the same message.
        [group: 'P348 an unchecked frame is loud', name: 'the partial check still names a write it can see outside the clause', expect: ["Cannot check the @Modifies clause [count] of 'bump': its body's writes can't be bounded", "The partial check already sees it write 'other', outside the clause"],
         src: tc('''class C {
                        int count = 0
                        int other = 0
                        @Modifies({ this.count })
                        void bump(int x) { def (a, b) = [x, x]; count = a + b; other = 1 }
                    }''')],
        // A library static with no registry spec is unbounded, and says so. (A sibling class's static was the example
        // until Phase 350 read it by its body.)
        [group: 'P348 an unchecked frame is loud', name: 'a static call on another class has no frame', expect: ["Cannot check the @Modifies clause [count] of 'bump': its body's writes can't be bounded", "static call 'System.identityHashCode(…)' with no @Pure or @Modifies spec"],
         src: tc('''class C {
                        int count = 0
                        @Modifies({ this.count })
                        void bump(int x) { count = System.identityHashCode(x) }
                    }''')],
        [group: 'P348 an unchecked frame is loud', name: 'a writer passed an argument that isn\'t a named variable', expect: ["Cannot check the @Modifies clause [count] of 'bump': its body's writes can't be bounded", "call 'fill(…)' writes its parameter 'a', but the argument 'new int[1]' isn't a named variable"],
         src: tc('''class C {
                        int count = 0
                        static void fill(int[] a, int v) { if (a.length > 0) a[0] = v }
                        @Modifies({ this.count })
                        void bump(int x) { fill(new int[1], x); count = x }
                    }''')],
        [group: 'P348 an unchecked frame is loud', name: 'a statement the collector doesn\'t follow', expect: ["Cannot check the @Modifies clause [count] of 'bump': its body's writes can't be bounded", "a synchronized statement"],
         src: tc('''class C {
                        int count = 0
                        @Modifies({ this.count })
                        void bump(int x) { synchronized (this) { count = x } }
                    }''')],
        [group: 'P348 an unchecked frame is loud', name: 'the Phase 347 call-site skip names the construct too', expect: ["Skipped verification of postcondition for f (call 'weird(…)' whose writes can't be bounded from its body: multiple assignment 'def (a, b) = [x, x]' — declare @Modifies on weird)"],
         src: tc('''class C {
                        static int count = 0
                        static int weird(int x) { def (a, b) = [x, x]; count = a + b; return x }
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int s = weird(n)
                            return s
                        }
                    }''')],
        // The declaration is what callers go through (sound by declaration, Phase 13/347): f proves `count == 0` past the
        // call, and the one place that could catch a wrong declaration says it can't — the flag is the whole point.
        [group: 'P348 an unchecked frame is loud', name: 'a declared frame is still trusted by the caller while the body is flagged', expect: ["Cannot check the @Modifies clause [] of 'weird': its body's writes can't be bounded — multiple assignment"], refute: 'Cannot prove postcondition of f',
         src: tc('''class C {
                        static int count = 0
                        @Modifies({ [] })
                        @Ensures({ result == x })
                        static int weird(int x) { def (a, b) = [x, x]; return a + b - x }
                        @Requires({ n >= 0 && count == 0 })
                        @Ensures({ result == n && count == 0 })
                        static int f(int n) {
                            int s = weird(n)
                            return s
                        }
                    }''')],
    ]
}
