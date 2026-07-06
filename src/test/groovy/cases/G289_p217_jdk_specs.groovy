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

/** 'P217 jdk specs' — 19 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G289_p217_jdk_specs {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The starter JDK specs artifact (Slice C): shipped skeletons for java.lang.Math (abs, negateExact with its true-iff @ThrowsIf at MIN_VALUE, floorDiv with its zero-divisor @ThrowsIf), java.lang.Integer (signum, sign-split ensures), and java.util.Objects (requireNonNull — @ThrowsIf(null) plus a non-null ensures, consumed under the Object-formal leniency rule: a spec\'s Object parameter accepts any reference actual). Chosen for provably-TRUE contracts: every @ThrowsIf arm is a genuine iff (negateExact throws exactly at the one unrepresentable point; floorDiv exactly at zero divisor) — Integer.parseInt is deliberately absent because its exact throw condition is outside the fragment and @ThrowsIf is an iff contract (one-directional signals-style arms are recorded future work). Consumers prove conditional ensures under caller guards and refute over-strong claims through the specs; all consumption is ledgered. Post-218 expansion: Math.max/min (total specs — nested composition proves clamp), floorMod (divisor-sign range facts + zero-divisor @ThrowsIf), addExact (overflow condition spelled over longs so the closure is also runtime-correct), Integer.compare (exact -1/0/1), Objects.checkIndex (the guard idiom as a method). Character (predicates via the boolean-return admission extension): isDigit/isUpperCase/isLowerCase and the toUpperCase/toLowerCase 32-point shifts — PARTIAL specs by design (the real predicates are Unicode-aware), each stated fact true over the ASCII ranges it names, everything else honestly opaque (the unguarded !isDigit claim refutes); the case round-trip composes two partial specs. String is deliberately absent: its core surface is natively modelled in the seq theory (better than trusted specs), and the rest gates on instance-method assumption consumption (recorded). Long (max/min/compare/signum/sum via Long\'s OWN single-overload statics — Math\'s long overloads are deferred: same-arity overload pairs would trip the ambiguity-declining lookups; sum\'s ensures is overflow-guarded, since the runtime wraps and a trusted-but-false spec is the one thing the registry must not ship).'

    static final List<Map> CASES = [

        // ---------- Phase 217: the starter JDK specs (Slice C) ----------
        // Skeletons: src/main/resources/META-INF/groovy-verify/specs/{java.lang.Math,java.lang.Integer,java.util.Objects}.groovy
        [group: 'P217 jdk specs', name: 'Math.negateExact: conditional ensures under the caller guard', ok: true,
         src: tc('''class C {
                        @Requires({ a != Integer.MIN_VALUE })
                        @Ensures({ result == -a })
                        static int f(int a) {
                            return Math.negateExact(a)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Integer.signum: sign-split ensures consumed', ok: true,
         src: tc('''class C {
                        @Requires({ a > 0 })
                        @Ensures({ result == 1 })
                        static int f(int a) {
                            return Integer.signum(a)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'over-strong signum claim refutes through the spec', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f(int a) {
                            return Integer.signum(a)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Objects.requireNonNull: non-null ensures (Object-formal leniency)', ok: true,
         src: tc('''class C {
                        @Ensures({ result != null })
                        static Object f(Object x) {
                            return java.util.Objects.requireNonNull(x)
                        }
                    }''')],
        // ---------- post-218 expansion: the high-priority core methods ----------
        // the showpiece: nested spec calls — clamp via max(min(...)) proves the range property
        [group: 'P217 jdk specs', name: 'clamp: nested max/min spec composition proves the range', ok: true,
         src: tc('''class C {
                        @Requires({ lo <= hi })
                        @Ensures({ lo <= result && result <= hi })
                        static int clamp(int x, int lo, int hi) {
                            return Math.max(lo, Math.min(x, hi))
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'floorMod: divisor-sign range ensures', ok: true,
         src: tc('''class C {
                        @Requires({ n > 0 })
                        @Ensures({ 0 <= result && result < n })
                        static int wrap(int i, int n) {
                            return Math.floorMod(i, n)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'floorMod over-claim refutes (result can be 0)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n > 0 })
                        @Ensures({ result > 0 })
                        static int wrap(int i, int n) {
                            return Math.floorMod(i, n)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Integer.compare as contract vocabulary', ok: true,
         src: tc('''class C {
                        @Requires({ Integer.compare(x, y) == -1 })
                        @Ensures({ result == y })
                        static int larger(int x, int y) {
                            return Math.max(x, y)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Objects.checkIndex identity under the range guard', ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i && i < n })
                        @Ensures({ result == i })
                        static int f(int i, int n) {
                            return java.util.Objects.checkIndex(i, n)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Math.addExact: long-spelled overflow condition, exact sum ensured', ok: true,
         src: tc('''class C {
                        @Requires({ a >= 0 && a <= 1000 && b >= 0 && b <= 1000 })
                        @Ensures({ result == a + b })
                        static int f(int a, int b) {
                            return Math.addExact(a, b)
                        }
                    }''')],
        // ---------- post-218c: Character (partial-but-true ASCII facts; boolean-return admission) ----------
        [group: 'P217 jdk specs', name: 'Character.isDigit: ascii range implies true', ok: true,
         src: tc('''class C {
                        @Requires({ c >= ('0' as char) && c <= ('9' as char) })
                        @Ensures({ result })
                        static boolean f(char c) {
                            return Character.isDigit(c)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Character.isDigit: ascii letters imply false', ok: true,
         src: tc('''class C {
                        @Requires({ c >= ('a' as char) && c <= ('z' as char) })
                        @Ensures({ !result })
                        static boolean f(char c) {
                            return Character.isDigit(c)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Character.toUpperCase: the 32 code-point shift', ok: true,
         src: tc('''class C {
                        @Requires({ c >= ('a' as char) && c <= ('z' as char) })
                        @Ensures({ result == c - 32 })
                        static char up(char c) {
                            return Character.toUpperCase(c)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'case round-trip composes two partial specs', ok: true,
         src: tc('''class C {
                        @Requires({ c >= ('a' as char) && c <= ('z' as char) })
                        @Ensures({ result == c })
                        static char roundTrip(char c) {
                            return Character.toLowerCase(Character.toUpperCase(c))
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Unicode honesty: unguarded isDigit claim refutes (partial spec stays partial)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ !result })
                        static boolean f(char c) {
                            return Character.isDigit(c)
                        }
                    }''')],
        // ---------- Long: the mechanical mirror, via Long's own single-overload statics ----------
        [group: 'P217 jdk specs', name: 'Long clamp: nested max/min composition over longs', ok: true,
         src: tc('''class C {
                        @Requires({ lo <= hi })
                        @Ensures({ lo <= result && result <= hi })
                        static long clamp(long x, long lo, long hi) {
                            return Long.max(lo, Long.min(x, hi))
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Long.compare as contract vocabulary', ok: true,
         src: tc('''class C {
                        @Requires({ Long.compare(x, y) == 1 })
                        @Ensures({ result == x })
                        static long larger(long x, long y) {
                            return Long.max(x, y)
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Long.signum of a guarded Long.sum composes', ok: true,
         src: tc('''class C {
                        @Requires({ a > 0 && a < 1000000 && b > 0 && b < 1000000 })
                        @Ensures({ result == 1 })
                        static int f(long a, long b) {
                            return Long.signum(Long.sum(a, b))
                        }
                    }''')],
        [group: 'P217 jdk specs', name: 'Long.signum over-claim refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f(long a) {
                            return Long.signum(a)
                        }
                    }''')],
    ]
}
