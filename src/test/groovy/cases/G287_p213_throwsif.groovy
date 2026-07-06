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

/** 'P213 throwsif' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G287_p213_throwsif {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The @ThrowsIf exceptional contract, round 2 (prototype — the verification-owned reference implementation ahead of an upstream groovy-contracts conversation; JML exceptional_behavior / SPARK Exceptional_Cases are the prior art): @Repeatable arms, each @ThrowsIf(value = { x == null }, exception = NPE) asserting the method throws (a subtype of) the exception EXACTLY WHEN the condition holds at entry. Three modes per arm: WOVEN (default — the ContractExpansionTransform inserts the generative guard-throw pre-STC, Lombok-@NonNull-style, so the verifier simply proves the post-weave body; the reference weaving until groovy-contracts adopts the annotation), WOVEN=FALSE (the body implements the guard — hand-written or Objects.requireNonNull, which the checker models as if-null-throw-NPE; the full iff is proved with concrete witnesses on refute), and TRUSTED (specification-only for third-party throws: not woven, not proved, not warned — vacuity-checked, caller-assumed, rung-monitored). Bare gc-style condition closures ({ x == null }) are normalised to typed-param closures pre-STC. The runtime rung is repeatable-aware: a throw justified by SOME arm (type match + condition true) is a positive cross-validation; unjustified matching throws and returns-under-condition fail the run.'

    static final List<Map> CASES = [

        // ---------- Phase 213: @ThrowsIf — the universal exceptional contract ----------
        [group: 'P213 throwsif', name: 'guard-throw iff contract verifies (both directions)', ok: true,
         src: tc('''class C {
                        @ThrowsIf(value = { int n -> n < 0 }, exception = IllegalArgumentException)
                        static int inc(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            return n + 1
                        }
                    }''')],
        // guard-throw with an else-arm return: still iff.
        // (woven = false: with generative weaving on, the inserted guard would CURE this by
        // construction — the refute pins the proof direction for body-implemented contracts.)
        [group: 'P213 throwsif', name: 'must-throw refutes: returns although the condition holds', expect: 'can return normally although the condition holds',
         src: tc('''class C {
                        @ThrowsIf(value = { int n -> n < 0 }, exception = IllegalArgumentException, woven = false)
                        static int inc(int n) {
                            if (n < -5) throw new IllegalArgumentException('very negative')
                            return n + 1
                        }
                    }''')],
        [group: 'P213 throwsif', name: 'only-when refutes: throws although no @ThrowsIf condition holds', expect: 'can throw IllegalArgumentException although no @ThrowsIf condition holds',
         src: tc('''class C {
                        @ThrowsIf(value = { int n -> n < 0 }, exception = IllegalArgumentException)
                        static int inc(int n) {
                            if (n <= 0) throw new IllegalArgumentException('non-positive')
                            return n + 1
                        }
                    }''')],
        [group: 'P213 throwsif', name: 'untyped @ThrowsIf verifies (any throwable)', ok: true,
         src: tc('''class C {
                        @ThrowsIf({ int n -> n < 0 })
                        static int inc(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            return n + 1
                        }
                    }''')],
        [group: 'P213 throwsif', name: '@Requires narrows the checked domain', ok: true,
         src: tc('''class C {
                        @Requires({ n >= -10 })
                        @ThrowsIf(value = { int n -> n < 0 }, exception = IllegalStateException)
                        static int f(int n) {
                            if (n < 0) throw new IllegalStateException('negative')
                            return n
                        }
                    }''')],
        [group: 'P213 throwsif', name: 'loop body skips loudly (outside the v1 fragment)', expect: 'Skipped @ThrowsIf verification',
         src: tc('''class C {
                        @ThrowsIf({ int n -> n < 0 })
                        static int f(int n) {
                            int i = 0
                            while (i < n) { i = i + 1 }
                            if (n < 0) throw new IllegalArgumentException('negative')
                            return i
                        }
                    }''')],
        // ---------- Phase 214: round 2 — woven/trusted modes, bare closures, repeatable arms ----------
        // Paul's canonical example: woven x (the transform inserts the guard — the reference weaving),
        // unwoven y (Objects.requireNonNull IS the guard, modelled by the checker). Bare gc-style
        // closures — the transform normalises them to typed-param closures pre-STC.
        [group: 'P213 throwsif', name: 'two arms: woven + body-implemented (requireNonNull)', ok: true,
         src: tc('''class C {
                        @ThrowsIf(value = { x == null }, exception = NullPointerException)
                        @ThrowsIf(value = { y == null }, exception = NullPointerException, woven = false)
                        static Object myMethod(Object x, Object y) {
                            Objects.requireNonNull(y)
                            return x
                        }
                    }''')],
        // trusted: specification-only (the throw lives in a third-party call) — no proof, no warning.
        [group: 'P213 throwsif', name: 'trusted spec on an opaque body is quiet', ok: true,
         src: tc('''class C {
                        @ThrowsIf(value = { s == null }, exception = NullPointerException, trusted = true)
                        static Object parse(Object s) {
                            return externalLibraryCall(s)
                        }
                        static Object externalLibraryCall(Object s) { s }
                    }''')],
        // ...and the SAME opaque body without trusted skips loudly — the pair pins what trusted waives.
        [group: 'P213 throwsif', name: 'same opaque body untrusted skips loudly', expect: 'Skipped @ThrowsIf verification',
         src: tc('''class C {
                        @ThrowsIf(value = { s == null }, exception = NullPointerException, woven = false)
                        static Object parse(Object s) {
                            return externalLibraryCall(s)
                        }
                        static Object externalLibraryCall(Object s) { s }
                    }''')],
        // a vacuous TRUSTED condition is flagged (a contradictory trusted spec poisons every caller).
        [group: 'P213 throwsif', name: 'vacuous trusted condition is flagged', expect: 'TRUSTED condition is unsatisfiable',
         src: tc('''class C {
                        @ThrowsIf(value = { int n -> n < 0 && n > 0 }, exception = IllegalStateException, trusted = true)
                        static int f(int n) { return externalCall(n) }
                        static int externalCall(int n) { n }
                    }''')],
        // repeatable arms with DIFFERENT exceptions, both body-implemented.
        [group: 'P213 throwsif', name: 'two arms, two exception types, both proved', ok: true,
         src: tc('''class C {
                        @ThrowsIf(value = { int n -> n < 0 }, exception = IllegalArgumentException, woven = false)
                        @ThrowsIf(value = { int n -> n > 100 }, exception = IllegalStateException, woven = false)
                        static int clamp(int n) {
                            if (n < 0) throw new IllegalArgumentException('negative')
                            if (n > 100) throw new IllegalStateException('too big')
                            return n
                        }
                    }''')],
    ]
}
