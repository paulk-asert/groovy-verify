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

/** 'P238 instanceof' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G302_p238_instanceof {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'instanceof yields its null fact: `x instanceof T` encodes as a fresh boolean with the one-directional axiom b implies x != null, so instanceof guards narrow nullity in every position while the type test itself stays outside the fragment.'

    static final List<Map> CASES = [

        // ---------- Phase 238: instanceof — the null fact, not the type (GROOVY-12242 parity) ----------
        // `x instanceof T` is never true of null (JVM guarantee). Each occurrence encodes as a FRESH
        // unconstrained boolean b plus the one-directional axiom `b ⟹ x != null` — sound in every
        // polarity: a positive occurrence yields the null fact, a negative one asserts nothing about x
        // (a failed type test doesn't imply null). Type-level narrowing stays outside the fragment.
        // The idiomatic early-exit shape (STC flow-types x on the continuation — GROOVY-12242).
        [group: 'P238 instanceof', name: 'early-exit !(x instanceof) narrows the continuation', ok: true,
         src: tc('''class C {
                        static int m(Object x) {
                            if (!(x instanceof String)) return 0
                            return x.length()
                        }
                    }''')],
        // The same fact on a declared String — there the test is purely a null check.
        [group: 'P238 instanceof', name: 'early-exit instanceof on a String param', ok: true,
         src: tc('''class C {
                        static int m(String s) {
                            if (!(s instanceof String)) return 0
                            return s.length()
                        }
                    }''')],
        // Positive branch: the fact holds inside the arm the test guards.
        [group: 'P238 instanceof', name: 'deref inside the instanceof branch', ok: true,
         src: tc('''class C {
                        static int m(String s) {
                            if (s instanceof String) { return s.length() }
                            return 0
                        }
                    }''')],
        // Short-circuit: the right conjunct's deref is discharged under the instanceof left conjunct.
        [group: 'P238 instanceof', name: 'instanceof as a short-circuit left conjunct', ok: true,
         src: tc('''class C {
                        static boolean m(String s) {
                            return s instanceof String && s.length() > 0
                        }
                    }''')],
        // Teeth — a non-exiting arm narrows nothing: the continuation deref still refutes.
        [group: 'P238 instanceof', name: 'non-exiting instanceof arm yields no narrowing', expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static int m(String s) {
                            if (s instanceof String) { }
                            return s.length()
                        }
                    }''')],
        // Teeth — the NEGATIVE arm learns nothing about nullity (¬b says nothing about s), and for a
        // String param this arm is in fact reachable only when s IS null — the deref must refute.
        [group: 'P238 instanceof', name: 'deref in the negative arm refutes', expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static int m(String s) {
                            if (!(s instanceof String)) { return s.length() }
                            return 0
                        }
                    }''')],
        // Teeth — the fact lands on the tested variable, not its neighbours.
        [group: 'P238 instanceof', name: 'instanceof on a different variable still refutes', expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static int m(String s, String t) {
                            if (!(t instanceof String)) return 0
                            return s.length()
                        }
                    }''')],
        // The negated-operator spelling `!instanceof` behaves identically to `!(… instanceof …)`.
        [group: 'P238 instanceof', name: 'the !instanceof spelling narrows too', ok: true,
         src: tc('''class C {
                        static int m(String s) {
                            if (s !instanceof String) return 0
                            return s.length()
                        }
                    }''')],
    ]
}
