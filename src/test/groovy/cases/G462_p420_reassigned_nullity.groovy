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
 * 'P420 reassigned nullity' — a reassignment left a local's old nullity in place. The region replay
 * ({@code LoopEncoder.rebind}) bound it only for a list or array's alias, and the value-flow replay only from a variable
 * (Phase 227), so `Map m = [:]; m = null; m.size()` compiled cleanly, as did `m = p` for a map; a builder's or string's
 * `m = p` reported with a call that doesn't fail (`f(new StringBuilder())`: the model chose `p` non-null and `m` null).
 * And an unannotated loop's summary kept the nullity of a local its body sets to `null`.
 *
 * The name's nullity is the new value's now: a `null` is null, a variable's is its, a literal, a `new` and a
 * `java.lang.String` method's `String` are non-null; any other is unknown, and a call resting on it is withheld. A loop's
 * summary leaves a name it reassigns of unknown nullity (a call's receiver keeps its own).
 */
class G462_p420_reassigned_nullity {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 420: a reassignment sets the local's nullity to the new value's — null, a variable's, non-null for a literal, a `new` or a String method's String, otherwise unknown (its call withheld) — and a loop's summary leaves a local it reassigns of unknown nullity."

    static final List<Map> CASES = [

        [group: "P420 reassigned nullity", name: "a literal local set to null",
         expect: ["Cannot invoke method size() on null object", "obligation: m != null", "fails on: f()"],
         src: tc('''class A {
                        static int f() {
                            Map<String, Integer> m = [:]
                            m = null
                            return m.size()
                        }
                    }''')],

        [group: "P420 reassigned nullity", name: "… a list's, under <<",
         expect: ["Cannot invoke method leftShift() on null object", "fails on: f()"],
         src: tc('''class A {
                        static void f() {
                            List<Integer> m = []
                            m = null
                            m << 2
                        }
                    }''')],

        // Declared null: the value is known, not unmodelled (it said "no failing call")
        [group: "P420 reassigned nullity", name: "… and one declared null",
         expect: ["Cannot invoke method leftShift() on null object", "fails on: f()"],
         refute: "no failing call",
         src: tc('''class A {
                        static void f() {
                            List<Integer> xs = null
                            xs << 1
                        }
                    }''')],

        [group: "P420 reassigned nullity", name: "a map set to a parameter",
         expect: ["Cannot invoke method leftShift() on null object", "fails on: f(null)"],
         src: tc('''class A {
                        static void f(Map<String, Integer> p) {
                            Map<String, Integer> m = [:]
                            m = p
                            m << [b: 2]
                        }
                    }''')],

        // The call shown was f(new StringBuilder()), which doesn't fail
        [group: "P420 reassigned nullity", name: "a builder set to a parameter fails on its null",
         expect: ["Cannot invoke method append() on null object", "fails on: f(null)"],
         refute: "new StringBuilder()",
         src: tc('''class A {
                        static void f(StringBuilder p) {
                            StringBuilder m = new StringBuilder()
                            m = p
                            m.append('x')
                        }
                    }''')],

        [group: "P420 reassigned nullity", name: "… and a string",
         expect: ["Cannot invoke method length() on null object", "fails on: f(null)"],
         refute: 'f("")',
         src: tc('''class A {
                        static int f(String p) {
                            String s = 'abc'
                            s = p
                            return s.length()
                        }
                    }''')],

        [group: "P420 reassigned nullity", name: "a parameter the precondition rules non-null proves",
         ok: true,
         src: tc('''class A {
                        @Requires({ p != null })
                        static int f(List<Integer> p) {
                            List<Integer> m = [1]
                            m = p
                            return m.size()
                        }
                    }''')],

        [group: "P420 reassigned nullity", name: "… as does another literal",
         ok: true,
         src: tc('''class A {
                        static int f() {
                            Map<String, Integer> m = [:]
                            m = [a: 1]
                            return m.size()
                        }
                    }''')],

        // ── a call's value ──

        [group: "P420 reassigned nullity", name: "a String method's String is non-null",
         ok: true,
         src: tc('''class A {
                        @Requires({ p != null })
                        static int f(String p) {
                            String s = 'abc'
                            s = p.toUpperCase()
                            return s.length()
                        }
                    }''')],

        // A GDK method may give null (`'abc'.find(/x/)` is null): unknown, so no call is claimed
        [group: "P420 reassigned nullity", name: "… a GDK one's may be null",
         expect: ["Cannot invoke method length() on null object",
                  "no failing call: the failure rests on s, a value the verifier doesn't model"],
         refute: "(unmodelled)",
         src: tc('''class A {
                        @Requires({ p != null })
                        static int f(String p) {
                            String s = 'abc'
                            s = p.find(/x/)
                            return s.length()
                        }
                    }''')],

        // ── in a loop ──

        [group: "P420 reassigned nullity", name: "a loop that sets the local to null",
         expect: ["Cannot invoke method add() on null object", "fails on: f(2)"],
         src: tc('''class A {
                        static void f(int n) {
                            List<Integer> out = []
                            for (int k = 0; k < n; k++) {
                                out.add(k)
                                out = null
                            }
                        }
                    }''')],

        [group: "P420 reassigned nullity", name: "… a while loop's too",
         expect: ["Cannot invoke method add() on null object", "fails on: f(2)"],
         src: tc('''class A {
                        static void f(int n) {
                            List<Integer> out = []
                            int k = 0
                            while (k < n) {
                                out.add(k)
                                out = null
                                k++
                            }
                        }
                    }''')],

        [group: "P420 reassigned nullity", name: "a loop that only appends keeps it",
         ok: true,
         src: tc('''class A {
                        static int f(int n) {
                            List<Integer> out = []
                            for (int k = 0; k < n; k++) out.add(k)
                            return out.size()
                        }
                    }''')],
    ]
}
