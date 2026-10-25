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
 * 'P418 call statement survival' — Phase 415 let an assignment's right side and a condition taken leave what they
 * dereference non-null after them, for the calls Phase 414 measured as throwing on null (`size`, `get`, …). A call on
 * its own line left nothing, so `xs.clear(); xs.size()` reported its null twice. A call statement the path moved past
 * leaves its receiver non-null now, until it's rebound.
 *
 * Which calls count is measured too: dispatched dynamically, a null receiver answers `Object`'s own methods and the
 * GDK's whose receiver is `Object` (`null.each { }` is null, `null.with { 1 }` is 1), read from the runtime's GDK
 * classes; any other call throws ("Cannot invoke method clear() on null object"), and counts — in an assignment and a
 * precondition as well (`@Requires({ xs.containsAll(ys) })` admits no null `xs`).
 */
class G460_p418_call_statement_survival {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 418: a call statement the path moved past leaves its receiver non-null until it's rebound, so a null reports once, at its first call; a call counts when it throws on a null receiver (not `Object`'s methods or the GDK's on `Object`, which null answers), in an assignment and a precondition too."

    static final List<Map> CASES = [

        // Reported twice before: at clear() and again at size()
        [group: "P418 call statement survival", name: "a call statement leaves its receiver non-null",
         expect: ["Cannot invoke method clear() on null object", "fails on: f(null)"],
         refute: "size()",
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            xs.clear()
                            return xs.size()
                        }
                    }''')],

        [group: "P418 call statement survival", name: "… a builder's too",
         expect: ["Cannot invoke method append() on null object", "@ line 5"],
         refute: "@ line 6",
         src: tc('''class A {
                        static void f(StringBuilder sb) {
                            sb.append('x')
                            sb.append('y')
                        }
                    }''')],

        [group: "P418 call statement survival", name: "… and an assignment's call that Phase 414 didn't list",
         expect: ["Cannot invoke method add() on null object"],
         refute: "size()",
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            boolean b = xs.add(1)
                            return xs.size()
                        }
                    }''')],

        [group: "P418 call statement survival", name: "a precondition's call that throws on null admits none",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs.containsAll([1]) })
                        static int f(List<Integer> xs) { xs.size() }
                    }''')],

        // ── what doesn't count ──

        // `null.each { }` is null, dispatched dynamically: the size() is the first dereference
        [group: "P418 call statement survival", name: "a call null answers leaves nothing",
         expect: ["Cannot invoke method size() on null object", "fails on: f(null)"],
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            xs.each { }
                            return xs.size()
                        }
                    }''')],

        // `null.with { true }` is true, so the precondition admits a null (it's outside the model, so no call is shown)
        [group: "P418 call statement survival", name: "… nor in a precondition",
         expect: ["Cannot invoke method size() on null object", "obligation: xs != null",
                  "no failing call: the precondition's 'xs.with({ ... })' is outside what the verifier models"],
         src: tc('''class A {
                        @Requires({ xs.with { true } })
                        static int f(List<Integer> xs) { xs.size() }
                    }''')],

        [group: "P418 call statement survival", name: "a rebinding after the call still refutes",
         expect: ["Cannot invoke method size() on null object", "@ line 7"],
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            xs.clear()
                            xs = null
                            return xs.size()
                        }
                    }''')],

        // On the path that skips it, nothing was dereferenced
        [group: "P418 call statement survival", name: "a call in one branch leaves the other's null",
         expect: ["fails on: f(null, true)", "fails on: f(null, false)"],
         src: tc('''class A {
                        static int f(List<Integer> xs, boolean c) {
                            if (c) xs.clear()
                            return xs.size()
                        }
                    }''')],
    ]
}
