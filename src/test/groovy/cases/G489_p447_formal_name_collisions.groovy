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
 * 'P447 formal name collisions' — a callee's contract is read in the caller's encoder, where a name's oracles (its
 * nullity, size, contents, set, map) are keyed by the name. A formal's value went through bindings, but those oracles
 * didn't: a formal named like one of the caller's variables read that variable's. `@Ensures({ s != null })` on a
 * formal `s` made the caller's own `s` non-null, and a caller's `s != null` discharged a callee's `@Requires({ s !=
 * null })` about another argument. A formal's oracles are fresh now (shadowed), and tied to the actual's.
 */
class G489_p447_formal_name_collisions {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 447: a callee's formal named like one of the caller's variables no longer reads that variable's nullity, set or map (each compiled clean — unsound); set and map formals are the actual's; a String-keyed map's havoc keeps its sorts, and an internal error in the implicit checks is reported instead of dropping them."

    static final List<Map> CASES = [

        // Unsound before: each compiled clean
        [group: "P447 formal name collisions", name: "a callee's @Ensures about its formal s isn't the caller's s",
         expect: "Possible NullPointerException",
         src: tc('''class A {
                        @Requires({ a != null })
                        static int f(String a, String s) { g(a); s.size() }
                        @Requires({ s != null })
                        @Ensures({ s != null })
                        static void g(String s) { }
                    }''')],

        [group: "P447 formal name collisions", name: "… nor a caller's s the callee's @Requires about its own",
         expect: "Cannot prove precondition of g at this call site",
         src: tc('''class A {
                        @Requires({ s != null })
                        static int f(String a, String s) { g(a) }
                        @Requires({ s != null })
                        static int g(String s) { s.size() }
                    }''')],

        [group: "P447 formal name collisions", name: "… for a set",
         expect: "Cannot prove precondition of g at this call site",
         src: tc('''class A {
                        @Requires({ a != null && s != null && s.contains(5) })
                        static void f(Set<Integer> a, Set<Integer> s) { g(a) }
                        @Requires({ s != null && s.contains(5) })
                        static void g(Set<Integer> s) { }
                    }''')],

        [group: "P447 formal name collisions", name: "… a written set",
         expect: "Assertion may not hold: s.contains(5)",
         src: tc('''class A {
                        @Requires({ a != null && s != null })
                        static void f(Set<Integer> a, Set<Integer> s) { g(a); assert s.contains(5) }
                        @Requires({ s != null })
                        @Ensures({ s.contains(5) })
                        static void g(Set<Integer> s) { s.add(5) }
                    }''')],

        [group: "P447 formal name collisions", name: "… a written map",
         expect: "Assertion may not hold: m.containsKey('k')",
         src: tc('''class A {
                        @Requires({ a != null && m != null })
                        static void f(Map<String, Integer> a, Map<String, Integer> m) { g(a); assert m.containsKey('k') }
                        @Requires({ m != null })
                        @Ensures({ m.containsKey('k') })
                        static void g(Map<String, Integer> m) { m.put('k', 1) }
                    }''')],

        // The actual is what the formal's contract is about
        [group: "P447 formal name collisions", name: "a written map's @Ensures is about the actual", ok: true,
         src: tc('''class A {
                        @Requires({ a != null })
                        static void f(Map<String, Integer> a) { g(a); assert a.containsKey('k') }
                        @Requires({ m != null })
                        @Ensures({ m.containsKey('k') })
                        static void g(Map<String, Integer> m) { m.put('k', 1) }
                    }''')],

        // Unsound before: the String-keyed map's havoc had an Int-sorted key-set, `containsKey('zz')` threw, and the
        // implicit checks were dropped without a word — the assertion "proved"
        [group: "P447 formal name collisions", name: "… and only what it promises",
         expect: "Assertion may not hold: a.containsKey('zz')",
         src: tc('''class A {
                        @Requires({ a != null })
                        static void f(Map<String, Integer> a) { g(a); assert a.containsKey('zz') }
                        @Requires({ m != null })
                        @Ensures({ m.containsKey('k') })
                        static void g(Map<String, Integer> m) { m.put('k', 1) }
                    }''')],

        // A false alarm before: the set formal had nothing of the actual's
        [group: "P447 formal name collisions", name: "a caller's set discharges a callee's @Requires about it", ok: true,
         src: tc('''class A {
                        @Requires({ a != null && a.contains(5) })
                        static void f(Set<Integer> a) { g(a) }
                        @Requires({ s != null && s.contains(5) })
                        static void g(Set<Integer> s) { }
                    }''')],
    ]
}
