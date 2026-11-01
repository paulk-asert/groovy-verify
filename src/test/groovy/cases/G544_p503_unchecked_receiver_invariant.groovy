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
 * 'P503 unchecked receiver invariant' — a write the model doesn't take, into a receiver's field its class invariant
 * reads ({@code b.xs.clear()} with {@code b} handed to a call, {@code b.names.add('x')} on a list of strings,
 * {@code b.m.put(k, v)}, a write through an alias, in a loop, an element store, a {@code <<}), owed nothing: a write
 * that broke the invariant compiled cleanly. Phase 501 models a direct write to a receiver's list, and the receiver
 * owes its invariant at the exit; any other such write is reported now, as the check it skips.
 */
class G544_p503_unchecked_receiver_invariant {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 503: a write the verifier doesn't model into a receiver's field its class invariant reads (`b.xs.clear(); h(b)`, `b.names.add('x')`, `b.m.put(k, v)`) says the invariant is unchecked, rather than compiling cleanly."

    static String client(String inv, String fields, String methods) { """@Invariant({ ${inv} })
                    final class B { ${fields} }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${methods}
                    }""" }

    static final List<Map> CASES = [

        // ---------- unmodelled writes: loud ----------
        [group: "P503 unchecked receiver invariant", name: "the receiver handed on", expect: ["Skipped the class invariant check of B for 'b' after 'b.xs.clear()' ('b' is also handed to 'h(b)')"],
         src: tc(client('xs != null && xs.size() > 0', 'List<Integer> xs', '''static void h(B b) { }
                        @Requires({ b != null })
                        static void f(B b) { b.xs.clear(); h(b) }'''))],
        [group: "P503 unchecked receiver invariant", name: "a list of strings", expect: ["Skipped the class invariant check of B for 'b' after 'b.names.add('x')' (the verifier doesn't model 'b.names' in f)"],
         src: tc(client('names != null && names.size() < 3', 'List<String> names', '''@Requires({ b != null })
                        static void f(B b) { b.names.add('x') }'''))],
        [group: "P503 unchecked receiver invariant", name: "a map", expect: ["Skipped the class invariant check of B for 'b' after 'b.m.put('a', 1)'"],
         src: tc(client('m != null && m.size() < 2', 'Map<String, Integer> m', '''@Requires({ b != null })
                        static void f(B b) { b.m.put('a', 1); b.m.put('b', 2) }'''))],
        [group: "P503 unchecked receiver invariant", name: "through an alias", expect: ["Skipped the class invariant check of B for 'b' after 'c.xs.clear()'"],
         src: tc(client('xs != null && xs.size() > 0', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { B c = b; c.xs.clear() }'''))],
        [group: "P503 unchecked receiver invariant", name: "in a loop", expect: ["Skipped the class invariant check of B for 'b' after 'b.xs.add(i)'"],
         src: tc(client('xs != null && xs.size() < 3', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { for (int i = 0; i < 5; i++) { b.xs.add(i) } }'''))],
        [group: "P503 unchecked receiver invariant", name: "with two receivers of the class", expect: ["Skipped the class invariant check of B for 'b' after 'b.xs.clear()'"],
         src: tc(client('xs != null && xs.size() > 0', 'List<Integer> xs', '''@Requires({ b != null && c != null })
                        static void f(B b, B c) { b.xs.clear() }'''))],
        [group: "P503 unchecked receiver invariant", name: "an element store", expect: ["Skipped the class invariant check of B for 'b' after 'b.xs[0] = -1'"],
         src: tc(client('xs != null && xs.size() > 0 && xs[0] >= 0', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { b.xs[0] = -1 }'''))],
        [group: "P503 unchecked receiver invariant", name: "a left shift", expect: ["Skipped the class invariant check of B for 'b' after 'b.names << 'x''"],
         src: tc(client('names != null && names.size() < 3', 'List<String> names', '''@Requires({ b != null })
                        static void f(B b) { b.names << 'x' }'''))],
        [group: "P503 unchecked receiver invariant", name: "once per field", expect: ["after 'b.names.add('x')'"], refute: "after 'b.names.add('y')'",
         src: tc(client('names != null && names.size() < 3', 'List<String> names', '''@Requires({ b != null })
                        static void f(B b) { b.names.add('x'); b.names.add('y') }'''))],

        // ---------- nothing to report ----------
        [group: "P503 unchecked receiver invariant", name: "a write the model takes is owed at the exit", ok: true,
         src: tc(client('xs != null && xs.size() > 0', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { b.xs.add(3) }'''))],
        [group: "P503 unchecked receiver invariant", name: "a read, the receiver handed on", ok: true,
         src: tc(client('xs != null && xs.size() > 0', 'List<Integer> xs', '''static void h(B b) { }
                        @Requires({ b != null })
                        static int f(B b) { int n = b.xs.size(); h(b); n }'''))],
        [group: "P503 unchecked receiver invariant", name: "a field the invariant doesn't read", ok: true,
         src: tc(client('n >= 0', 'List<Integer> xs; int n', '''static void h(B b) { }
                        @Requires({ b != null })
                        static void f(B b) { b.xs.clear(); h(b) }'''))],
    ]
}
