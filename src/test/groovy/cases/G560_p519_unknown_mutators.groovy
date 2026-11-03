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
 * 'P519 unknown mutators' — Phase 503 reported a write into a receiver's field its class invariant reads, but knew a
 * write only by a list of mutators' names ({@code add}, {@code clear}, {@code put}, …). Any other compiled cleanly where
 * it broke the invariant: {@code b.sb.append(…)}, {@code b.xs.removeIf { … }}, {@code b.xs.sort()}, a closure's
 * delegate ({@code b.xs.with { add(1) }}), and the field handed to a call that writes it ({@code Collections.sort(b.xs)},
 * {@code Arrays.fill(b.a, 7)}). Now any call on the field but a known read is a write, a view's is its field's, and a
 * field handed to one of this unit's methods (not {@code @Pure}) or to a JDK static that writes its argument is too.
 */
class G560_p519_unknown_mutators {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 519: any call on a receiver's field its invariant reads, but a known read, says the invariant is unchecked; so does handing the field to a call that may write it."

    static String client(String inv, String fields, String methods) { """@Invariant({ ${inv} })
                    final class B { ${fields} }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${methods}
                    }""" }

    static final String G = "P519 unknown mutators"
    static String skipped(String call, String why) { "Skipped the class invariant check of B for 'b' after '${call}' (${why})" }

    static final List<Map> CASES = [
        // ---------- unknown mutators: loud now ----------
        [group: G, name: "a StringBuilder appended", expect: [skipped("b.sb.append('xxxx')", "the verifier doesn't model 'b.sb' in f")],
         src: tc(client('sb != null && sb.length() < 3', 'StringBuilder sb', '''@Requires({ b != null })
                        static void f(B b) { b.sb.append('xxxx') }'''))],
        [group: G, name: "… its length set", expect: [skipped("b.sb.setLength(9)", "the verifier doesn't model 'b.sb' in f")],
         src: tc(client('sb != null && sb.length() < 3', 'StringBuilder sb', '''@Requires({ b != null })
                        static void f(B b) { b.sb.setLength(9) }'''))],
        [group: G, name: "removeIf", expect: [skipped("b.xs.removeIf { true }", "the verifier doesn't model 'b.xs' in f")],
         src: tc(client('xs != null && xs.size() > 0', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { b.xs.removeIf { true } }'''))],
        [group: G, name: "a list sorted in place", expect: [skipped("b.xs.sort()", "the verifier doesn't model 'b.xs' in f")],
         src: tc(client('xs != null && (xs.size() < 2 || xs[0] >= xs[1])', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { b.xs.sort() }'''))],
        [group: G, name: "a closure's delegate", expect: [skipped("b.xs.with { add(1) }", "the verifier doesn't model 'b.xs' in f")],
         src: tc(client('xs != null && xs.size() < 1', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { b.xs.with { add(1) } }'''))],
        [group: G, name: "through a view", expect: [skipped("b.m.keySet().clear()", "the verifier doesn't model 'b.m' in f")],
         src: tc(client('m != null && m.size() > 0', 'Map<String, Integer> m', '''@Requires({ b != null })
                        static void f(B b) { b.m.keySet().clear() }'''))],
        // ---------- a field handed to a call that writes it ----------
        [group: G, name: "handed to Collections.sort", expect: [skipped("Collections.sort(b.xs)", "'b.xs' is handed to 'Collections.sort(b.xs)'")],
         src: tc(client('xs != null && (xs.size() < 2 || xs[0] >= xs[1])', 'List<Integer> xs', '''@Requires({ b != null })
                        static void f(B b) { Collections.sort(b.xs) }'''))],
        [group: G, name: "handed to Arrays.fill", expect: [skipped("Arrays.fill(b.a, 7)", "'b.a' is handed to 'Arrays.fill(b.a, 7)'")],
         src: tc(client('a != null && a.length > 0 && a[0] == 0', 'int[] a', '''@Requires({ b != null })
                        static void f(B b) { Arrays.fill(b.a, 7) }'''))],
        [group: G, name: "handed to arraycopy's destination", expect: [skipped("System.arraycopy(src, 0, b.a, 0, 1)", "'b.a' is handed to 'System.arraycopy(src, 0, b.a, 0, 1)'")],
         src: tc(client('a != null && a.length > 0 && a[0] == 0', 'int[] a', '''@Requires({ b != null && src != null && src.length > 0 })
                        static void f(B b, int[] src) { System.arraycopy(src, 0, b.a, 0, 1) }'''))],
        [group: G, name: "handed to a method of this unit", expect: [skipped("h(b.xs)", "'b.xs' is handed to 'h(b.xs)'")],
         src: tc(client('xs != null && xs.size() < 1', 'List<Integer> xs', '''static void h(List<Integer> ys) { ys?.add(1) }
                        @Requires({ b != null })
                        static void f(B b) { h(b.xs) }'''))],
        // ---------- reads: nothing to report ----------
        [group: G, name: "reads, unreported", ok: true,
         src: tc(client('xs != null && xs.size() > 0', 'List<Integer> xs', '''@Requires({ b != null })
                        static int f(B b) { int n = 0; b.xs.each { n += it }; b.xs.size() + (b.xs.contains(1) ? 1 : 0) + n }'''))],
        [group: G, name: "a StringBuilder read", ok: true,
         src: tc(client('sb != null && sb.length() < 3', 'StringBuilder sb', '''@Requires({ b != null })
                        static String f(B b) { b.sb.toString() }'''))],
        [group: G, name: "handed to a @Pure method", ok: true,
         src: tc(client('xs != null && xs.size() < 1', 'List<Integer> xs', '''@Pure static int h(List<Integer> ys) { 0 }
                        @Requires({ b != null })
                        static int f(B b) { h(b.xs) }'''))],
        [group: G, name: "… its list still modelled", ok: true,
         src: tc(client('xs != null && xs.size() < 3', 'List<Integer> xs', '''@Pure static int h(List<Integer> ys) { 0 }
                        @Requires({ b != null })
                        static void f(B b) { h(b.xs); b.xs.clear() }'''))],
        [group: G, name: "an argument a JDK method reads", ok: true,
         src: tc(client('xs != null && xs.size() < 1', 'List<Integer> xs', '''@Requires({ b != null })
                        static int f(B b) { List<Integer> ys = new ArrayList<Integer>(); ys.addAll(b.xs); ys.size() }'''))],
        [group: G, name: "an immutable field handed on", ok: true,
         src: tc(client('name != null && name.length() < 3', 'String name', '''static int h(String s) { s?.length() ?: 0 }
                        @Requires({ b != null })
                        static int f(B b) { h(b.name) }'''))],
    ]
}
