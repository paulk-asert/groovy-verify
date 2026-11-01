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
 * 'P502 unmodelled list index' — a List call that throws for its index, or on an empty list ({@code get(i)},
 * {@code removeAt(i)}, {@code set(i, v)}, {@code add(i, v)}, {@code first()}, {@code last()}, {@code pop()}, …), on a
 * list that isn't a name the verifier models — a receiver's field it doesn't model ({@code b.xs} of a receiver handed
 * to a call, a {@code List<String>} one), a call's result, an element of a nested list — had no obligation, and said
 * nothing. Loud now, as Phase 408 made an unmodelled array's index. {@code this.xs.get(i)} is the field's, checked;
 * a literal's read in bounds by its length ({@code [1, 2, 3].first()}) needs no report.
 */
class G543_p502_unmodelled_list_index {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 502: a throwing List index call (`get`, `first`, `pop`, …) on a list the verifier doesn't model — `b.xs` it can't model, `f()`, `xss[0]` — says it's unchecked; `this.xs.get(i)` is checked as the field's."

    static final List<Map> CASES = [

        // ---------- unmodelled: loud ----------
        [group: "P502 unmodelled list index", name: "a receiver's list, the receiver handed to a call", expect: ["Skipped list index safety check ('b.xs.get(1)' indexes the list 'b.xs'"],
         src: tc('''@Invariant({ xs != null })
                    final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        static void h(B b) { }
                        @Requires({ b != null })
                        static Integer f(B b) { h(b); b.xs.get(1) }
                    }''')],
        [group: "P502 unmodelled list index", name: "… of two receivers of the class", expect: ["Skipped list index safety check ('b.xs.first()' indexes the list 'b.xs'"],
         src: tc('''final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        @Requires({ b != null && c != null })
                        static Integer f(B b, B c) { b.xs.first() }
                    }''')],
        [group: "P502 unmodelled list index", name: "… of strings", expect: ["Skipped list index safety check ('b.names.get(3)' indexes the list 'b.names'"],
         src: tc('''final class B { List<String> names }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        @Requires({ b != null })
                        static String f(B b) { b.names.get(3) }
                    }''')],
        [group: "P502 unmodelled list index", name: "a call's result", expect: ["Skipped list index safety check ('g().get(5)' indexes the list 'g()'"],
         src: tc('''class C {
                        static List<Integer> g() { [1] }
                        static Integer f() { g().get(5) }
                    }''')],
        [group: "P502 unmodelled list index", name: "a nested list's element", expect: ["Skipped list index safety check ('xss[0].get(5)' indexes the list 'xss[0]'"],
         src: tc('''class C {
                        @Requires({ xss != null && xss.size() > 0 && xss[0] != null })
                        static Integer f(List<List<Integer>> xss) { xss[0].get(5) }
                    }''')],
        [group: "P502 unmodelled list index", name: "a removal from one", expect: ["Skipped list index safety check ('g().pop()' indexes the list 'g()'"],
         src: tc('''class C {
                        static List<Integer> g() { [1] }
                        static Integer f() { g().pop() }
                    }''')],
        [group: "P502 unmodelled list index", name: "a literal's read past its end", expect: ["Skipped list index safety check ('[10, 20].get(2)' indexes the list '[10, 20]'"],
         src: tc('''class C {
                        static Integer f() { [10, 20].get(2) }
                    }''')],

        // ---------- modelled, or decided ----------
        [group: "P502 unmodelled list index", name: "this.xs is the field's", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 5 && 5 < xs.size()'],
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        Integer f() { this.xs.get(5) }
                    }''')],
        [group: "P502 unmodelled list index", name: "… and in bounds by the precondition", ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 5 })
                        Integer f() { this.xs.get(5) }
                    }''')],
        [group: "P502 unmodelled list index", name: "a literal's read in bounds", ok: true,
         src: tc('''class C {
                        @Ensures({ result == 50 })
                        static int f() { [10, 20].get(1) + [10, 20].first() + List.of(10, 20).last() }
                    }''')],
        [group: "P502 unmodelled list index", name: "a modelled receiver's list is checked, not skipped", expect: ['Possible IndexOutOfBoundsException', 'obligation: 0 <= 1 && 1 < b.xs.size()'],
         src: tc('''final class B { List<Integer> xs }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        @Requires({ b != null && b.xs != null })
                        static Integer f(B b) { b.xs.get(1) }
                    }''')],
        [group: "P502 unmodelled list index", name: "a call that doesn't index isn't reported", ok: true,
         src: tc('''class C {
                        static List<Integer> g() { [1] }
                        static int f() { g().size() }
                    }''')],
        [group: "P502 unmodelled list index", name: "… nor a map's get", ok: true,
         src: tc('''class C {
                        static Map<String, Integer> g() { [a: 1] }
                        static Integer f() { g().get('a') }
                    }''')],
    ]
}
