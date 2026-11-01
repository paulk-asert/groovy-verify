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
 * 'P497 shadowed fields' — a field and a parameter or local of the same name were one SMT value: the encoder names a
 * field by its own name, as it does the parameter. So a class invariant's {@code count >= 0} proved
 * {@code f(int count)}'s PARAMETER non-negative, a callee's {@code @Requires({ v == 5 })} on the field was met by the
 * caller's parameter {@code v}, and {@code this.count = 3; count} returned 3. A method whose checks use a shadowed
 * field is refused, loudly; one that only shadows it is checked as before, as is the constructor idiom
 * ({@code this.count = count} first, the parameter never reassigned), where field and parameter are one value.
 */
class G538_p497_shadowed_field {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 497: a method whose checks use a field a parameter or local shadows — through the class invariant, `this.f`, or a callee's contract — is refused rather than read the parameter as the field; the constructor idiom `this.f = f` still verifies."

    static final List<Map> CASES = [

        // ---------- what read the parameter as the field ----------
        [group: "P497 shadowed fields", name: "a class invariant's field", expect: ["field 'count' is shadowed by a parameter of f, and the class invariant uses the field"],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Ensures({ result })
                        boolean f(int count) { count >= 0 }
                    }''')],
        [group: "P497 shadowed fields", name: "a callee's precondition on the field", expect: ["field 'v' is shadowed by a parameter of f, and g's contract uses the field"],
         src: tc('''class A {
                        int v
                        @Requires({ v == 5 })
                        void g() { }
                        void f(int v) { if (v == 5) g() }
                    }''')],
        [group: "P497 shadowed fields", name: "… a static callee's, on a static field", expect: ["field 'v' is shadowed by a parameter of f, and g's contract uses the field"],
         src: tc('''class A {
                        static int v
                        @Requires({ v == 5 })
                        static void g() { }
                        static void f(int v) { if (v == 5) g() }
                    }''')],
        [group: "P497 shadowed fields", name: "this.count, beside the parameter", expect: ["field 'count' is shadowed by a parameter of f, and this.count uses the field"],
         src: tc('''class A {
                        int count
                        @Ensures({ result == 3 })
                        int f(int count) { this.count = 3; count }
                    }''')],
        [group: "P497 shadowed fields", name: "… in the postcondition", expect: ["field 'count' is shadowed by a parameter of f, and this.count uses the field"],
         src: tc('''class A {
                        int count
                        @Ensures({ this.count == count })
                        void f(int count) { }
                    }''')],
        [group: "P497 shadowed fields", name: "a local's", expect: ["field 'count' is shadowed by a local of f, and the class invariant uses the field"],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Ensures({ result })
                        boolean f() { int count = -1; count < 0 }
                    }''')],
        [group: "P497 shadowed fields", name: "a setter's, under the invariant", expect: ["field 'count' is shadowed by a parameter of set, and this.count uses the field"],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        void set(int count) { this.count = count }
                    }''')],
        [group: "P497 shadowed fields", name: "a constructor's second write", expect: ["field 'count' is shadowed by a parameter of <init>, and this.count uses the field"],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Requires({ count >= 0 })
                        A(int count) { this.count = count; this.count = -1 }
                    }''')],
        [group: "P497 shadowed fields", name: "… or a reassigned parameter", expect: ["field 'count' is shadowed by a parameter of <init>, and this.count uses the field"],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Requires({ count >= 0 })
                        A(int count) { this.count = count; count = -1 }
                    }''')],

        // ---------- shadowing that reads no field ----------
        [group: "P497 shadowed fields", name: "a shadow no check reads the field through", ok: true,
         src: tc('''class A {
                        int count
                        @Requires({ count > 0 })
                        @Ensures({ result > 1 })
                        int f(int count) { count + 1 }
                    }''')],
        [group: "P497 shadowed fields", name: "… nor a static method's, under the invariant", ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Ensures({ result })
                        static boolean f(int count) { count >= 0 || count < 0 }
                    }''')],
        [group: "P497 shadowed fields", name: "… nor an instance callee's own formal", ok: true,
         src: tc('''class A {
                        int v
                        @Requires({ v == 5 })
                        void g(int v) { }
                        void f(int v) { if (v == 5) g(v) }
                    }''')],
        [group: "P497 shadowed fields", name: "… nor a callee's own formal", ok: true,
         src: tc('''class A {
                        int v
                        @Requires({ v == 5 })
                        static void g(int v) { }
                        static void f(int v) { if (v == 5) g(v) }
                    }''')],
        [group: "P497 shadowed fields", name: "the constructor idiom: a parameter copied in first", ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Requires({ count >= 0 })
                        A(int count) { this.count = count }
                    }''')],
        [group: "P497 shadowed fields", name: "… which the invariant still holds to", expect: ['invariant'],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        A(int count) { this.count = count }
                    }''')],
        [group: "P497 shadowed fields", name: "… but not with a call that writes the field", expect: ["field 'count' is shadowed by a parameter of <init>, and this.count uses the field"],
         src: tc('''class A {
                        int count
                        @Modifies({ this.count })
                        @Ensures({ count == old.count + 1 })
                        void bump() { count++ }
                        @Requires({ count >= 0 })
                        A(int count) { this.count = count; bump(); assert count > 0 }
                    }''')],
        [group: "P497 shadowed fields", name: "… and whose 0 isn't the parameter's", expect: ['Cannot prove postcondition'],
         src: tc('''class A {
                        int count
                        @Ensures({ count == 0 })
                        A(int count) { }
                    }''')],
        [group: "P497 shadowed fields", name: "an unshadowed field still reads", ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Ensures({ result })
                        boolean f(int n) { count >= 0 }
                    }''')],
    ]
}
