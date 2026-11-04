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
 * 'P526 null receiver field' — a receiver's field of a reference type other than an enum ({@code b.s}, a String; a
 * boxed {@code Integer}; an object) compared with null ({@code b.s == null}) wasn't translated: the contract was
 * outside the fragment. Now it reads the field's flag {@code b$s}, the one the receiver's invariant constrains, and a
 * refutation builds the receiver: {@code fails on: f(new B())}.
 */
class G567_p526_null_receiver_field {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 526: a receiver's String, boxed or object field compared with null reads the field's own nullity, under the receiver's invariant."

    static final String G = "P526 null receiver field"
    static String client(String inv, String methods) { """${inv ? "@Invariant({ ${inv} })" : ''}
                    final class B { String s; Integer n; B next }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class Client {
                        ${methods}
                    }""" }

    static final List<Map> CASES = [
        [group: G, name: "a null String field, in a body", ok: true,
         src: tc(client(null, '''@Requires({ b != null && b.s == null })
                        @Ensures({ !result })
                        static boolean f(B b) { b.s != null }'''))],
        [group: G, name: "non-null, refuted on a fresh receiver", expect: ['Cannot prove postcondition', 'fails on: f(new B())'],
         src: tc(client(null, '''@Requires({ b != null })
                        @Ensures({ b.s != null })
                        static void f(B b) { }'''))],
        [group: G, name: "… non-null by its invariant", ok: true,
         src: tc(client('s != null', '''@Requires({ b != null })
                        @Ensures({ b.s != null })
                        static void f(B b) { }'''))],
        [group: G, name: "… non-null by the precondition", ok: true,
         src: tc(client(null, '''@Requires({ b != null && b.s != null })
                        @Ensures({ result })
                        static boolean f(B b) { b.s != null }'''))],
        [group: G, name: "a boxed field, null", ok: true,
         src: tc(client(null, '''@Requires({ b != null && b.n == null })
                        @Ensures({ result })
                        static boolean f(B b) { b.n == null }'''))],
        [group: G, name: "… non-null, refuted", expect: ['Cannot prove postcondition', 'fails on: f(new B())'],
         src: tc(client(null, '''@Requires({ b != null })
                        @Ensures({ b.n != null })
                        static void f(B b) { }'''))],
        [group: G, name: "an object field, null", ok: true,
         src: tc(client(null, '''@Requires({ b != null && b.next == null })
                        @Ensures({ !result })
                        static boolean f(B b) { b.next != null }'''))],
        [group: G, name: "… non-null by its invariant", ok: true,
         src: tc(client('next != null', '''@Requires({ b != null })
                        @Ensures({ b.next != null })
                        static void f(B b) { }'''))],
        [group: G, name: "a String field equal to a literal is non-null", ok: true,
         src: tc(client(null, '''@Requires({ b != null && b.s == 'x' })
                        @Ensures({ b.s != null })
                        static void f(B b) { }'''))],
        [group: G, name: "the field's null in a body's guard", ok: true,
         src: tc(client(null, '''@Requires({ b != null })
                        @Ensures({ result >= 0 })
                        static int f(B b) { b.s == null ? 0 : b.s.length() }'''))],
    ]
}
