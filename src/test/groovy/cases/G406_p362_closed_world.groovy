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
 * 'P362 the closed world, opted into and ledgered' — Phases 360/361 made the open world the default: an
 * overridable body is neither a call's frame nor its value, and a field of an open class is read through a getter a
 * subclass may override. A class that wants the earlier precision — its subclasses are known, or are proxies that
 * delegate — now says so: `@TypeChecked(extensions = 'verification.VerifyChecker(closedWorld: true)')`. Its proofs
 * rely on the body or the field as written, and each reliance is a TrustLedger fact of kind `closed world` (Phase
 * 216), anchored at the method that relies on it: VERIFY_TRUST=report lists the obligations a subclass's author takes
 * on, and deny fails the build on them. What the unit can see is still checked: an override in the unit (Phase 359)
 * and a declared accessor (Phase 361) count as before.
 */
class G406_p362_closed_world {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 362 the closed world, opted into and ledgered: `VerifyChecker(closedWorld: true)` lets a class\'s proofs rely on an overridable method\'s body (its frame and its value) and on an open class\'s field as written, each reliance a `closed world` TrustLedger fact at the relying method, so VERIFY_TRUST=report lists the obligations a subclass\'s author takes on and deny fails on them; overrides and accessors in the unit are still checked, and the option is per class.'

    static final List<Map> CASES = [

        [group: "P362 the closed world, opted into and ledgered", name: "an open class's writer is framed by its body, and ledgered", ok: true,
         trusted: "[closed world] Counter#incr — frame read off its body [count]: a subclass compiled elsewhere must write no more",
         src: tcw('''class A {
                        @Requires({ c != null && c.count == 0 && c.total == 7 })
                        @Ensures({ c.total == 7 })
                        static void g(Counter c) { c.incr() }
                    }
                    class Counter { int count; int total; void incr() { count = count + 1 } }''')],
        [group: "P362 the closed world, opted into and ledgered", name: "… and its fields are read as the fields, ledgered too", ok: true,
         trusted: "[closed world] Counter#total — read as the field: a subclass compiled elsewhere must not declare getTotal()",
         src: tcw('''class A {
                        @Requires({ c != null && c.count == 0 && c.total == 7 })
                        @Ensures({ c.total == 7 })
                        static void g(Counter c) { c.incr() }
                    }
                    class Counter { int count; int total; void incr() { count = count + 1 } }''')],
        [group: "P362 the closed world, opted into and ledgered", name: "an open helper's body is its value, ledgered", ok: true,
         trusted: "[closed world] Base#get — body used as its value: a subclass compiled elsewhere must not override it",
         src: tcw('''class Base {
                        int get() { 0 }
                        @Ensures({ result == 0 })
                        int foo() { get() }
                    }''')],
        // The method under check is not a reliance: only a call relies on a callee's body.
        [group: "P362 the closed world, opted into and ledgered", name: "only a call's reliance is ledgered", ok: true,
         untrusted: "Base#foo",
         src: tcw('''class Base {
                        int get() { 0 }
                        @Ensures({ result == 0 })
                        int foo() { get() }
                    }''')],
        [group: "P362 the closed world, opted into and ledgered", name: "VERIFY_TRUST=deny fails on a reliance, at the relying method", trustMode: 'deny',
         expect: "Trusted without proof (VERIFY_TRUST=deny): [closed world] Box#n — read as the field: a subclass compiled elsewhere must not declare getN()",
         src: tcw('''class A {
                        @Requires({ b != null && b.n == 3 })
                        @Ensures({ result == 3 })
                        static int f(Box b) { b.n }
                    }
                    class Box { int n }''')],
        [group: "P362 the closed world, opted into and ledgered", name: "an override in the unit still counts", expect: "Cannot prove postcondition of g",
         src: tcw('''class A {
                        static int peek(Base h) { h == null ? 0 : h.get() }
                        @Requires({ s != null && s.n == 0 })
                        @Ensures({ s.n == 0 })
                        static void g(Sub s) { peek(s) }
                    }
                    class Base { int get() { 0 } }
                    class Sub extends Base { int n; int get() { n = n + 1; return n } }''')],
        [group: "P362 the closed world, opted into and ledgered", name: "… as does a getter a subclass in the unit declares",
         expect: "Groovy reads 'n' through 'Sub.getN(…)', a user getter that isn't the field",
         src: tcw('''class A {
                        @Requires({ b != null && b.n == 3 })
                        @Ensures({ result == 3 })
                        static int f(Box b) { b.n }
                    }
                    class Box { int n }
                    class Sub extends Box { int getN() { 7 } }''')],
        [group: "P362 the closed world, opted into and ledgered", name: "the option is per class",
         expect: "'Counter.incr(…)' can be overridden by a subclass compiled elsewhere, so its body isn't its frame",
         src: tcw('''class A {
                        static int one() { 1 }
                    }
                    @TypeChecked(extensions = 'verification.VerifyChecker')
                    final class B {
                        @Requires({ c != null && a != null && a.length > 0 && a[0] == 7 })
                        @Ensures({ a[0] == 7 })
                        static void g(Counter c, int[] a) { c.incr() }
                    }
                    class Counter { int count; void incr() { count = count + 1 } }''')],
    ]
}
