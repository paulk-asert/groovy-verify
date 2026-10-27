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
 * 'P433 a written parameter owes its invariant' — Phase 432 declined a write through an object parameter whose class
 * declares an `@Invariant`: the invariant is assumed of the parameter at entry (Phase 45) and by every later method
 * handed it, and nothing re-proved it after the write. A method with no `@Ensures` wasn't checked at all, so its write
 * broke the invariant silently.
 *
 * The parameter's class invariant is now an exit obligation of every path that wrote through it — with or without an
 * `@Ensures` — reported as its own (`Cannot prove class invariant of C holds for 'c' at exit of f`) when the method's
 * own goal holds. A call handed the parameter after a write is declined: it would assume the invariant mid-update.
 */
class G475_p433_param_invariant_after_write {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 433: a write through an object parameter whose class declares an @Invariant re-proves that invariant at the method's exit — with or without an @Ensures, where it was declined (or, without one, unchecked) — and refutes as `Cannot prove class invariant of C holds for 'c' at exit of f`; a call handed the parameter is declined."

    static final List<Map> CASES = [

        // Declined in Phase 432
        [group: "P433 a written parameter owes its invariant", name: "writes that keep it prove",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ c.n == 1 })
                        static void f(C c) { c.hi = 1; c.n = 1 }
                        @Requires({ c != null && p >= 0 })
                        static void g(C c, int p) { c.n = p; c.hi = p }
                        @Requires({ c != null && p >= 0 })
                        static void both(C c, int p) { c.hi = p + 1; c.n = p; c.hi = c.n }
                    }
                    @Invariant({ n >= 0 && n <= hi })
                    final class C { int n; int hi }''')],

        // Unchecked before: no @Ensures, so the method never reached the postcondition path
        [group: "P433 a written parameter owes its invariant", name: "a write that breaks it refutes, @Ensures or not",
         expect: ["Cannot prove class invariant of C holds for 'c' at exit of h, after a write through it",
                  "invariant: (n >= 0)", "fails on: h(new C(n: 0), -"],
         src: tc('''class A {
                        @Requires({ c != null })
                        static void h(C c, int p) { c.n = p }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],

        // The method's own goal holds, so the invariant is named, not the postcondition
        [group: "P433 a written parameter owes its invariant", name: "… named as the invariant beside a kept @Ensures",
         expect: "Cannot prove class invariant of C holds for 'c' at exit of k",
         refute: "Cannot prove postcondition of k",
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ c.n == -1 })
                        static void k(C c) { c.n = -1 }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],

        [group: "P433 a written parameter owes its invariant", name: "a broken @Ensures is still the postcondition",
         expect: ["Cannot prove postcondition of k", "ensured: (c.n == 2)"],
         refute: "class invariant of C",
         src: tc('''class A {
                        @Requires({ c != null })
                        @Ensures({ c.n == 2 })
                        static void k(C c) { c.n = 1 }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],

        // The intermediate state needn't meet it, only the exit
        [group: "P433 a written parameter owes its invariant", name: "only the exit owes it",
         ok: true,
         src: tc('''class A {
                        @Requires({ c != null })
                        static void q(C c) { c.n = -1; c.n = 3 }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],

        [group: "P433 a written parameter owes its invariant", name: "a call handed the parameter is declined",
         expect: "field write 'c.n = 1' is outside fragment — 'C' declares an @Invariant, which the call 'this.println(c)' would assume of 'c' while the write may have broken it",
         src: tc('''class A {
                        @Requires({ c != null })
                        static void cl(C c) { c.n = 1; println(c) }
                    }
                    @Invariant({ n >= 0 })
                    final class C { int n }''')],
    ]
}
