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

/** 'P309 call results as arguments' — a contracted call's result reaching ANOTHER call's @Requires, either through a
 *  local (`int c = f(n); g(c)`) or directly (`g(f(n))`). Shared import header and wrappers come from {@link CaseDsl}. */
class G353_p309_call_result_args {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A contracted call\'s result passed on to another call — via a local or directly — carries the first callee\'s @Ensures into the second callee\'s @Requires check; a too-weak or missing @Ensures still refutes.'

    static final List<Map> CASES = [
        // ---------- Phase 309: call results as arguments ----------
        // The call-site precondition check replays the straight-line prefix to the call (Phase 24). A scalar local
        // bound from a contracted call used to be havoc'd there, so f's `result >= 0` never reached g's
        // `@Requires({ z >= 0 })` — a spurious refute at the n = Integer.MIN_VALUE corner the havoc left open. The
        // replay now assumes the callee's @Ensures for the local, as the postcondition path always has.
        [group: 'P309 call results as arguments', name: 'local bound from a call discharges the next precondition', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int n) { n >= 0 ? n : 0 }
                        @Requires({ z >= 0 })
                        static int g(int z) { z }
                        static int h(int n) { int c = f(n); return g(c) }
                    }''')],
        // Reassignment rather than declaration takes the same route.
        [group: 'P309 call results as arguments', name: 'reassigned local from a call discharges the next precondition', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int n) { n >= 0 ? n : 0 }
                        @Requires({ z >= 0 })
                        static int g(int z) { z }
                        static int h(int n) { int c = -1; c = f(n); return g(c) }
                    }''')],
        // The direct form: the argument IS the call. Previously skipped as "outside fragment".
        [group: 'P309 call results as arguments', name: 'nested call argument discharges the outer precondition', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int n) { n >= 0 ? n : 0 }
                        @Requires({ z >= 0 })
                        static int g(int z) { z }
                        static int h(int n) { g(f(n)) }
                    }''')],
        // A boolean result carries the same way.
        [group: 'P309 call results as arguments', name: 'boolean call result discharges a boolean precondition', ok: true,
         src: tc('''class C {
                        @Ensures({ result == (n > 0) })
                        static boolean pos(int n) { n > 0 }
                        @Requires({ ok ==> n > 0 })
                        static int g(boolean ok, int n) { ok ? n : 1 }
                        static int h(int n) { boolean p = pos(n); return g(p, n) }
                    }''')],
        // Refute control: the callee's @Ensures is too weak to give the precondition, so it must still refute —
        // the fix assumes what f promises, nothing more.
        [group: 'P309 call results as arguments', name: 'too-weak callee ensures still refutes', expect: 'Cannot prove precondition of g',
         src: tc('''class C {
                        @Ensures({ result >= -1 })
                        static int f(int n) { n >= 0 ? n : -1 }
                        @Requires({ z >= 0 })
                        static int g(int z) { z }
                        static int h(int n) { int c = f(n); return g(c) }
                    }''')],
        // Refute control: no @Ensures, and a body that really can go negative (an uncontracted callee's body is
        // read, so `n >= 0 ? n : 0` would — correctly — prove; this one must not).
        [group: 'P309 call results as arguments', name: 'uncontracted callee that can go negative refutes', expect: 'Cannot prove precondition of g',
         src: tc('''class C {
                        static int f(int n) { n - 1 }
                        @Requires({ z >= 0 })
                        static int g(int z) { z }
                        static int h(int n) { int c = f(n); return g(c) }
                    }''')],
        // Refute control, nested form.
        [group: 'P309 call results as arguments', name: 'too-weak callee ensures refutes in the nested form', expect: 'Cannot prove precondition of g',
         src: tc('''class C {
                        @Ensures({ result >= -1 })
                        static int f(int n) { n >= 0 ? n : -1 }
                        @Requires({ z >= 0 })
                        static int g(int z) { z }
                        static int h(int n) { g(f(n)) }
                    }''')],
        // The postcondition side of the same shape: a call nested in a RETURN expression. The return-position hoist
        // (Phase 206) now works inside-out, so `inc(dbl(n))` hoists `dbl(n)` first and then `inc(…)` over it.
        [group: 'P309 call results as arguments', name: 'nested call in a return expression proves', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 2 * n })
                        static int dbl(int n) { 2 * n }
                        @Ensures({ result == m + 1 })
                        static int inc(int m) { m + 1 }
                        @Ensures({ result == 2 * n + 1 })
                        static int h(int n) { inc(dbl(n)) }
                    }''')],
        // Refute control: a wrong claim over the same nested return must REFUTE — had the nested call still been
        // outside the fragment it would skip instead, so this pins that the return expression is really reasoned about.
        [group: 'P309 call results as arguments', name: 'nested call in a return expression refutes a wrong claim',
         expect: 'Cannot prove postcondition of h', refute: 'ret$call',
         src: tc('''class C {
                        @Ensures({ result == 2 * n })
                        static int dbl(int n) { 2 * n }
                        @Ensures({ result == m + 1 })
                        static int inc(int m) { m + 1 }
                        @Ensures({ result == 2 * n })
                        static int h(int n) { inc(dbl(n)) }
                    }''')],
    ]
}
