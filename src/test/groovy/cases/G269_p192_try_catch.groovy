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

/** 'P192 try-catch' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G269_p192_try_catch {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'try/catch and throw in the @Ensures path model: the happy path is walked exactly, each catch handler is a separate path entered with every try-assigned local havocked (the try may have executed any prefix before throwing), and an explicit throw ends its path (a postcondition is vacuous on a non-returning path — so guard-throw prologues and rethrowing handlers verify); finally and heap mutation inside try stay loud skips.'

    static final List<Map> CASES = [

        // ---------- Phase 192: try/catch happy path + throw (path ends) ----------
        // The headline: a try with a compensating catch — every path (both try branches AND the
        // handler) proves the postcondition.
        [group: 'P192 try-catch', name: 'try with compensating catch verifies on all paths', ok: true,
         src: tc('''class C {
             @Ensures({ result >= 5 })
             static int f(int n) {
                 try {
                     if (n > 5) return n
                     return 5
                 } catch (RuntimeException e) {
                     return 5
                 }
             }
         }''')],
        // TEETH: the catch path is genuinely checked — a handler that violates the postcondition refutes.
        [group: 'P192 try-catch', name: 'violating catch path refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
             @Ensures({ result >= 5 })
             static int g(int n) {
                 try {
                     return n > 5 ? n : 5
                 } catch (RuntimeException e) {
                     return 0
                 }
             }
         }''')],
        // TEETH for the havoc: the handler must NOT see a value the try block assigned — the try may
        // have thrown before (or after) the write, so `x` is unknown at catch entry and `result == 2`
        // is unprovable there.
        [group: 'P192 try-catch', name: 'catch entry havocs try-assigned locals', expect: 'Cannot prove postcondition',
         src: tc('''class C {
             @Ensures({ result == 2 })
             static int h() {
                 int x = 1
                 try {
                     x = 2
                     return x
                 } catch (RuntimeException e) {
                     return x
                 }
             }
         }''')],
        // A rethrowing handler: the catch path ends at the throw (no normal return → nothing to prove
        // there), so only the exact happy path carries the postcondition.
        [group: 'P192 try-catch', name: 'rethrowing catch leaves only the happy path', ok: true,
         src: tc('''class C {
             @Ensures({ result == n + 1 })
             static int r(int n) {
                 try {
                     return n + 1
                 } catch (RuntimeException e) {
                     throw new IllegalStateException('wrapped')
                 }
             }
         }''')],
        // The guard-throw prologue — ubiquitous in real code, previously an "unsupported statement
        // ThrowStatement" skip. The throwing path is vacuous; the surviving path knows !(n < 0).
        [group: 'P192 try-catch', name: 'guard-throw prologue verifies', ok: true,
         src: tc('''class C {
             @Ensures({ result >= 1 })
             @ThrowsIf(value = { n < 0 }, exception = IllegalArgumentException, woven = false)
             static int inc(int n) {
                 if (n < 0) throw new IllegalArgumentException('negative')
                 return n + 1
             }
         }''')],
        // Refute twin: the guard fact is what carries the proof — asking for more than it gives refutes
        // on the surviving path (n == 0 returns 1).
        [group: 'P192 try-catch', name: 'guard-throw refute twin', expect: 'Cannot prove postcondition',
         src: tc('''class C {
             @Ensures({ result >= 2 })
             static int inc(int n) {
                 if (n < 0) throw new IllegalArgumentException('negative')
                 return n + 1
             }
         }''')],
        // `finally` stays outside the fragment — loudly.
        [group: 'P192 try-catch', name: 'finally skips loudly', expect: "'finally' unsupported",
         src: tc('''class C {
             @Ensures({ result >= 0 })
             static int f(int n) {
                 try {
                     return n * 0
                 } catch (RuntimeException e) {
                     return 0
                 } finally {
                     n = 0
                 }
             }
         }''')],
        // Heap mutation inside the try (an array store) can't be framed per-name at catch entry — loud skip.
        [group: 'P192 try-catch', name: 'heap mutation in try skips loudly', expect: 'try block mutates heap state',
         src: tc('''class C {
             @Ensures({ result >= 0 })
             static int f(int[] a) {
                 try {
                     a[0] = 1
                     return 1
                 } catch (RuntimeException e) {
                     return 0
                 }
             }
         }''')],
    ]
}
