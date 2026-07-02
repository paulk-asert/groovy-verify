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

/** 'P66 repeated contracts' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G186_p66_repeated_contracts {

    static final List<Map> CASES = [

        // ---------- Phase 66: repeated @Requires / @Ensures are conjoined ----------
        // groovy-contracts is @Repeatable and enforces each at runtime, so multiple @Requires mean
        // their conjunction. Both are now captured: result = a + b >= 0 needs BOTH a >= 0 and b >= 0
        // (previously only the last was kept, so `a` was unconstrained and this refuted).
        [group: 'P66 repeated contracts', name: 'two @Requires both assumed', ok: true,
         src: tc('class C { @Requires({ a >= 0 }) @Requires({ b >= 0 }) @Ensures({ result >= 0 }) static int f(int a, int b) { a + b } }')],
        // Soundness: a method must satisfy EVERY @Ensures. Here the body returns 3 — it meets the
        // *last* postcondition (3 <= 100) but violates the *first* (3 >= 5), which used to be dropped
        // (silently "verifying" a method that breaks its own spec). Now correctly refuted.
        [group: 'P66 repeated contracts', name: 'two @Ensures both proven (violates first → refuted)',
         expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result >= 5 }) @Ensures({ result <= 100 }) static int f() { 3 } }')],
        // A body satisfying both postconditions verifies.
        [group: 'P66 repeated contracts', name: 'two @Ensures both satisfied verified', ok: true,
         src: tc('class C { @Ensures({ result >= 5 }) @Ensures({ result <= 100 }) static int f() { 50 } }')],
        // Three @Requires conjoin too, and a precondition that rules out the unsafe input verifies the body.
        [group: 'P66 repeated contracts', name: 'three @Requires conjoined verify index', ok: true,
         src: tc('class C { @Requires({ a != null }) @Requires({ i >= 0 }) @Requires({ i < a.length }) static int f(int[] a, int i) { a[i] } }')],
        // @Modifies is @Repeatable too, but a frame is a *union* of locations (not a conjunction): two
        // @Modifies are merged, so a method writing both declared fields passes the frame check
        // (previously only the last was kept, wrongly flagging the write to the dropped field).
        [group: 'P66 repeated contracts', name: 'two @Modifies frames merged (both writes allowed)', ok: true,
         src: tc('class C { int a; int b; @Modifies({ this.a }) @Modifies({ this.b }) void setBoth() { a = 1; b = 2 } }')],
        // A write outside the merged frame is still caught — both declared locations are in scope, the
        // undeclared third field is the violation.
        [group: 'P66 repeated contracts', name: 'two @Modifies, undeclared write violates',
         expect: 'not in its @Modifies clause',
         src: tc('class C { int a; int b; int c; @Modifies({ this.a }) @Modifies({ this.b }) void m() { a = 1; b = 2; c = 3 } }')],
    ]
}
