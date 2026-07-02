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

/** 'P86 inc/dec' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G101_p86_inc_dec {

    static final List<Map> CASES = [

        // ---------- Phase 86: pre/post increment & decrement (++ / --) as statements ----------
        // `i++` / `++i` / `i--` / `--i` desugar to `i = i ± 1` (pre/post is irrelevant as a statement),
        // in both straight-line and loop-body positions (the for-loop *update* slot already handled them).
        [group: 'P86 inc/dec', name: 'straight-line i++', ok: true,
         src: tc('class C { @Ensures({ result == 6 }) static int f() { int s = 5; s++; s } }')],
        [group: 'P86 inc/dec', name: 'straight-line ++i (prefix)', ok: true,
         src: tc('class C { @Ensures({ result == 6 }) static int f() { int s = 5; ++s; s } }')],
        [group: 'P86 inc/dec', name: 'straight-line i--', ok: true,
         src: tc('class C { @Ensures({ result == 4 }) static int f() { int s = 5; s--; s } }')],
        [group: 'P86 inc/dec', name: 'wrong inc result refutes', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result == 5 }) static int f() { int s = 5; s++; s } }')],
        // The idiomatic loop counter: `i++` in the while body.
        [group: 'P86 inc/dec', name: 'while body i++ counter', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int count(int n) {
                            int c = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && c == i })
                            @Decreases({ n - i })
                            while (i < n) { c++; i++ }
                            c
                        }
                    }''')],
        // Array-element increment desugars to an array store.
        [group: 'P86 inc/dec', name: 'array element a[i]++', ok: true,
         src: tc('''class C {
                        int[] a
                        @Requires({ a != null && 0 <= i && i < a.length })
                        @Ensures({ a[i] == old.a[i] + 1 })
                        void bump(int i) { a[i]++ }
                    }''')],
    ]
}
