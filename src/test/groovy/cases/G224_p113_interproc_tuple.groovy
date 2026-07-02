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

/** 'P113 interproc-tuple' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G224_p113_interproc_tuple {

    static final List<Map> CASES = [
        // ---------- P113 inter-procedural tuple results ----------
        // Binding `Tuple2 r = callee(...)` to a local and using its slots (`r.v1`) in the body — array index,
        // call argument, return composition. A tuple local is registered (Phase-80 param-tuple machinery) and
        // the callee's @Ensures binds its slots via a `result`→`r` rename; the slot entities are constrained
        // wherever the assignment is replayed (body VC, bounds check, call-precondition discharge).
        [group: 'P113 interproc-tuple', name: 'hoisted tuple slot used in body', ok: true,
         src: tc('''class C {
                        @Ensures({ result.v1 == 0 && result.v2 == 1 })
                        static Tuple2<Integer, Integer> mk() { return Tuple.tuple(0, 1) }
                        @Ensures({ result == 0 })
                        static int g() {
                            Tuple2<Integer, Integer> r = mk()
                            return r.v1
                        }
                    }''')],
        // Binding-correctness control: r.v1 == 0 (from mk's @Ensures), so claiming result == 1 must refute —
        // the slot is genuinely bound to the callee's value, not left free.
        [group: 'P113 interproc-tuple', name: 'wrong slot value refuted', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Ensures({ result.v1 == 0 && result.v2 == 1 })
                        static Tuple2<Integer, Integer> mk() { return Tuple.tuple(0, 1) }
                        @Ensures({ result == 1 })
                        static int g() {
                            Tuple2<Integer, Integer> r = mk()
                            return r.v1
                        }
                    }''')],
        // The full two-pass FoVeOOS Duplets: find two duplicate pairs with DIFFERENT values, by composing
        // duplet + dupletExcept(first value) across method calls — the capstone that the inter-procedural
        // tuple result enables. result is a Tuple4 built from the two tuple-returning calls' slots.
        [group: 'P113 interproc-tuple', name: 'full two-pass duplets composition', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && (0..<a.length).any { int p -> (p + 1..<a.length).any { int q -> a[p] == a[q] } } })
                        @Ensures({ 0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2] })
                        static Tuple2<Integer, Integer> duplet(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length &&
                                (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] } } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length &&
                                    (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] } } &&
                                    (i + 1..<j).every { int q -> a[i] != a[q] } })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j]) return Tuple.tuple(i, j)
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return Tuple.tuple(-1, -1)
                        }
                        @Requires({ a != null && (0..<a.length).any { int p -> (p + 1..<a.length).any { int q -> a[p] == a[q] && a[p] != except } } })
                        @Ensures({ 0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2] && a[result.v1] != except })
                        static Tuple2<Integer, Integer> dupletExcept(int[] a, int except) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length &&
                                (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] || a[p] == except } } })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < a.length && i + 1 <= j && j <= a.length &&
                                    (0..<i).every { int p -> (p + 1..<a.length).every { int q -> a[p] != a[q] || a[p] == except } } &&
                                    (i + 1..<j).every { int q -> a[i] != a[q] || a[i] == except } })
                                @Decreases({ a.length - j })
                                while (j < a.length) {
                                    if (a[i] == a[j] && a[i] != except) return Tuple.tuple(i, j)
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return Tuple.tuple(-1, -1)
                        }
                        @Requires({ a != null && (0..<a.length).any { int i -> (i + 1..<a.length).any { int j -> (0..<a.length).any { int k -> (k + 1..<a.length).any { int l -> a[i] == a[j] && a[k] == a[l] && a[i] != a[k] } } } } })
                        @Ensures({ 0 <= result.v1 && result.v1 < result.v2 && result.v2 < a.length && a[result.v1] == a[result.v2] &&
                                   0 <= result.v3 && result.v3 < result.v4 && result.v4 < a.length && a[result.v3] == a[result.v4] &&
                                   a[result.v1] != a[result.v3] })
                        static Tuple4<Integer, Integer, Integer, Integer> duplets(int[] a) {
                            Tuple2<Integer, Integer> r1 = duplet(a)
                            Tuple2<Integer, Integer> r2 = dupletExcept(a, a[r1.v1])
                            return Tuple.tuple(r1.v1, r1.v2, r2.v1, r2.v2)
                        }
                    }''')],
    ]
}
