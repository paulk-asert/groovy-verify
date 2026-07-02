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

/** 'P91 nested' — 14 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G107_p91_nested {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A loop nested inside another (matrix sum, n*n / n*m double loops) with scalar accumulators.'

    static final List<Map> CASES = [
        // Matrix sum — nested loops + array-range `.sum()` aggregation + the NIA monotonicity lemma (the
        // flat-index `a[k]` read bound `i*m+j < n*m`). The bare `.sum()` form is NOT empty-safe: a range subscript
        // `a[0..<k]` is a Groovy *sublist* (a List), and `[].sum()` is *null*, not 0 — so at the `n == 0` entry the
        // invariant `sum == a[0..<0].sum()` is `0 == null`. The verifier now models the empty List fold as
        // unconstrained (only a numeric *array*'s `.sum()` empties to 0), so it can no longer establish it — a
        // refute-hostile boundary that soft-fails to "could not decide" on this heavy nested VC. The `.sum(0)`
        // variant below is the empty-safe workaround (and the form the README "Examples" now shows).
        [group: 'P91 nested', name: 'matrix sum: bare .sum() refused at the empty edge', expect: 'Could not decide',
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 && a != null && a.length >= n * m })
                        @Ensures({ result == a[0..<n * m].sum() })
                        static int matrixSum(int n, int m, int[] a) {
                            int sum = 0; int i = 0; int k = 0
                            @Invariant({ 0 <= i && i <= n && k == i * m && sum == a[0..<k].sum() })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= i && i < n && 0 <= j && j <= m && k == i * m + j &&
                                             sum == a[0..<k].sum() })
                                @Decreases({ m - j })
                                while (j < m) {
                                    sum += a[k]
                                    k += 1
                                    j += 1
                                }
                                i += 1
                            }
                            sum
                        }
                    }''')],
        // The empty-safe workaround for the same proof: Groovy's no-arg `.sum()` is duck-typed (it folds with
        // `+`, so `['', 1, 2, 3].sum() == '123'`) and therefore has no zero element — `[].sum()` is *null*, not 0.
        // Seeding the fold with `.sum(0)` supplies the zero, so `[].sum(0) == 0` and the `n == 0` edge of this
        // proof matches the runtime exactly (see the runtime rung: the `.sum()` form is a known empty-edge
        // divergence, this one cross-validates clean).
        [group: 'P91 nested', name: 'matrix sum with sum(0) seed (empty-safe)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 && a != null && a.length >= n * m })
                        @Ensures({ result == a[0..<n * m].sum(0) })
                        static int matrixSum(int n, int m, int[] a) {
                            int sum = 0; int i = 0; int k = 0
                            @Invariant({ 0 <= i && i <= n && k == i * m && sum == a[0..<k].sum(0) })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= i && i < n && 0 <= j && j <= m && k == i * m + j &&
                                             sum == a[0..<k].sum(0) })
                                @Decreases({ m - j })
                                while (j < m) {
                                    sum += a[k]
                                    k += 1
                                    j += 1
                                }
                                i += 1
                            }
                            sum
                        }
                    }''')],
        // The matrix sum, made empty-safe with Arrays.copyOf instead of slicing (the int[]-returning workaround):
        // copyOf keeps array semantics, so the n == 0 edge is `0 == copyOf(a, 0).sum() == 0` — and it verifies.
        [group: 'P91 nested', name: 'matrix sum via Arrays.copyOf (empty-safe array slice)', ok: true,
         src: HDR + 'import java.util.Arrays\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + '''class C {
                        @Requires({ n >= 0 && m >= 0 && a != null && a.length >= n * m })
                        @Ensures({ result == Arrays.copyOf(a, n * m).sum() })
                        static int matrixSum(int n, int m, int[] a) {
                            int sum = 0; int i = 0; int k = 0
                            @Invariant({ 0 <= i && i <= n && k == i * m && sum == Arrays.copyOf(a, k).sum() })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= i && i < n && 0 <= j && j <= m && k == i * m + j &&
                                             sum == Arrays.copyOf(a, k).sum() })
                                @Decreases({ m - j })
                                while (j < m) {
                                    sum += a[k]
                                    k += 1
                                    j += 1
                                }
                                i += 1
                            }
                            sum
                        }
                    }'''.stripIndent()],

        // ---------- Phase 91: nested loops (compositional cut-points) ----------
        // Canonical: count = n*n via a double loop. Outer inv `count == i*n`, inner inv `count == i*n + j`.
        [group: 'P91 nested', name: 'count = n*n double loop', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n * n })
                        static int f(int n) {
                            int count = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && count == i * n })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n && count == i * n + j })
                                @Decreases({ n - j })
                                while (j < n) {
                                    count = count + 1
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            count
                        }
                    }''')],
        // Rectangular variant — distinct bounds n, m: count = n*m.
        [group: 'P91 nested', name: 'count = n*m distinct bounds', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 })
                        @Ensures({ result == n * m })
                        static int f(int n, int m) {
                            int count = 0; int i = 0
                            @Invariant({ 0 <= i && i <= n && count == i * m })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= m && count == i * m + j })
                                @Decreases({ m - j })
                                while (j < m) { count = count + 1; j = j + 1 }
                                i = i + 1
                            }
                            count
                        }
                    }''')],

        // SOUNDNESS PROBE A — false outer postcondition must NOT verify.
        [group: 'P91 nested', name: 'false outer post refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n * n + 1 })
                        static int f(int n) {
                            int count = 0; int i = 0
                            @Invariant({ 0 <= i && i <= n && count == i * n })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n && count == i * n + j })
                                @Decreases({ n - j })
                                while (j < n) { count = count + 1; j = j + 1 }
                                i = i + 1
                            }
                            count
                        }
                    }''')],
        // SOUNDNESS PROBE B — false inner invariant (off by one) must be CAUGHT (inner establish fails).
        [group: 'P91 nested', name: 'false inner invariant caught', expect: 'holds on entry',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n * n })
                        static int f(int n) {
                            int count = 0; int i = 0
                            @Invariant({ 0 <= i && i <= n && count == i * n })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n && count == i * n + j + 1 })
                                @Decreases({ n - j })
                                while (j < n) { count = count + 1; j = j + 1 }
                                i = i + 1
                            }
                            count
                        }
                    }''')],
        // SOUNDNESS PROBE C — THE KEY ONE: a too-weak inner invariant (drops the count relation) is itself
        // provable, but must NOT let the outer silently pass: the outer preservation can't re-establish
        // `count == (i+1)*n` because the summary leaves count unconstrained.
        [group: 'P91 nested', name: 'weak inner invariant fails outer preservation', expect: 'preserved by the loop body',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n * n })
                        static int f(int n) {
                            int count = 0; int i = 0
                            @Invariant({ 0 <= i && i <= n && count == i * n })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n })
                                @Decreases({ n - j })
                                while (j < n) { count = count + 1; j = j + 1 }
                                i = i + 1
                            }
                            count
                        }
                    }''')],
        // PROBE D — un-annotated inner loop must skip loudly (can't summarise without an invariant).
        [group: 'P91 nested', name: 'unannotated inner loop skips loudly', expect: 'unsupported statement WhileStatement',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n * n })
                        static int f(int n) {
                            int count = 0; int i = 0
                            @Invariant({ 0 <= i && i <= n && count == i * n })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                while (j < n) { count = count + 1; j = j + 1 }
                                i = i + 1
                            }
                            count
                        }
                    }''')],
        // BOUNDARY — 3-level nesting is out of this slice; skips loudly (the 2nd-level summary's frame
        // can't be bounded once its body holds a 3rd loop).
        [group: 'P91 nested', name: '3-level nesting skips loudly', expect: 'Skipped loop verification',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == 0 })
                        static int f(int n) {
                            int count = 0; int i = 0
                            @Invariant({ 0 <= i && i <= n }) @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n }) @Decreases({ n - j })
                                while (j < n) {
                                    int k = 0
                                    @Invariant({ 0 <= k && k <= n }) @Decreases({ n - k })
                                    while (k < n) { count = count + 1; k = k + 1 }
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            0
                        }
                    }''')],
        // PROBE: linear-bound array-fill — inner loop clears a buffer a[0..<m] each pass (index j, linear).
        [group: 'P91 nested', name: 'array-fill: clear buffer each pass (linear bound)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 && m >= 0 && a != null && a.length >= m })
                        @Ensures({ (0..<m).every { result[it] == 0 } })
                        static int[] clear(int n, int m, int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && (i >= 1 ==> (0..<m).every { a[it] == 0 }) })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= m && (0..<j).every { a[it] == 0 } })
                                @Decreases({ m - j })
                                while (j < m) {
                                    a[j] = 0
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            a
                        }
                    }''')],
        // PROBE: out-of-bounds inner store is caught (a.length only >= n, but the flat index k reaches ~n*m).
        [group: 'P91 nested', name: 'array-fill out-of-bounds store refutes', expect: 'out of bounds',
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 && a != null && a.length >= n })
                        static int[] zero(int n, int m, int[] a) {
                            int i = 0
                            int k = 0
                            @Invariant({ 0 <= i && i <= n && k == i * m })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= i && i < n && 0 <= j && j <= m && k == i * m + j })
                                @Decreases({ m - j })
                                while (j < m) {
                                    a[k] = 0
                                    k = k + 1
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            a
                        }
                    }''')],
        // The flat n×m matrix fill verifies end-to-end: the store bound i*m+j < n*m is closed by the
        // verifier-supplied monotonicity lemma (Phase 91b), and the content quantifier is stripped from the
        // bounds discharge so Z3 stays out of its quantifier+NIA dead end.
        [group: 'P91 nested', name: '2D matrix fill verifies (monotonicity lemma)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 && m >= 0 && a != null && a.length >= n * m })
                        @Ensures({ (0..<n * m).every { result[it] == 0 } })
                        static int[] zero(int n, int m, int[] a) {
                            int i = 0
                            int k = 0
                            @Invariant({ 0 <= i && i <= n && k == i * m && (0..<k).every { a[it] == 0 } })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= i && i < n && 0 <= j && j <= m && k == i * m + j &&
                                             (0..<k).every { a[it] == 0 } })
                                @Decreases({ m - j })
                                while (j < m) {
                                    a[k] = 0
                                    k = k + 1
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            a
                        }
                    }''')],
        // BOUNDARY E — an inner loop with a COLLECTION MUTATOR (size-changing) still skips loudly.
        [group: 'P91 nested', name: 'inner loop list mutator skips loudly', expect: 'field/collection',
         src: tc('''class C {
                        @Requires({ n >= 0 && xs != null })
                        static void f(int n, List<Integer> xs) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n })
                                @Decreases({ n - j })
                                while (j < n) { xs.add(0); j = j + 1 }
                                i = i + 1
                            }
                        }
                    }''')],
    ]
}
