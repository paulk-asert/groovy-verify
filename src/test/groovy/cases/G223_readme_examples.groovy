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

/** 'README examples' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G223_readme_examples {

    static final List<Map> CASES = [

        // ---------- README Examples (verbatim, so the docs can't drift from reality) ----------
        [group: 'README examples', name: 'nested loop: count = n*n', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n * n })
                        static int squareCount(int n) {
                            int count = 0, i = 0
                            @Invariant({ 0 <= i && i <= n && count == i * n })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n && count == i * n + j })
                                @Decreases({ n - j })
                                while (j < n) {
                                    count += 1
                                    j += 1
                                }
                                i += 1
                            }
                            count
                        }
                    }''')],
        [group: 'README examples', name: 'two-cursor array copy dst[j++] = src[i++]', ok: true,
         src: tc('''class C {
                        @Requires({ src != null && dst != null && src.length <= dst.length })
                        @Ensures({ (0..<src.length).every { result[it] == src[it] } })
                        static int[] copy(int[] src, int[] dst) {
                            int i = 0, j = 0
                            @Invariant({ 0 <= i && i <= src.length && i == j &&
                                         (0..<i).every { dst[it] == src[it] } })
                            @Decreases({ src.length - i })
                            while (i < src.length) { dst[j++] = src[i++] }   // dst[j] = src[i]; i++; j++
                            return dst
                        }
                    }''')],
        [group: 'README examples', name: 'set merge (union membership)', ok: true,
         src: tc('''class C {
                        @Requires({ p in granted })
                        @Ensures({ p in (granted | extra) })
                        static int merge(Set<Integer> granted, Set<Integer> extra, int p) { 0 }
                    }''')],
        [group: 'README examples', name: 'lowBit (bitwise low bit)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 || result == 1 })
                        static int lowBit(int a) { a & 1 }
                    }''')],
        [group: 'README examples', name: 'singleton (sized array, symbolic n)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result.length == n && result[0] == x })
                        static int[] singleton(int n, int x) {
                            int[] r = new int[n]   // length n, all zero
                            r[0] = x
                            return r
                        }
                    }''')],
    ]
}
