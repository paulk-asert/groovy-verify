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

/** 'P312 break' — `break` out of an annotated loop: the code after the loop is checked from every state the loop
 *  can be left in. Shared import header and wrappers come from {@link CaseDsl}. */
class G357_p312_break {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = '`break` out of an annotated loop, top-level or as a leaf of a tail if/else chain: the breaking iteration need not preserve the invariant or decrease the variant, and the postcondition and after-loop obligations are checked from each break as well as the natural exit.'

    static final List<Map> CASES = [
        // ---------- Phase 312: break ----------
        // LemmaScript's linear search, verbatim: the result is set in the break's lead.
        [group: 'P312 break', name: 'linear search with result and break', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= -1 && result < arr.length })
                        @Ensures({ result >= 0 ==> arr[result] == target })
                        @Ensures({ result == -1 ==> (0..<arr.length).every { arr[it] != target } })
                        static int linearSearch(int[] arr, int target) {
                            int i = 0
                            int result = -1
                            @Invariant({ 0 <= i && i <= arr.length })
                            @Invariant({ (0..<i).every { arr[it] != target } })
                            @Invariant({ result == -1 || (result >= 0 && result < arr.length && arr[result] == target) })
                            @Decreases({ arr.length - i })
                            while (i < arr.length) {
                                if (arr[i] == target) { result = i; break }
                                i = i + 1
                            }
                            return result
                        }
                    }''')],
        // LemmaScript's binary search, verbatim: the break leaf is the FIRST branch of the tail if/else chain, and
        // the breaking iteration doesn't shrink [lo, hi] — no variant decrease needed when the loop is left.
        [group: 'P312 break', name: 'binary search with a break leaf in the tail chain', ok: true,
         src: tc('''class C {
                        @Requires({ arr.isSorted() })
                        @Ensures({ result >= -1 && result < arr.length })
                        @Ensures({ result >= 0 ==> arr[result] == target })
                        @Ensures({ result == -1 ==> (0..<arr.length).every { arr[it] != target } })
                        static int binarySearch(int[] arr, int target) {
                            int lo = 0
                            int hi = arr.length - 1
                            int result = -1
                            @Invariant({ 0 <= lo && lo <= arr.length && -1 <= hi && hi < arr.length })
                            @Invariant({ (0..<lo).every { arr[it] != target } })
                            @Invariant({ (hi + 1..<arr.length).every { arr[it] != target } })
                            @Invariant({ result == -1 || (result >= 0 && result < arr.length && arr[result] == target) })
                            @Decreases({ hi - lo + 1 })
                            while (lo <= hi) {
                                int mid = lo + (hi - lo).intdiv(2)
                                if (arr[mid] == target) { result = mid; break }
                                else if (arr[mid] < target) lo = mid + 1
                                else hi = mid - 1
                            }
                            return result
                        }
                    }''')],
        // LemmaScript's isSorted: a boolean flag set in the lead.
        [group: 'P312 break', name: 'isSorted with a flag and break', ok: true,
         src: tc('''class C {
                        @Requires({ arr.length > 0 })
                        @Ensures({ result ==> (0..<arr.length - 1).every { arr[it] <= arr[it + 1] } })
                        @Ensures({ !result ==> (0..<arr.length - 1).any { arr[it] > arr[it + 1] } })
                        static boolean isSorted(int[] arr) {
                            boolean result = true
                            int i = 0
                            @Invariant({ 0 <= i && i < arr.length })
                            @Invariant({ result ==> (0..<i).every { arr[it] <= arr[it + 1] } })
                            @Invariant({ !result ==> (0..<arr.length - 1).any { arr[it] > arr[it + 1] } })
                            @Decreases({ arr.length - i })
                            while (i + 1 < arr.length) {
                                if (arr[i] > arr[i + 1]) { result = false; break }
                                i = i + 1
                            }
                            return result
                        }
                    }''')],
        // A classic for loop: break skips the update, so the result is the index of the hit.
        [group: 'P312 break', name: 'for loop break skips the update', ok: true,
         src: tc('''class C {
                        @Ensures({ 0 <= result && result <= a.length })
                        @Ensures({ result < a.length ==> a[result] < 0 })
                        static int firstNegative(int[] a) {
                            int i
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            for (i = 0; i < a.length; i++) {
                                if (a[i] < 0) break
                            }
                            return i
                        }
                    }''')],
        // while (true): the loop can only be left by its break, so only the break path reaches the return.
        [group: 'P312 break', name: 'while true left only by break', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int countTo(int n) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (true) {
                                if (i == n) break
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // The breaking iteration need not preserve the invariant: the lead sets i = a.length + 1 (outside the
        // invariant's range) and the code after the loop is still checked from that state, where the divisor is 1.
        [group: 'P312 break', name: 'break lead may leave the invariant behind', ok: true,
         src: tc('''class C {
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) { i = a.length + 1; break }
                                i = i + 1
                            }
                            return 10.intdiv(a.length - i + 2)
                        }
                    }''')],
        // Refute: the same shape, but from the break the divisor is 0. Safe from the natural exit (where it is 1),
        // so this pins that the after-loop obligations really are checked from the break.
        [group: 'P312 break', name: 'after-loop obligation unsafe only from the break refutes', expect: 'fails on: f([-1] as int[])',
         src: tc('''class C {
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) { i = a.length + 1; break }
                                i = i + 1
                            }
                            return 10.intdiv(a.length - i + 1)
                        }
                    }''')],
        // Refute: a postcondition that holds on the natural exit (i == a.length) but not from the break.
        [group: 'P312 break', name: 'postcondition wrong only from the break refutes', expect: 'fails on: firstNegative([-1] as int[])',
         src: tc('''class C {
                        @Ensures({ result == a.length })
                        static int firstNegative(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) break
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // Refute: and one wrong only on the natural exit — the break path must not hide it.
        [group: 'P312 break', name: 'postcondition wrong only on the natural exit refutes', expect: 'Cannot prove postcondition of firstNegative',
         src: tc('''class C {
                        @Ensures({ result < a.length })
                        static int firstNegative(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] < 0) break
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
        // A nested loop's break is modelled at the top level of the inner body (Phase 324); one buried in an if is
        // rewritten to that shape (Phase 339).
        [group: 'P312 break', name: 'buried break in a nested loop verifies (Phase 339)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result >= 0 })
                        static int f(int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                int j = 0
                                @Invariant({ 0 <= j && j <= n })
                                @Decreases({ n - j })
                                while (j < n) {
                                    if (j > 0) { if (j == i) break }
                                    j = j + 1
                                }
                                s = s + j
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        // A break buried in a nested if is rewritten to a flag and `if (brk) break` (Phase 339).
        [group: 'P312 break', name: 'buried break verifies (Phase 339)', ok: true,
         src: tc('''class C {
                        @Ensures({ result >= 0 })
                        static int f(int[] a) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= a.length })
                            @Decreases({ a.length - i })
                            while (i < a.length) {
                                if (a[i] > 0) { if (a[i] > 10) break }
                                i = i + 1
                            }
                            return i
                        }
                    }''')],
    ]
}
