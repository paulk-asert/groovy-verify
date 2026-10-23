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

/** 'LemmaScript port' — the verified TypeScript examples of LemmaScript (lemmascript.org, MIT) ported structure for
 *  structure; examples/lemmascript.md links each block here. LemmaScript's `//@ contract` sentence is carried as a
 *  plain groovydoc comment. Shared import header and wrappers come from {@link CaseDsl}. */
class G354_lemmascript_port {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'LemmaScript\'s verified TypeScript examples ported to Groovy contracts — binary and linear search, max, sortedness, sum, swap, leftPad, duplicate detection, zigzag encoding, a bounded counter, money splitting (allocate, nonlinear), recursive pruneWindow — loops leaving by `break` as LemmaScript\'s do, with the overflow LemmaScript\'s unbounded `number` cannot see.'

    static final List<Map> CASES = [
        // ---------- LemmaScript port (lemmascript.org front page + examples/*.ts) ----------
        // binarySearch.ts — the front page's example, verbatim: LemmaScript's invariants (inclusive `hi` and all),
        // and its `break` out of the loop once the target is found (Phase 312). No `//@ done_with` counterpart is
        // needed: the code after the loop is checked from the break's state as well as the natural exit.
        [group: 'LemmaScript port', name: 'binarySearch', ok: true,
         src: tc('''class C {
                        /** Finds target in a sorted array, or reports -1. */
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
        // Refute control: drop sortedness and the excluded-region invariant is no longer preserved.
        [group: 'LemmaScript port', name: 'binarySearch without sortedness refutes', expect: 'Cannot prove loop invariant is preserved',
         src: tc('''class C {
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
        // clamp.ts — mutable local, conditional assignment.
        [group: 'LemmaScript port', name: 'clamp', ok: true,
         src: tc('''class C {
                        /** Clamps x into the closed range [lo, hi]. */
                        @Requires({ lo <= hi })
                        @Ensures({ result >= lo && result <= hi })
                        static int clamp(int x, int lo, int hi) {
                            int result = x
                            if (result < lo) result = lo
                            if (result > hi) result = hi
                            return result
                        }
                    }''')],
        // linearSearch.ts — verbatim, `break` and all.
        [group: 'LemmaScript port', name: 'linearSearch', ok: true,
         src: tc('''class C {
                        /** Returns the first index of target, or -1 when it is absent. */
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
        // maxElement.ts — LemmaScript's forall/exists pair as native .every/.any.
        [group: 'LemmaScript port', name: 'maxElement', ok: true,
         src: tc('''class C {
                        /** Returns the largest element of a non-empty array. */
                        @Requires({ arr.length > 0 })
                        @Ensures({ (0..<arr.length).every { arr[it] <= result } })
                        @Ensures({ (0..<arr.length).any { arr[it] == result } })
                        static int maxElement(int[] arr) {
                            int max = arr[0]
                            int i = 1
                            @Invariant({ 1 <= i && i <= arr.length })
                            @Invariant({ (0..<i).every { arr[it] <= max } })
                            @Invariant({ (0..<i).any { arr[it] == max } })
                            @Decreases({ arr.length - i })
                            while (i < arr.length) {
                                if (arr[i] > max) max = arr[i]
                                i = i + 1
                            }
                            return max
                        }
                    }''')],
        // isSorted.ts — a boolean result specified in both directions, its flag set before the `break`.
        [group: 'LemmaScript port', name: 'isSorted', ok: true,
         src: tc('''class C {
                        /** Reports whether a non-empty array is in ascending order. */
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
        // arraySum.ts — LemmaScript's `sumTo(arr, i)` helper is Groovy's own range sum.
        [group: 'LemmaScript port', name: 'arraySum', ok: true,
         src: tc('''class C {
                        /** Sums the elements of a non-empty array. */
                        @Requires({ arr.length > 0 })
                        @Ensures({ result == arr.sum() })
                        static int arraySum(int[] arr) {
                            int sum = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= arr.length })
                            @Invariant({ i == 0 ? sum == 0 : sum == arr[0..<i].sum() })
                            @Decreases({ arr.length - i })
                            while (i < arr.length) { sum = sum + arr[i]; i = i + 1 }
                            return sum
                        }
                    }''')],
        // swap.ts — `old` names the pre-state that TypeScript's aliasing `let result = arr` leaves implicit.
        [group: 'LemmaScript port', name: 'swap', ok: true,
         src: tc('''class C {
                        /** Swaps two elements of an array in place. */
                        @Requires({ 0 <= i && i < arr.length && 0 <= j && j < arr.length })
                        @Ensures({ result.length == arr.length && result[i] == old.arr[j] && result[j] == old.arr[i] })
                        static int[] swap(int[] arr, int i, int j) {
                            int tmp = arr[i]
                            arr[i] = arr[j]
                            arr[j] = tmp
                            return arr
                        }
                    }''')],
        // leftPad.ts — the npm left-pad, as LemmaScript adapts it, with exactly the original's invariants: `n` is fixed
        // before the loop, and since Phase 318 the loop keeps that without it being restated.
        [group: 'LemmaScript port', name: 'leftPad', ok: true,
         src: tc('''class C {
                        /** Pads str on the left with ch until it is len characters long. */
                        @Requires({ str != null && ch != null && ch.length() == 1 && len >= 0 })
                        @Ensures({ str.length() >= len ==> result == str })
                        @Ensures({ str.length() < len ==> result.length() == len })
                        static String leftPad(String str, int len, String ch) {
                            String result = str
                            int n = len - str.length()
                            int i = 0
                            @Invariant({ result.length() == str.length() + i && i >= 0 })
                            @Invariant({ n > 0 ==> i <= n })
                            @Invariant({ n <= 0 ==> result == str })
                            @Decreases({ n - i })
                            while (i < n) { result = ch + result; i = i + 1 }
                            return result
                        }
                    }''')],
        // containsDuplicate.ts — LemmaScript tracks seen values in a Set; this is the nested-loop form, the outer
        // invariant saying no pair starting before i is a duplicate.
        [group: 'LemmaScript port', name: 'containsDuplicate', ok: true,
         src: tc('''class C {
                        /** Reports whether any value occurs twice. */
                        @Ensures({ !result ==> (0..<nums.length).every { int a -> (a + 1..<nums.length).every { int b -> nums[a] != nums[b] } } })
                        static boolean containsDuplicate(int[] nums) {
                            int i = 0
                            @Invariant({ 0 <= i && i <= nums.length })
                            @Invariant({ (0..<i).every { int a -> (a + 1..<nums.length).every { int b -> nums[a] != nums[b] } } })
                            @Decreases({ nums.length - i })
                            while (i < nums.length) {
                                int j = i + 1
                                @Invariant({ 0 <= i && i < j && j <= nums.length })
                                @Invariant({ (i + 1..<j).every { int b -> nums[i] != nums[b] } })
                                @Decreases({ nums.length - j })
                                while (j < nums.length) {
                                    if (nums[i] == nums[j]) return true
                                    j = j + 1
                                }
                                i = i + 1
                            }
                            return false
                        }
                    }''')],
        // zigzag.ts — Protocol Buffers' signed-to-unsigned fold, and its round-trip laws. Proved over mathematical
        // integers, the same model LemmaScript's `number` gets.
        [group: 'LemmaScript port', name: 'zigzag round trips', ok: true,
         src: tc('''class C {
                        /** Folds a signed integer onto a non-negative zigzag code. */
                        @Ensures({ result >= 0 && result == (n >= 0 ? 2 * n : -2 * n - 1) })
                        static int encode(int n) { n >= 0 ? 2 * n : -2 * n - 1 }

                        /** Unfolds a zigzag code back to its signed integer: the integer whose code it is. */
                        @Requires({ z >= 0 })
                        @Ensures({ z == (result >= 0 ? 2 * result : -2 * result - 1) })
                        static int decode(int z) { z % 2 == 0 ? z.intdiv(2) : -(z + 1).intdiv(2) }

                        /** Decoding an encoded integer recovers it. */
                        @Ensures({ result == n })
                        static int roundTrip(int n) { decode(encode(n)) }

                        /** Encoding a decoded code recovers it. */
                        @Requires({ z >= 0 })
                        @Ensures({ result == z })
                        static int reverseRoundTrip(int z) { encode(decode(z)) }
                    }''')],
        // The same encode on Java's 32-bit int: @CheckOverflow finds the doubling overflows at both ends — a
        // fact about Java's int that a proof over unbounded integers cannot see.
        [group: 'LemmaScript port', name: 'zigzag encode overflows 32-bit int', expect: 'multiplication overflows 32-bit signed range',
         src: tc('''class C {
                        @CheckOverflow
                        @Ensures({ result >= 0 })
                        static int encode(int n) { n >= 0 ? 2 * n : -2 * n - 1 }
                    }''')],
        // counter.ts — a class with a bounded count.
        [group: 'LemmaScript port', name: 'Counter', ok: true,
         src: tc('''class Counter {
                        int count = 0
                        final int max

                        Counter(int max) { this.max = max }

                        /** Advances the count, returning its previous value. */
                        @Requires({ count < max })
                        @Ensures({ count <= max && result == old.count })
                        int increment() { int o = count; count = count + 1; return o }

                        /** Reports whether the count has reached its bound. */
                        @Ensures({ result == (count >= max) })
                        boolean isAtMax() { count >= max }
                    }''')],
        // maxSpread.ts — `Math.max(...scores)` is Groovy's own `scores.max()`.
        [group: 'LemmaScript port', name: 'highScore', ok: true,
         src: tc('''class C {
                        /** Returns the highest of a non-empty set of scores. */
                        @Requires({ scores != null && scores.length > 0 })
                        @Ensures({ (0..<scores.length).every { scores[it] <= result } })
                        static int highScore(int[] scores) { scores.max() }
                    }''')],
        // pruneWindow (the front page's core.verified.ts), as a loop, with both of LemmaScript's postconditions. The
        // window bound needs the precondition's `t <= now` inside the loop, which Phase 320 restored (a `[]` prefix
        // used to drop every loop-stable @Requires).
        [group: 'LemmaScript port', name: 'pruneWindow', ok: true,
         src: tc('''class C {
                        /** Keeps only the requests still inside the sliding time window. */
                        @Requires({ log != null && log.every { int t -> t <= now } })
                        @Ensures({ result.size() <= log.size() })
                        @Ensures({ result.every { int t -> now - w < t && t <= now } })
                        static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
                            List<Integer> out = []
                            int i = 0
                            @Invariant({ 0 <= i && i <= log.size() && out.size() <= i })
                            @Invariant({ out.every { int t -> now - w < t && t <= now } })
                            @Decreases({ log.size() - i })
                            while (i < log.size()) {
                                if (log[i] > now - w) out.add(log[i])
                                i = i + 1
                            }
                            return out
                        }
                    }''')],
        // pruneWindow as LemmaScript writes it: recurse on the tail, rebuild with the head. log.slice(1) is
        // log.drop(1), and [log[0], ...rest] is [log[0]] + rest (Phase 323).
        [group: 'LemmaScript port', name: 'pruneWindow recursive', ok: true,
         src: tc('''class C {
                        /** Keeps only the requests still inside the sliding time window. */
                        @Requires({ log != null && log.every { int t -> t <= now } })
                        @Ensures({ result.size() <= log.size() })
                        @Ensures({ result.every { int t -> now - w < t && t <= now } })
                        @Decreases({ log.size() })
                        static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
                            if (log.isEmpty()) return []
                            List<Integer> rest = pruneWindow(log.drop(1), now, w)
                            if (log[0] > now - w) return [log[0]] + rest
                            return rest
                        }
                    }''')],
        // allocate (the front page's second story), fixed: floor each share, then hand the leftover back out. The
        // first loop's invariant is the lemma LemmaScript needs separately: flooring loses at most W - 1 per share, so
        // the leftover is below weights.length and result[k] stays in bounds. Nonlinear (total * w / W) beside the
        // quantified sums — Phase 321's sliced retry — plus the range-store sum law for both loops' stores.
        [group: 'LemmaScript port', name: 'allocate', ok: true,
         src: tc('''class C {
                        /** Splits total across the weights without losing any of it. */
                        @Requires({ weights != null && total >= 0 && weights.every { int w -> w >= 0 } && weights.sum() > 0 })
                        @Ensures({ result.sum() == total })
                        static int[] allocate(int total, int[] weights) {
                            int W = weights.sum()
                            int[] result = new int[weights.length]
                            int s = 0
                            int p = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= weights.length && result.length == weights.length })
                            @Invariant({ s == result[0..<i].sum(0) && p == weights[0..<i].sum(0) })
                            @Invariant({ s * W <= total * p && total * p <= s * W + i * (W - 1) })
                            @Decreases({ weights.length - i })
                            while (i < weights.length) {
                                result[i] = (total * weights[i]).intdiv(W)
                                s = s + result[i]
                                p = p + weights[i]
                                i = i + 1
                            }
                            int left = total - s
                            int k = 0
                            @Invariant({ 0 <= k && 0 <= left && result.length == weights.length })
                            @Invariant({ k + left < weights.length + (left == 0 ? 1 : 0) })
                            @Invariant({ result.sum() + left == total })
                            @Decreases({ left })
                            while (left > 0) {
                                result[k] = result[k] + 1
                                k = k + 1
                                left = left - 1
                            }
                            return result
                        }
                    }''')],
        // The agent's first attempt stops after flooring: allocate(10, [1, 1, 1]) is [3, 3, 3]. Not proved; the
        // solver can't build a counterexample through the recursive sum axioms, so it is "could not decide".
        [group: 'LemmaScript port', name: 'allocate first attempt loses the remainder', expect: 'Cannot prove postcondition of allocate',   // Phase 384: refuted (a bounded sum witness), not undecided
         src: tc('''class C {
                        @Requires({ weights != null && total >= 0 && weights.every { int w -> w >= 0 } && weights.sum() > 0 })
                        @Ensures({ result.sum() == total })
                        static int[] allocate(int total, int[] weights) {
                            int W = weights.sum()
                            int[] result = new int[weights.length]
                            int s = 0
                            int p = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= weights.length && result.length == weights.length })
                            @Invariant({ s == result[0..<i].sum(0) && p == weights[0..<i].sum(0) })
                            @Invariant({ s * W <= total * p && total * p <= s * W + i * (W - 1) })
                            @Decreases({ weights.length - i })
                            while (i < weights.length) {
                                result[i] = (total * weights[i]).intdiv(W)
                                s = s + result[i]
                                p = p + weights[i]
                                i = i + 1
                            }
                            return result
                        }
                    }''')],
        // Without the leftover lemma (drop the W - 1 slack), nothing bounds k, and result[k] may be out of bounds.
        [group: 'LemmaScript port', name: 'allocate without the leftover lemma', expect: 'index may be out of bounds',
         src: tc('''class C {
                        @Requires({ weights != null && total >= 0 && weights.every { int w -> w >= 0 } && weights.sum() > 0 })
                        @Ensures({ result.sum() == total })
                        static int[] allocate(int total, int[] weights) {
                            int W = weights.sum()
                            int[] result = new int[weights.length]
                            int s = 0
                            int p = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= weights.length && result.length == weights.length })
                            @Invariant({ s == result[0..<i].sum(0) && p == weights[0..<i].sum(0) })
                            @Invariant({ s * W <= total * p })
                            @Decreases({ weights.length - i })
                            while (i < weights.length) {
                                result[i] = (total * weights[i]).intdiv(W)
                                s = s + result[i]
                                p = p + weights[i]
                                i = i + 1
                            }
                            int left = total - s
                            int k = 0
                            @Invariant({ 0 <= k && 0 <= left && result.length == weights.length })
                            @Invariant({ result.sum() + left == total })
                            @Decreases({ left })
                            while (left > 0) {
                                result[k] = result[k] + 1
                                k = k + 1
                                left = left - 1
                            }
                            return result
                        }
                    }''')],
    ]
}
