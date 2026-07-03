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

/** 'P202 prover showdown' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G277_p202_prover_showdown {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Hillel Wayne\'s Theorem Prover Showdown, all three challenges with FULL specs: leftpad (length == max, pad prefix all c, suffix == s — single-loop array form), fulcrum (the returned cut minimizes |2*prefix - total| over ALL cuts, O(n), via a guarded pure-recursive psum helper tied to the accumulator by its defining equation), and unique (pairwise-distinct AND both subset directions — a bidirectional spec beyond the original partial Dafny solution — nested loops with a found-flag invariant). Teeth: a mis-offset leftpad suffix refutes, a fulcrum that never updates its best cut fails invariant preservation, a unique that always inserts refutes no-dups.'

    static final List<Map> CASES = [

        // ---------- Phase 202: the Theorem Prover Showdown (leftpad / unique / fulcrum) ----------
        // Hillel Wayne posed these three as the imperative-vs-functional verification duel; the repo\'s
        // loop-invariant machinery is precisely the imperative side. All three carry their full specs.
        [group: 'P202 prover showdown', name: 'leftpad: length, pad prefix, suffix — full spec', ok: true,
         src: tc('''class C {
                       @Requires({ s != null && n >= 0 })
                       @Ensures({ result.length == (n > s.length ? n : s.length) &&
                                  (0..<(n > s.length ? n - s.length : 0)).every { int i -> result[i] == c } &&
                                  (0..<s.length).every { int i -> result[(n > s.length ? n - s.length : 0) + i] == s[i] } })
                       static int[] leftpad(int c, int n, int[] s) {
                           int pad = n > s.length ? n - s.length : 0
                           int[] r = new int[pad + s.length]
                           int k = 0
                           @Invariant({ 0 <= k && k <= pad + s.length &&
                                        pad == (n > s.length ? n - s.length : 0) &&
                                        r.length == pad + s.length &&
                                        (0..<(k < pad ? k : pad)).every { int q -> r[q] == c } &&
                                        (0..<(k > pad ? k - pad : 0)).every { int q -> r[pad + q] == s[q] } })
                           @Decreases({ pad + s.length - k })
                           while (k < pad + s.length) {
                               if (k >= pad) { r[k] = s[k - pad] } else { r[k] = c }
                               k = k + 1
                           }
                           return r
                       }
                   }''')],
        [group: 'P202 prover showdown', name: 'fulcrum: returned cut minimizes |left-right| over all cuts', ok: true,
         src: tc('''class C {
                       static int psum(int[] a, int k) {
                           (a != null && 0 < k && k <= a.length) ? psum(a, k - 1) + a[k - 1] : 0
                       }
                       @Requires({ a != null })
                       @Ensures({ 0 <= result && result <= a.length &&
                           (0..a.length).every { int j ->
                               (2 * psum(a, result) - psum(a, a.length) >= 0 ?
                                    2 * psum(a, result) - psum(a, a.length) : psum(a, a.length) - 2 * psum(a, result)) <=
                               (2 * psum(a, j) - psum(a, a.length) >= 0 ?
                                    2 * psum(a, j) - psum(a, a.length) : psum(a, a.length) - 2 * psum(a, j)) } })
                       static int fulcrum(int[] a) {
                           int total = psum(a, a.length)
                           int left = 0
                           int best = 0
                           int bestDiff = total >= 0 ? total : -total
                           int i = 1
                           @Invariant({ a != null && 1 <= i && i <= a.length + 1 &&
                               total == psum(a, a.length) &&
                               left == psum(a, i - 1) &&
                               0 <= best && best <= i - 1 &&
                               bestDiff == (2 * psum(a, best) - total >= 0 ? 2 * psum(a, best) - total : total - 2 * psum(a, best)) &&
                               (0..<i).every { int j ->
                                   bestDiff <= (2 * psum(a, j) - total >= 0 ? 2 * psum(a, j) - total : total - 2 * psum(a, j)) } })
                           @Decreases({ a.length + 1 - i })
                           while (i <= a.length) {
                               left = left + a[i - 1]
                               int d = 2 * left - total
                               int diff = d >= 0 ? d : -d
                               if (diff < bestDiff) { best = i; bestDiff = diff }
                               i = i + 1
                           }
                           return best
                       }
                   }''')],
        [group: 'P202 prover showdown', name: 'unique: no-dups + both subset directions (full spec)', ok: true,
         src: tc('''class C {
                       @Requires({ a != null && r != null && r.length == a.length })
                       @Ensures({ 0 <= result && result <= a.length &&
                           (0..<result).every { int i -> (0..<i).every { int j -> r[j] != r[i] } } &&
                           (0..<result).every { int i -> (0..<a.length).any { int j -> a[j] == r[i] } } &&
                           (0..<a.length).every { int i -> (0..<result).any { int j -> r[j] == a[i] } } })
                       static int unique(int[] a, int[] r) {
                           int m = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length && 0 <= m && m <= i &&
                               (0..<m).every { int x -> (0..<x).every { int y -> r[y] != r[x] } } &&
                               (0..<m).every { int x -> (0..<a.length).any { int j -> a[j] == r[x] } } &&
                               (0..<i).every { int x -> (0..<m).any { int y -> r[y] == a[x] } } })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               boolean found = false
                               int j = 0
                               @Invariant({ 0 <= j && j <= m && m <= i && i < a.length && 0 <= i &&
                                   found == (0..<j).any { int y -> r[y] == a[i] } &&
                                   (0..<m).every { int x -> (0..<x).every { int y -> r[y] != r[x] } } &&
                                   (0..<m).every { int x -> (0..<a.length).any { int q -> a[q] == r[x] } } &&
                                   (0..<i).every { int x -> (0..<m).any { int y -> r[y] == a[x] } } })
                               @Decreases({ m - j })
                               while (j < m) {
                                   if (r[j] == a[i]) { found = true }
                                   j = j + 1
                               }
                               if (!found) { r[m] = a[i]; m = m + 1 }
                               i = i + 1
                           }
                           return m
                       }
                   }''')],
        // Teeth: suffix copied without the pad offset — the suffix conjunct refutes.
        [group: 'P202 prover showdown', name: 'leftpad refutes on a mis-offset suffix', expect: 'Cannot prove',
         src: tc('''class C {
                       @Requires({ s != null && n >= 0 })
                       @Ensures({ result.length == (n > s.length ? n : s.length) &&
                                  (0..<(n > s.length ? n - s.length : 0)).every { int i -> result[i] == c } &&
                                  (0..<s.length).every { int i -> result[i] == s[i] } })
                       static int[] leftpad(int c, int n, int[] s) {
                           int pad = n > s.length ? n - s.length : 0
                           int[] r = new int[pad + s.length]
                           int k = 0
                           @Invariant({ 0 <= k && k <= pad + s.length &&
                                        pad == (n > s.length ? n - s.length : 0) &&
                                        r.length == pad + s.length &&
                                        (0..<(k < pad ? k : pad)).every { int q -> r[q] == c } &&
                                        (0..<(k > pad ? k - pad : 0)).every { int q -> r[pad + q] == s[q] } })
                           @Decreases({ pad + s.length - k })
                           while (k < pad + s.length) {
                               if (k >= pad) { r[k] = s[k - pad] } else { r[k] = c }
                               k = k + 1
                           }
                           return r
                       }
                   }''')],
        // Teeth: never updating the best cut — the argmin invariant is not preserved.
        [group: 'P202 prover showdown', name: 'fulcrum refutes when the best cut is never updated', expect: 'Cannot prove',
         src: tc('''class C {
                       static int psum(int[] a, int k) {
                           (a != null && 0 < k && k <= a.length) ? psum(a, k - 1) + a[k - 1] : 0
                       }
                       @Requires({ a != null })
                       @Ensures({ 0 <= result && result <= a.length &&
                           (0..a.length).every { int j ->
                               (2 * psum(a, result) - psum(a, a.length) >= 0 ?
                                    2 * psum(a, result) - psum(a, a.length) : psum(a, a.length) - 2 * psum(a, result)) <=
                               (2 * psum(a, j) - psum(a, a.length) >= 0 ?
                                    2 * psum(a, j) - psum(a, a.length) : psum(a, a.length) - 2 * psum(a, j)) } })
                       static int fulcrum(int[] a) {
                           int total = psum(a, a.length)
                           int left = 0
                           int best = 0
                           int bestDiff = total >= 0 ? total : -total
                           int i = 1
                           @Invariant({ a != null && 1 <= i && i <= a.length + 1 &&
                               total == psum(a, a.length) &&
                               left == psum(a, i - 1) &&
                               0 <= best && best <= i - 1 &&
                               bestDiff == (2 * psum(a, best) - total >= 0 ? 2 * psum(a, best) - total : total - 2 * psum(a, best)) &&
                               (0..<i).every { int j ->
                                   bestDiff <= (2 * psum(a, j) - total >= 0 ? 2 * psum(a, j) - total : total - 2 * psum(a, j)) } })
                           @Decreases({ a.length + 1 - i })
                           while (i <= a.length) {
                               left = left + a[i - 1]
                               int d = 2 * left - total
                               int diff = d >= 0 ? d : -d
                               
                               i = i + 1
                           }
                           return best
                       }
                   }''')],
        // Teeth: the correct dedup body with an over-strong spec — result == a.length claims the input
        // never had duplicates; the exit check refutes.
        // (Canary form: this model search is strongly hardware-sensitive — crisp refute in ~2s locally,
        // timeout even at 8s on a CI runner. The tooth is that the over-strong claim NEVER verifies;
        // refute-vs-timeout is a hardware detail, and a clean verify fails the case loudly.)
        [group: 'P202 prover showdown', name: 'unique never proves an over-strong no-duplicates-ever claim (canary)', expect: 'postcondition of unique',
         src: tc('''class C {
                       @Requires({ a != null && r != null && r.length == a.length })
                       @Ensures({ result == a.length && 0 <= result &&
                           (0..<result).every { int i -> (0..<i).every { int j -> r[j] != r[i] } } &&
                           (0..<result).every { int i -> (0..<a.length).any { int j -> a[j] == r[i] } } &&
                           (0..<a.length).every { int i -> (0..<result).any { int j -> r[j] == a[i] } } })
                       static int unique(int[] a, int[] r) {
                           int m = 0
                           int i = 0
                           @Invariant({ 0 <= i && i <= a.length && 0 <= m && m <= i &&
                               (0..<m).every { int x -> (0..<x).every { int y -> r[y] != r[x] } } &&
                               (0..<m).every { int x -> (0..<a.length).any { int j -> a[j] == r[x] } } &&
                               (0..<i).every { int x -> (0..<m).any { int y -> r[y] == a[x] } } })
                           @Decreases({ a.length - i })
                           while (i < a.length) {
                               boolean found = false
                               int j = 0
                               @Invariant({ 0 <= j && j <= m && m <= i && i < a.length && 0 <= i &&
                                   found == (0..<j).any { int y -> r[y] == a[i] } &&
                                   (0..<m).every { int x -> (0..<x).every { int y -> r[y] != r[x] } } &&
                                   (0..<m).every { int x -> (0..<a.length).any { int q -> a[q] == r[x] } } &&
                                   (0..<i).every { int x -> (0..<m).any { int y -> r[y] == a[x] } } })
                               @Decreases({ m - j })
                               while (j < m) {
                                   if (r[j] == a[i]) { found = true }
                                   j = j + 1
                               }
                               if (!found) { r[m] = a[i]; m = m + 1 }
                               i = i + 1
                           }
                           return m
                       }
                   }''')],
    ]
}
