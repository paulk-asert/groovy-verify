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

/**
 * 'P321 nonlinear' — gap 6 of the LemmaScript ports, the money-splitting allocate. Two changes. Z3 handles nonlinear
 * arithmetic and quantified axioms well apart but rarely together, so an UNKNOWN query mixing them is retried on
 * slices: quantifier-free plus bounded ground instances of the axioms, or linear with the axioms kept, and failing
 * that goal conjunct by goal conjunct (Z3Backend). And a store into an array now shifts every range sum over it
 * (the range-store sum law), in loop bodies as well as method bodies, so a fill loop keeps s == r[0..<i].sum(0)
 * and a bump loop keeps r.sum() + left.
 */
class G366_p321_nonlinear {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 321 nonlinear arithmetic (gap 6 of the LemmaScript ports): LemmaScript\'s allocate — floor each share total * w / W, then hand the leftover back out one at a time — ports with its spec result.sum() == total. A query mixing nonlinear arithmetic with quantified axioms that comes back UNKNOWN is retried on sound slices (quantifier-free plus bounded ground instances, or linear with the axioms; then per goal conjunct), which only ever turns UNKNOWN into VERIFIED. A store into an int array shifts every range sum over it by the stored delta, in loop bodies too, so fill and bump loops keep their sum invariants. Wrong claims in this class report "could not decide", not a counterexample: a model for the recursive sum axioms is out of the solver\'s reach.'

    static final List<Map> CASES = [

        // ---------- the floor lemma: scalar, no quantifiers, already in reach ----------
        // Integer division brackets the exact share: q * W <= total * w < q * W + W.
        [group: 'P321 nonlinear', name: 'a floored share is bracketed by the exact one', ok: true,
         src: tc('''class C {
                        @Requires({ W > 0 && total >= 0 && w >= 0 })
                        @Ensures({ result * W <= total * w && total * w < result * W + W })
                        static int share(int total, int w, int W) { (total * w).intdiv(W) }
                    }''')],
        // …and the share isn't exact: 3 * 1 / 2 floors to 1.
        [group: 'P321 nonlinear', name: 'a floored share is not exact', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ W > 0 && total >= 0 && w >= 0 })
                        @Ensures({ result * W == total * w })
                        static int share(int total, int w, int W) { (total * w).intdiv(W) }
                    }''')],

        // ---------- the sliced retry: nonlinear invariants beside a quantified prefix sum ----------
        // The flooring loop: each share loses less than W, so after n shares the total lost is at most n * (W - 1),
        // hence total - sum < n. The arithmetic needs no sum axiom and p == ws[0..<i].sum(0) needs no arithmetic,
        // but in one query Z3 timed out on both preservation and the postcondition.
        [group: 'P321 nonlinear', name: 'flooring loses less than one unit per share', ok: true,
         src: tc('''class C {
                        @Requires({ ws != null && total >= 0 && ws.every { int w -> w >= 0 } && ws.sum() > 0 })
                        @Ensures({ result <= total && total < result + ws.length })
                        static int floored(int total, int[] ws) {
                            int W = ws.sum()
                            int s = 0
                            int p = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= ws.length && p == ws[0..<i].sum(0) })
                            @Invariant({ s * W <= total * p && total * p <= s * W + i * (W - 1) })
                            @Decreases({ ws.length - i })
                            while (i < ws.length) {
                                s = s + (total * ws[i]).intdiv(W)
                                p = p + ws[i]
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        // A slack too tight to hold (each share can lose up to W - 1, not W - 2) is never proved: the slices only
        // ever add VERIFIED for what's true.
        [group: 'P321 nonlinear', name: 'a too-tight flooring slack is not proved', expect: 'Could not decide loop-invariant preservation',
         src: tc('''class C {
                        @Requires({ ws != null && total >= 0 && ws.every { int w -> w >= 0 } && ws.sum() > 0 })
                        @Ensures({ result <= total })
                        static int floored(int total, int[] ws) {
                            int W = ws.sum()
                            int s = 0
                            int p = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= ws.length && p == ws[0..<i].sum(0) })
                            @Invariant({ s * W <= total * p && total * p <= s * W + i * (W - 2) })
                            @Decreases({ ws.length - i })
                            while (i < ws.length) {
                                s = s + (total * ws[i]).intdiv(W)
                                p = p + ws[i]
                                i = i + 1
                            }
                            return s
                        }
                    }''')],

        // ---------- the range-store sum law ----------
        // A fill loop: storing r[i] leaves the prefix r[0..<i] alone, so s == r[0..<i].sum(0) is carried across it.
        [group: 'P321 nonlinear', name: 'a fill loop keeps its prefix sum across the store', ok: true,
         src: tc('''class C {
                        @Requires({ ws != null })
                        @Ensures({ result == ws.sum() })
                        static int copySum(int[] ws) {
                            int[] r = new int[ws.length]
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= ws.length && r.length == ws.length })
                            @Invariant({ s == r[0..<i].sum(0) && s == ws[0..<i].sum(0) })
                            @Decreases({ ws.length - i })
                            while (i < ws.length) {
                                r[i] = ws[i]
                                s = s + r[i]
                                i = i + 1
                            }
                            return s
                        }
                    }''')],
        // A bump loop: r[k] += 1 raises the whole sum by one, so r.sum() + left is constant.
        [group: 'P321 nonlinear', name: 'a bump loop keeps sum plus leftover constant', ok: true,
         src: tc('''class C {
                        @Requires({ r != null && left >= 0 && left <= r.length && r.sum() + left == total })
                        @Ensures({ result == total })
                        static int bump(int[] r, int left, int total) {
                            int k = 0
                            @Invariant({ 0 <= k && 0 <= left && k + left <= r.length && r.sum() + left == total })
                            @Decreases({ left })
                            while (left > 0) {
                                r[k] = r[k] + 1
                                k = k + 1
                                left = left - 1
                            }
                            return r.sum()
                        }
                    }''')],
        // …and bumping by two is caught (no counterexample through the sum axioms, but never proved).
        [group: 'P321 nonlinear', name: 'a bump by two breaks the constant', expect: 'Could not decide loop-invariant preservation',
         src: tc('''class C {
                        @Requires({ r != null && left >= 0 && left <= r.length && r.sum() + left == total })
                        @Ensures({ result == total })
                        static int bump(int[] r, int left, int total) {
                            int k = 0
                            @Invariant({ 0 <= k && 0 <= left && k + left <= r.length && r.sum() + left == total })
                            @Decreases({ left })
                            while (left > 0) {
                                r[k] = r[k] + 2
                                k = k + 1
                                left = left - 1
                            }
                            return r.sum()
                        }
                    }''')],
    ]
}
