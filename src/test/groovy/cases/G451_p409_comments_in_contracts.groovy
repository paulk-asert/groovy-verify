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
 * 'P409 comments in contracts' — found re-checking the blog post's examples. A contract's text is captured verbatim
 * (power-assert's SourceText) and re-parsed for the encoder, and SourceText joins a multi-line slice into one line. A
 * `//` comment inside it then swallowed everything after it: `result == x // the identity` / `&& result > x` came
 * back as `result == x`, and a wrong postcondition, class invariant or precondition was checked only up to the
 * comment, silently. After a trailing `&&` the text no longer parsed: an @Ensures skipped loudly, but a @Requires or a
 * class @Invariant was dropped without a word. Line comments are left out of the slice now (not one inside a string or
 * a block comment), and a multi-line capture must re-parse to the expression written, or it is a compile error.
 */
class G451_p409_comments_in_contracts {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 409: a `//` comment inside a multi-line contract no longer swallows the rest of it — the captured text leaves line comments out (not one in a string or block comment), and a multi-line capture must re-parse to the expression written (soundness fix)."

    static final List<Map> CASES = [

        // Unsound before: compiled cleanly — only `result == x` was checked
        [group: "P409 comments in contracts", name: "a comment after a conjunct no longer hides the next (@Ensures)",
         expect: ["Cannot prove postcondition of f", "fails on: f("],
         src: tc('''class C {
                        @Ensures({ result == x       // the identity
                                   && result > x })
                        static int f(int x) { x }
                    }''')],

        // Unsound before: compiled cleanly — only `count >= 0` was checked
        [group: "P409 comments in contracts", name: "… a class @Invariant",
         expect: ["Cannot prove class invariant of bump", "fails on: bump()"],
         src: tc('''@Invariant({ count >= 0     // never negative
                                  && count <= 5 })
                    class C {
                        int count
                        void bump() { count = count + 10 }
                    }''')],

        // Unsound before: the call site was held only to `x > 0`
        [group: "P409 comments in contracts", name: "… a @Requires, at a call site",
         expect: "Cannot prove precondition of f at this call site",
         src: tc('''class C {
                        @Requires({ x > 0      // positive
                                    && x < 10 })
                        static int f(int x) { x }
                        static int g() { f(50) }
                    }''')],

        // Unsound before: compiled cleanly — the text after the comment ended in `&&`, and the invariant was dropped
        [group: "P409 comments in contracts", name: "a comment after a trailing `&&`: a class @Invariant is checked",
         expect: "Cannot prove class invariant of bump",
         src: tc('''@Invariant({ count >= 0 &&   // never negative
                                  count <= 5 })
                    class C {
                        int count
                        void bump() { count = count + 10 }
                    }''')],

        // A false positive before: the @Requires was dropped, and `a[i]` failed on `f(new int[0], -1)`
        [group: "P409 comments in contracts", name: "… a @Requires is assumed",
         ok: true,
         src: tc('''class C {
                        @Requires({ 0 <= i &&        // lower
                                    i < a.length })  // upper
                        static int f(int[] a, int i) { a[i] }
                    }''')],

        // Skipped before ("contract source was not captured"); now it is checked, and refutes
        [group: "P409 comments in contracts", name: "… an @Ensures is checked",
         expect: ["Cannot prove postcondition of f", "fails on: f("],
         refute: "Skipped verification of postcondition",
         src: tc('''class C {
                        @Ensures({ result >= 0 &&     // non-negative
                                   result == x + 1 })
                        static int f(int x) { x }
                    }''')],

        // A `//` in a string literal or a block comment is no comment
        [group: "P409 comments in contracts", name: "a `//` inside a string is kept",
         ok: true,
         src: tc('''class C {
                        @Ensures({ result == 'http://a'   // the url
                                   && result.length() == 8 })
                        static String f() { 'http://a' }
                    }''')],

        [group: "P409 comments in contracts", name: "… and so is what follows it",
         expect: "Cannot prove postcondition of f",
         src: tc('''class C {
                        @Ensures({ result == 'http://a'   // the url
                                   && result.length() == 9 })
                        static String f() { 'http://a' }
                    }''')],

        [group: "P409 comments in contracts", name: "a `//` inside a block comment is no line comment",
         expect: ["Cannot prove postcondition of f", "fails on: f("],
         src: tc('''class C {
                        @Ensures({ result == x /* see http://x */ &&
                                   result > x })
                        static int f(int x) { x }
                    }''')],

        // The blog post's and README's spelling: the suite's insertion sort with its comments, which proves
        [group: "P409 comments in contracts", name: "the insertion sort with comments in its contracts",
         ok: true,
         src: tc('''final class C {
                       int[] a
                       // lemma: every element of an adjacent-sorted prefix [0,k] is <= a[k], by induction on k.
                       @Requires({ 0 <= k && k < a.length && (0..<k).every { a[it] <= a[it + 1] } })
                       @Ensures({ (0..<k + 1).every { a[it] <= a[k] } })
                       @Decreases({ k })
                       void maxBound(int k) {
                           if (k > 0) maxBound(k - 1)
                       }
                       @Requires({ 0 <= m && m < a.length &&
                                   (0..<m - 1).every { a[it] <= a[it + 1] } &&   // prefix sorted
                                   (0..<m + 1).every { a[it] <= hi } })           // active region bounded by hi
                       @Modifies({ this.a })
                       @Ensures({ (0..<m).every { a[it] <= a[it + 1] } &&         // a[0..m] now sorted
                                  (0..<m + 1).every { a[it] <= hi } &&            // bound preserved
                                  (m + 1..<a.length).every { a[it] == old.a[it] } && // suffix framed (untouched)
                                  a.count(v) == old.a.count(v) })                 // permutation
                       @Decreases({ m })
                       void insert(int m, int hi, int v) {
                           if (m > 0 && a[m] < a[m - 1]) {
                               maxBound(m - 1)                                     // the new pivot bounds the prefix
                               int t = a[m]; a[m] = a[m - 1]; a[m - 1] = t
                               insert(m - 1, a[m], v)                              // recurse with the pivot as the bound
                           }
                       }
                       @Requires({ 0 <= n && n <= a.length && (0..<n).every { a[it] <= hi } })
                       @Modifies({ this.a })
                       @Ensures({ (n == 0 || (0..<n - 1).every { a[it] <= a[it + 1] }) &&
                                  (0..<n).every { a[it] <= hi } &&
                                  (n..<a.length).every { a[it] == old.a[it] } &&
                                  a.count(v) == old.a.count(v) })
                       @Decreases({ n })
                       void sort(int n, int hi, int v) {
                           if (n > 1) { sort(n - 1, hi, v); insert(n - 1, hi, v) }
                       }
                   }''')],
    ]
}
