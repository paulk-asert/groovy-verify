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
 * 'P318 loop frame' — the loop VCs (preservation, progress, the post-loop use, in-body exits and the body's implicit
 * obligations) started from the invariant, the guard and the loop-stable @Requires only, so a local the prefix set
 * and the loop never touches had lost its value there. They now assume the prefix's FRAME facts: `x == e` for an
 * assignment neither of whose sides the loop or the rest of the prefix writes, and `x != null` (with `x.length` for
 * an array) for an allocation the loop only writes the contents of.
 */
class G363_p318_loop_frame {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 318 loop frame facts (gap 3 of the LemmaScript ports): a local the prefix sets and the loop never touches keeps its value at the loop head, in the body and after the loop, as in Dafny, so it needs no invariant restating it. Value facts `x == e` for a prefix assignment when neither x nor anything pure e reads is written by the loop or the rest of the prefix; shape facts `x != null` (and `x.length == len` for an array) for an allocation the loop only writes the contents of (an element store or a list mutator). Never framed: anything the loop reassigns, a source the loop writes, a list\'s size, an array\'s contents, a self-referencing update, a local assigned in any closure, and every fact when the loop\'s writes cannot be bounded.'

    static final List<Map> CASES = [

        // LemmaScript's leftPad with exactly its own invariants: `n` is set before the loop and never written in it.
        [group: 'P318 loop frame', name: 'leftPad\'s shortfall survives the loop unrestated', ok: true,
         src: tc("""class C {
                        @Requires({ str != null && ch != null && ch.length() == 1 && len >= 0 })
                        @Ensures({ str.length() < len ==> result.length() == len })
                        static String leftPad(String str, int len, String ch) {
                            String result = str
                            int n = len - str.length()
                            int i = 0
                            @Invariant({ i >= 0 && result.length() == str.length() + i })
                            @Invariant({ n > 0 ==> i <= n })
                            @Decreases({ n - i })
                            while (i < n) { result = ch + result; i = i + 1 }
                            return result
                        }
                    }""")],
        // The plainest case: `m = k`, and the loop reads m but never writes it.
        [group: 'P318 loop frame', name: 'a local copy of a parameter keeps its value through the loop', ok: true,
         src: tc("""class C {
                        @Requires({ k >= 0 })
                        @Ensures({ result == 2 * k })
                        static int twice(int k) {
                            int m = k
                            int i = 0
                            int s = 0
                            @Invariant({ 0 <= i && i <= m && s == 2 * i })
                            @Decreases({ m - i })
                            while (i < m) { s = s + 2; i = i + 1 }
                            return s
                        }
                    }""")],
        // An element store changes contents, not length or nullness: `r.length == n` and `r != null` hold throughout.
        [group: 'P318 loop frame', name: 'a filled array keeps its length and non-null', ok: true,
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.length == n })
                        static int[] zeros(int n) {
                            int[] r = new int[n]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { r[i] = 0; i = i + 1 }
                            return r
                        }
                    }""")],
        // A list mutator changes contents and size, never nullness: the add needs no `out != null` invariant.
        [group: 'P318 loop frame', name: 'a list built by add stays non-null', ok: true,
         src: tc("""class C {
                        @Requires({ xs != null })
                        @Ensures({ result.size() <= xs.size() })
                        static List<Integer> pos(List<Integer> xs) {
                            List<Integer> out = []
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && out.size() <= i })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] > 0) out.add(xs[i])
                                i = i + 1
                            }
                            return out
                        }
                    }""")],
        // Already worked before this phase — the stable-@Requires half the frame now generalises.
        [group: 'P318 loop frame', name: 'a precondition over parameters is still used inside the loop (Phase 64)', ok: true,
         src: tc("""class C {
                        @Requires({ a != null && a.length == n && n >= 0 })
                        static int sum(int[] a, int n) {
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { s = s + a[i]; i = i + 1 }
                            return s
                        }
                    }""")],
        // `n = a.length` before the loop bounds `a[i]` in the body: the implicit obligation sees the fact too.
        [group: 'P318 loop frame', name: 'a local bound to an array length bounds the index in the body', ok: true,
         src: tc("""class C {
                        @Requires({ a != null })
                        static int sum(int[] a) {
                            int n = a.length
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { s = s + a[i]; i = i + 1 }
                            return s
                        }
                    }""")],
        // The soundness half: each of these must still be refuted. m is written by the loop.
        [group: 'P318 loop frame', name: 'a local the loop reassigns is not framed', expect: 'Cannot prove postcondition of f',
         src: tc("""class C {
                        @Requires({ k >= 1 })
                        @Ensures({ result == k })
                        static int f(int k) {
                            int m = k
                            int i = 0
                            @Invariant({ 0 <= i && i <= 1 })
                            @Decreases({ 1 - i })
                            while (i < 1) { m = m - 1; i = i + 1 }
                            return m
                        }
                    }""")],
        // t's source, s, is written by the loop: `t == s` would be stale.
        [group: 'P318 loop frame', name: 'a local whose source the loop writes is not framed', expect: 'Cannot prove postcondition of f',
         src: tc("""class C {
                        @Ensures({ result == 0 })
                        static int f() {
                            int s = 0
                            int t = s
                            int i = 0
                            @Invariant({ 0 <= i && i <= 3 })
                            @Decreases({ 3 - i })
                            while (i < 3) { s = s + 1; i = i + 1 }
                            return s - t
                        }
                    }""")],
        // `m = m + 1` reads the OLD m; as a fact (m == m + 1) it would be false and prove everything.
        [group: 'P318 loop frame', name: 'a self-referencing prefix update is never assumed as a fact', expect: 'Cannot prove postcondition of f',
         src: tc("""class C {
                        @Ensures({ result == k })
                        static int f(int k) {
                            int m = k
                            m = m + 1
                            int i = 0
                            @Invariant({ 0 <= i && i <= 1 })
                            @Decreases({ 1 - i })
                            while (i < 1) { i = i + 1 }
                            return m
                        }
                    }""")],
        // …which is also why the true claim isn't proved: neither of m's two assignments is framed.
        [group: 'P318 loop frame', name: 'boundary: a local updated twice before the loop is not framed', expect: 'Cannot prove postcondition of f',
         src: tc("""class C {
                        @Ensures({ result == k + 1 })
                        static int f(int k) {
                            int m = k
                            m = m + 1
                            int i = 0
                            @Invariant({ 0 <= i && i <= 1 })
                            @Decreases({ 1 - i })
                            while (i < 1) { i = i + 1 }
                            return m
                        }
                    }""")],
        // A reassigned array is a different array: its length is the new one's.
        [group: 'P318 loop frame', name: 'an array the loop reassigns keeps no length fact', expect: 'Cannot prove postcondition of f',
         src: tc("""class C {
                        @Requires({ n >= 2 })
                        @Ensures({ result.length == n })
                        static int[] f(int n) {
                            int[] r = new int[n]
                            int i = 0
                            @Invariant({ 0 <= i && i <= 1 })
                            @Decreases({ 1 - i })
                            while (i < 1) { r = new int[1]; i = i + 1 }
                            return r
                        }
                    }""")],
        // add changes the size: only nullness is framed for a list.
        [group: 'P318 loop frame', name: 'a list the loop appends to keeps no size fact', expect: 'Cannot prove postcondition of f',
         src: tc("""class C {
                        @Ensures({ result.size() == 0 })
                        static List<Integer> f() {
                            List<Integer> out = []
                            int i = 0
                            @Invariant({ 0 <= i && i <= 2 })
                            @Decreases({ 2 - i })
                            while (i < 2) { out.add(i); i = i + 1 }
                            return out
                        }
                    }""")],
        // The length fact names n, which the loop then changes.
        [group: 'P318 loop frame', name: 'an array length whose source the loop writes is not framed', expect: 'Cannot prove postcondition of f',
         src: tc("""class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            int[] r = new int[n]
                            int i = 0
                            @Invariant({ 0 <= i && i <= 1 })
                            @Decreases({ 1 - i })
                            while (i < 1) { n = n + 1; i = i + 1 }
                            return r.length
                        }
                    }""")],
        // Element stores do change contents: `r[0] == 0` from the allocation is gone.
        [group: 'P318 loop frame', name: 'an array\'s contents are not framed when the loop stores into it', expect: 'Cannot prove postcondition of f',
         src: tc("""class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result == 0 })
                        static int f(int n) {
                            int[] r = new int[n]
                            int i = 0
                            @Invariant({ 0 <= i && i <= n })
                            @Decreases({ n - i })
                            while (i < n) { r[i] = 5; i = i + 1 }
                            return r[0]
                        }
                    }""")],
    ]
}
