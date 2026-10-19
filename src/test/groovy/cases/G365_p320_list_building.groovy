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
 * 'P320 list building' — gap 5 of the LemmaScript ports. Two changes: a list / map / array literal before a loop no
 * longer makes the write-set analysis give up (which had dropped every loop-stable @Requires, so pruneWindow's window
 * bound couldn't see `t <= now`), and `src.findAll { p }` is modelled as a list no longer than src whose elements all
 * pass p and come from src.
 */
class G365_p320_list_building {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 320 list building (gap 5 of the LemmaScript ports): element facts about what a loop appended with add prove (in either spelling, out.every { t -> … } or (0..<out.size()).every { k -> … out[k] … }); a list, map or array literal before the loop no longer makes the write-set analysis bail, which had silently dropped every loop-stable @Requires from preservation and progress; and src.findAll { p } is modelled as a fresh non-null list with 0 <= size <= src.size() whose every element passes p and is drawn from src. Not claimable from findAll: completeness (every passing element kept), order, duplicates. Recursion that rebuilds a list (drop / [x] + rest / a list-valued recursive result) remains outside.'

    static final List<Map> CASES = [

        // ---------- the literal-prefix fix: loop-stable preconditions survive a `[]` before the loop ----------
        // The precondition says every log entry is <= now; the loop never writes log, so it holds inside the loop.
        // A `List out = []` in the prefix made the write-set bail as "unknown expression", and it was dropped.
        [group: 'P320 list building', name: 'a precondition reaches a loop after a list literal', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && (0..<xs.size()).every { int k -> xs[k] <= cap } })
                        @Ensures({ (0..<result.size()).every { int k -> result[k] <= cap } })
                        static List<Integer> copy(List<Integer> xs, int cap) {
                            List<Integer> out = []
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && out.size() == i })
                            @Invariant({ (0..<out.size()).every { int k -> out[k] <= cap } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                out.add(xs[i])
                                i = i + 1
                            }
                            return out
                        }
                    }''')],
        // …and after an array literal and a map literal (the same bail).
        [group: 'P320 list building', name: 'a precondition reaches a loop after array and map literals', ok: true,
         src: tc('''class C {
                        @Requires({ a != null && n >= 0 && n <= a.length && (0..<a.length).every { int k -> a[k] >= 0 } })
                        @Ensures({ result >= 0 })
                        static int sum(int[] a, int n) {
                            int[] seen = [1, 2]
                            Map<String, Integer> m = [x: 1]
                            int s = 0
                            int i = 0
                            @Invariant({ 0 <= i && i <= n && s >= 0 })
                            @Decreases({ n - i })
                            while (i < n) {
                                s = s + a[i]
                                i = i + 1
                            }
                            return s
                        }
                    }''')],

        // ---------- element facts about what add appended ----------
        // A conditional add: everything kept passes the filter (indexed spelling).
        [group: 'P320 list building', name: 'a filter loop keeps only passing elements (indexed)', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ (0..<result.size()).every { int k -> result[k] > 0 } })
                        static List<Integer> pos(List<Integer> xs) {
                            List<Integer> out = []
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && out.size() <= i })
                            @Invariant({ (0..<out.size()).every { int k -> out[k] > 0 } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                if (xs[i] > 0) out.add(xs[i])
                                i = i + 1
                            }
                            return out
                        }
                    }''')],
        // An unconditional add: the k-th element is known exactly.
        [group: 'P320 list building', name: 'a map loop knows each appended element', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.size() == xs.size() && (0..<xs.size()).every { int k -> result[k] == 2 * xs[k] } })
                        static List<Integer> dbl(List<Integer> xs) {
                            List<Integer> out = []
                            int i = 0
                            @Invariant({ 0 <= i && i <= xs.size() && out.size() == i })
                            @Invariant({ (0..<i).every { int k -> out[k] == 2 * xs[k] } })
                            @Decreases({ xs.size() - i })
                            while (i < xs.size()) {
                                out.add(2 * xs[i])
                                i = i + 1
                            }
                            return out
                        }
                    }''')],

        // ---------- findAll ----------
        [group: 'P320 list building', name: 'findAll keeps only passing elements', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.every { int t -> t > 0 } })
                        static List<Integer> pos(List<Integer> xs) {
                            return xs.findAll { int t -> t > 0 }
                        }
                    }''')],
        // The lower bound from the predicate, the upper bound from the precondition through membership.
        [group: 'P320 list building', name: 'pruneWindow by findAll', ok: true,
         src: tc('''class C {
                        /** Keeps only the requests still inside the sliding time window. */
                        @Requires({ log != null && log.every { int t -> t <= now } })
                        @Ensures({ result.size() <= log.size() })
                        @Ensures({ result.every { int t -> now - w < t && t <= now } })
                        static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
                            return log.findAll { int t -> t > now - w }
                        }
                    }''')],
        // A findAll local, indexed after a size check (the implicit `it` predicate).
        [group: 'P320 list building', name: 'a findAll local can be indexed', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result >= 0 })
                        static int first(List<Integer> xs) {
                            List<Integer> ps = xs.findAll { it > 0 }
                            if (ps.size() == 0) return 0
                            return ps[0]
                        }
                    }''')],
        // The soundness half: each of these must not prove. Which elements are kept isn't claimed…
        [group: 'P320 list building', name: 'findAll completeness is not claimable', expect: 'Cannot prove postcondition of pos',
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.size() == xs.size() })
                        static List<Integer> pos(List<Integer> xs) {
                            return xs.findAll { int t -> t > 0 }
                        }
                    }''')],
        // …nor their order (Groovy keeps it, but the model doesn't claim it: a sound miss)…
        [group: 'P320 list building', name: 'findAll order is not claimable', expect: 'Cannot prove postcondition of pos',
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() >= 2 && xs[0] > 0 && xs[1] > 0 })
                        @Ensures({ result[0] == xs[0] })
                        static List<Integer> pos(List<Integer> xs) {
                            return xs.findAll { int t -> t > 0 }
                        }
                    }''')],
        // …nor anything stronger than the predicate…
        [group: 'P320 list building', name: 'findAll gives no more than its predicate', expect: 'Cannot prove postcondition of pos',
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.every { int t -> t > 1 } })
                        static List<Integer> pos(List<Integer> xs) {
                            return xs.findAll { int t -> t > 0 }
                        }
                    }''')],
        // …and a later mutation of the result is seen.
        [group: 'P320 list building', name: 'an add after findAll is seen', expect: 'Cannot prove postcondition of pos',
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.every { int t -> t > 0 } })
                        static List<Integer> pos(List<Integer> xs) {
                            List<Integer> ps = xs.findAll { it > 0 }
                            ps.add(-1)
                            return ps
                        }
                    }''')],
        // The receiver may still be null.
        [group: 'P320 list building', name: 'findAll on a possibly-null list is a dereference', expect: 'Possible NullPointerException: Cannot invoke method findAll() on null object',
         src: tc('''class C {
                        @Ensures({ result.every { int t -> t > 0 } })
                        static List<Integer> pos(List<Integer> xs) {
                            return xs.findAll { int t -> t > 0 }
                        }
                    }''')],
    ]
}
