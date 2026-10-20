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
 * 'P323 list recursion' — the last list gap of the LemmaScript ports: LemmaScript's recursive pruneWindow, which
 * recurses on log.slice(1) and rebuilds with [log[0], ...rest]. Three list values (src.drop(k), a + b, the spread
 * literal [x, *rest]), list-valued actual arguments hoisted to named lists, and a self-call's list formal no longer
 * overwriting the caller's list of the same name.
 */
class G368_p323_list_recursion {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 323 recursion that rebuilds a list (the last list gap of the LemmaScript ports): src.drop(k) for a literal k >= 0, a concatenation a + b of list literals and named Int lists, and the spread literal [x, *rest] are list values with exact size and element facts; such a value passed as an argument is hoisted to a named list, so precondition, postcondition and termination checks all see it; and a self-call\'s list formal is aliased to its actual only for the call. LemmaScript\'s recursive pruneWindow ports structure for structure. Fixed on the way: a spread literal counted as one slot (proving [x, *xs].size() == 2), and xs + 1 / xs * 2 / xs << x translated the list as an Int (now a loud skip).'

    static final List<Map> CASES = [

        // ---------- list values: drop and concatenation ----------
        [group: 'P323 list recursion', name: 'drop(1) is the list without its head', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result.size() == xs.size() - 1 && (0..<result.size()).every { int k -> result[k] == xs[k + 1] } })
                        static List<Integer> f(List<Integer> xs) { xs.drop(1) }
                    }''')],
        [group: 'P323 list recursion', name: 'drop past the end is empty', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() <= 1 })
                        @Ensures({ result.size() == 0 })
                        static List<Integer> f(List<Integer> xs) { xs.drop(1) }
                    }''')],
        [group: 'P323 list recursion', name: 'drop(1) does not keep the head', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 1 })
                        @Ensures({ result[0] == xs[0] })
                        static List<Integer> f(List<Integer> xs) { xs.drop(1) }
                    }''')],
        [group: 'P323 list recursion', name: '[x] + xs puts x first', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.size() == xs.size() + 1 && result[0] == x })
                        static List<Integer> f(int x, List<Integer> xs) { [x] + xs }
                    }''')],
        // A spread element contributes its whole list. It used to count as one slot, so the next, wrong, claim proved.
        [group: 'P323 list recursion', name: 'a spread literal has the spread list\'s size plus its other elements', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.size() == xs.size() + 1 && result[0] == x })
                        static List<Integer> f(int x, List<Integer> xs) { [x, *xs] }
                    }''')],
        [group: 'P323 list recursion', name: 'a spread literal is not two elements', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.size() == 2 })
                        static List<Integer> f(int x, List<Integer> xs) { [x, *xs] }
                    }''')],
        // `xs + 1` appends. It used to translate the list as an Int and refute this true claim with a bogus f([]).
        [group: 'P323 list recursion', name: 'appending an element still skips', expect: 'outside fragment',
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result.size() == xs.size() + 1 })
                        static List<Integer> f(List<Integer> xs) { xs + 1 }
                    }''')],

        // ---------- recursion over drop(1) ----------
        // The self-call's formal xs IS the caller's xs: aliasing it to the actual must end with the call.
        [group: 'P323 list recursion', name: 'a recursive length', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result == xs.size() })
                        @Decreases({ xs.size() })
                        static int len(List<Integer> xs) {
                            if (xs.isEmpty()) return 0
                            int r = len(xs.drop(1))
                            return r + 1
                        }
                    }''')],
        [group: 'P323 list recursion', name: 'the caller\'s list is its own after the recursive call', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ result == xs.size() })
                        @Decreases({ xs.size() })
                        static int len(List<Integer> xs) {
                            if (xs.isEmpty()) return 0
                            int r = len(xs.drop(1))
                            return xs.size()
                        }
                    }''')],
        [group: 'P323 list recursion', name: 'recursive pruneWindow with a spread rebuild', ok: true,
         src: tc('''class C {
                        @Requires({ log != null && log.every { int t -> t <= now } })
                        @Ensures({ result.size() <= log.size() })
                        @Ensures({ result.every { int t -> now - w < t && t <= now } })
                        @Decreases({ log.size() })
                        static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
                            if (log.isEmpty()) return []
                            List<Integer> rest = pruneWindow(log.drop(1), now, w)
                            if (log[0] > now - w) return [log[0], *rest]
                            return rest
                        }
                    }''')],
        // The spec says nothing about order, so rebuilding at the back proves too.
        [group: 'P323 list recursion', name: 'recursive pruneWindow appending instead', ok: true,
         src: tc('''class C {
                        @Requires({ log != null && log.every { int t -> t <= now } })
                        @Ensures({ result.size() <= log.size() })
                        @Ensures({ result.every { int t -> now - w < t && t <= now } })
                        @Decreases({ log.size() })
                        static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
                            if (log.isEmpty()) return []
                            List<Integer> rest = pruneWindow(log.drop(1), now, w)
                            if (log[0] > now - w) return rest + [log[0]]
                            return rest
                        }
                    }''')],
        [group: 'P323 list recursion', name: 'recursive pruneWindow keeping a stale entry', expect: 'Cannot prove postcondition of pruneWindow',
         src: tc('''class C {
                        @Requires({ log != null && log.every { int t -> t <= now } })
                        @Ensures({ result.size() <= log.size() })
                        @Ensures({ result.every { int t -> now - w < t && t <= now } })
                        @Decreases({ log.size() })
                        static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
                            if (log.isEmpty()) return []
                            List<Integer> rest = pruneWindow(log.drop(1), now, w)
                            if (log[0] > now - w - 1) return [log[0]] + rest
                            return rest
                        }
                    }''')],
        [group: 'P323 list recursion', name: 'recursive pruneWindow without shrinking', expect: 'Cannot prove recursion measure decreases',
         src: tc('''class C {
                        @Requires({ log != null && log.every { int t -> t <= now } })
                        @Ensures({ result.size() <= log.size() })
                        @Ensures({ result.every { int t -> now - w < t && t <= now } })
                        @Decreases({ log.size() })
                        static List<Integer> pruneWindow(List<Integer> log, int now, int w) {
                            if (log.isEmpty()) return []
                            List<Integer> rest = pruneWindow(log.drop(0), now, w)
                            if (log[0] > now - w) return [log[0]] + rest
                            return rest
                        }
                    }''')],
    ]
}
