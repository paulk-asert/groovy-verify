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

/** 'P16 sets' — 14 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G155_p16_sets {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Finite Set membership: x in s / !in, and an assumed membership entails membership.'

    static final List<Map> CASES = [

        // ---------- `!in` operator (negated membership; `x !in s` ≡ `!(x in s)`) ----------
        // It lowers to the identical `not(member)` term as `!(x in s)` — recognised in contracts.
        [group: 'P16 sets', name: '!in is negated membership', ok: true,
         src: tc('''class C {
                        @Requires({ x !in s })
                        @Ensures({ !(x in s) })
                        static int f(Set<Integer> s, int x) { 0 }
                    }''')],
        [group: 'P16 sets', name: '!in does not imply membership (refutes)',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ x !in s })
                        @Ensures({ x in s })
                        static int f(Set<Integer> s, int x) { 0 }
                    }''')],

        // ---------- Phase 16: finite sets (characteristic array + cardinality law) ----------
        // Membership assumed entails membership — `x in s` over a Set parameter (the read side).
        [group: 'P16 sets', name: 'membership assumed entails membership', ok: true,
         src: tc('class C { @Requires({ x in s }) @Ensures({ x in s }) static int f(Set<Integer> s, int x) { 0 } }')],
        // Not vacuous: with nothing assumed, membership cannot be proved.
        [group: 'P16 sets', name: 'unproven membership refuted', expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ x in s }) static int f(Set<Integer> s, int x) { 0 } }')],
        // `s.contains(x)` is the method spelling of the same membership.
        [group: 'P16 sets', name: 'contains is membership', ok: true,
         src: tc('class C { @Requires({ s.contains(x) }) @Ensures({ x in s }) static int f(Set<Integer> s, int x) { 0 } }')],
        // add makes the element a member — the post-state read rides Z3 array theory (store then select).
        [group: 'P16 sets', name: 'add makes element a member', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Modifies({ this.s })
                        @Ensures({ x in s })
                        void put(int x) { s.add(x) }
                    }''')],
        // Cardinality law (headline): adding an element NOT already present grows the size by one.
        [group: 'P16 sets', name: 'add of new element grows size by one', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ x !in s })
                        @Modifies({ this.s })
                        @Ensures({ s.size() == old.s.size() + 1 })
                        void put(int x) { s.add(x) }
                    }''')],
        // Soundness: without knowing x is new, the +1 cannot be claimed (x may already be present).
        [group: 'P16 sets', name: 'add without freshness refutes +1', expect: 'Cannot prove postcondition',
         src: tc('''class C { Set<Integer> s
                        @Modifies({ this.s })
                        @Ensures({ s.size() == old.s.size() + 1 })
                        void put(int x) { s.add(x) }
                    }''')],
        // Adding an element already present leaves the size unchanged.
        [group: 'P16 sets', name: 'add of present element keeps size', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ x in s })
                        @Modifies({ this.s })
                        @Ensures({ s.size() == old.s.size() })
                        void put(int x) { s.add(x) }
                    }''')],
        // remove of a present element shrinks the size by one.
        [group: 'P16 sets', name: 'remove of present element shrinks size', ok: true,
         src: tc('''class C { Set<Integer> s
                        @Requires({ x in s })
                        @Modifies({ this.s })
                        @Ensures({ s.size() == old.s.size() - 1 })
                        void drop(int x) { s.remove(x) }
                    }''')],
        // An undeclared set mutation violates a pure (@Modifies({})) frame — caught like an array store.
        [group: 'P16 sets', name: 'undeclared set write refuted', expect: 'not in its @Modifies',
         src: tc('''class C { Set<Integer> s
                        @Modifies({ [] })
                        void touch(int x) { s.add(x) }
                    }''')],
        // A set operation needing an unbounded quantifier (containsAll/subset) is a loud skip, not a pass.
        [group: 'P16 sets', name: 'subset op outside fragment skipped', expect: 'Skipped verification of postcondition',
         src: tc('class C { @Requires({ s.containsAll(t) }) @Ensures({ s.containsAll(t) }) static int f(Set<Integer> s, Set<Integer> t) { 0 } }')],
        // The cardinality law wired into a recursive @Decreases measure: each call adds a *fresh* element
        // to `s` (the guard `x !in s` makes it fresh), so the measure `n - s.size()` strictly decreases —
        // a finite recursion over a bounded domain (the DFS-shaped termination argument), proved with no
        // quantifier. Termination + the recursion's own well-foundedness, end to end.
        [group: 'P16 sets', name: 'set-cardinality decreases measure', ok: true,
         src: tc('''class C { Set<Integer> s; int n
                        @Modifies({ this.s })
                        @Decreases({ n - s.size() })
                        void fill(int x) {
                            if (x !in s && s.size() < n) {
                                s.add(x)
                                fill(x + 1)
                            }
                        }
                    }''')],
        // Soundness: drop the freshness guard `x !in s` and the added element may already be present,
        // so `s.size()` need not grow — the measure does not provably decrease → termination refuted.
        [group: 'P16 sets', name: 'non-fresh add does not decrease measure', expect: 'recursion measure',
         src: tc('''class C { Set<Integer> s; int n
                        @Modifies({ this.s })
                        @Decreases({ n - s.size() })
                        void fill(int x) {
                            if (s.size() < n) {
                                s.add(x)
                                fill(x + 1)
                            }
                        }
                    }''')],
    ]
}
