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

/** 'P40 list mutation' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G161_p40_list_mutation {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'xs.add(v): size grows by one and the new last element is v; a wrong delta refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 40: size-changing list mutation ----------
        // Append: xs.add(v) grows size by 1; the new last element is v.
        [group: 'P40 list mutation', name: 'xs.add(v): size grows by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() + 1 })
                        void push(int v) { xs.add(v) }
                    }''')],
        // Append: the appended value lives at the new last index.
        [group: 'P40 list mutation', name: 'xs.add(v): new last element is v', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs[old.xs.size()] == v })
                        void push(int v) { xs.add(v) }
                    }''')],
        // Soundness: claiming size grew by 2 from a single add refutes.
        [group: 'P40 list mutation', name: 'xs.add(v): wrong delta refutes',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() + 2 })
                        void push(int v) { xs.add(v) }
                    }''')],
        // Frame: a non-modified element at index j < oldSize is unchanged.
        [group: 'P40 list mutation', name: 'xs.add(v) preserves earlier elements', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && 0 <= j && j < xs.size() })
                        @Modifies({ this.xs })
                        @Ensures({ xs[j] == old.xs[j] })
                        void push(int v, int j) { xs.add(v) }
                    }''')],
        // Two adds chain: size grows by 2 (the expression composition lets the encoder track
        // sequential mutations without SSA naming).
        [group: 'P40 list mutation', name: 'two adds: size grows by 2', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() + 2 })
                        void pushTwo(int a, int b) { xs.add(a); xs.add(b) }
                    }''')],
        // Clear: size goes to 0.
        [group: 'P40 list mutation', name: 'xs.clear() drops size to 0', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == 0 })
                        void reset() { xs.clear() }
                    }''')],
        // removeLast: with a guard, size shrinks by 1.
        [group: 'P40 list mutation', name: 'xs.removeLast() with guard: size shrinks by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() - 1 })
                        void popOne() { xs.removeLast() }
                    }''')],
        // pop is the Groovy alias for removeLast.
        [group: 'P40 list mutation', name: 'xs.pop() with guard: size shrinks by 1', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() - 1 })
                        void popOne() { xs.pop() }
                    }''')],
        // Soundness: pop without a size guard refutes via the synthesised IndexSite obligation
        // ("0 < xs.size()") — same diagnostic shape as the bracket form would produce. Uses a
        // List parameter (rather than field) because the ObligationCollector's realVar check
        // currently only fires on parameter-resolved VariableExpressions; field-resolved access
        // is a known limit (the body-replay path still threads the mutation, but the implicit
        // bounds check at the call site is parameter-only).
        [group: 'P40 list mutation', name: 'xs.removeLast() without guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        static void popOne(List<Integer> xs) { xs.removeLast() }
                    }''')],
        // Push-then-pop returns to the original size — composes both mutations.
        [group: 'P40 list mutation', name: 'add then removeLast: size restored', ok: true,
         src: tc('''class C {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.size() == old.xs.size() })
                        void roundTrip(int v) { xs.add(v); xs.removeLast() }
                    }''')],
        // README Stack example anchor — push-pop preserves both size and count (the headline
        // Phase 41 win, narrated as a Stack class in the README "Lists — mutation" beat).
        [group: 'P40 list mutation', name: 'README Stack: roundTrip preserves count', ok: true,
         src: tc('''class Stack {
                        List<Integer> xs
                        @Requires({ xs != null })
                        @Modifies({ this.xs })
                        @Ensures({ xs.count(v) == old.xs.count(v) })   // count preserved across a push-pop round-trip
                        void roundTrip(int v) { xs.add(v); xs.removeLast() }
                    }''')],
    ]
}
