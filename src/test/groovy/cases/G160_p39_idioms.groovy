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

/** 'P39 idioms' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G160_p39_idioms {

    static final List<Map> CASES = [

        // ---------- Phase 39: common non-mutating list/map idioms ----------
        // xs.get(i) is sugar for xs[i] — both lower to (select xs i).
        [group: 'P39 idioms', name: 'xs.get(i) === xs[i]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && 0 <= i && i < xs.size() })
                        @Ensures({ result == xs[i] })
                        static int f(List<Integer> xs, int i) { xs.get(i) }
                    }''')],
        // xs.first() === xs[0]; needs the precondition to discharge the bounds check.
        [group: 'P39 idioms', name: 'xs.first() === xs[0]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs[0] })
                        static int f(List<Integer> xs) { xs.first() }
                    }''')],
        // xs.head() — Groovy idiomatic alias for first().
        [group: 'P39 idioms', name: 'xs.head() === xs[0]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs[0] })
                        static int f(List<Integer> xs) { xs.head() }
                    }''')],
        // xs.last() === xs[size-1].
        [group: 'P39 idioms', name: 'xs.last() === xs[size-1]', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result == xs[xs.size() - 1] })
                        static int f(List<Integer> xs) { xs.last() }
                    }''')],
        // Implicit-bounds refute: xs.first() without a size guard refutes — Phase 39 synthesises an
        // IndexSite(xs, 0) so the bounds check fires the same way it does on xs[0].
        [group: 'P39 idioms', name: 'xs.first() without size guard refutes',
         expect: 'IndexOutOfBoundsException',
         src: tc('''class C {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) { xs.first() }
                    }''')],
        // Map.getOrDefault: ite over containsKey, lowered to value-or-default.
        [group: 'P39 idioms', name: 'm.getOrDefault picks the value when present', ok: true,
         src: tc('''class C {
                        @Requires({ m != null && m.containsKey("k") && m["k"] == 42 })
                        @Ensures({ result == 42 })
                        static int f(Map<String, Integer> m) { m.getOrDefault("k", 0) }
                    }''')],
        // Map.getOrDefault: returns default when key absent.
        [group: 'P39 idioms', name: 'm.getOrDefault picks default when key absent', ok: true,
         src: tc('''class C {
                        @Requires({ m != null && !m.containsKey("k") })
                        @Ensures({ result == 99 })
                        static int f(Map<String, Integer> m) { m.getOrDefault("k", 99) }
                    }''')],
        // xs.set(i, v) statement: mutates same as xs[i] = v. Use List<Integer> since arrays
        // don't have a .set() method on the Groovy/Java type system.
        [group: 'P39 idioms', name: 'xs.set(i, v) statement === xs[i] = v', ok: true,
         src: tc('''class C {
                        List<Integer> a
                        @Requires({ a != null && 0 <= k && k < a.size() })
                        @Modifies({ this.a })
                        @Ensures({ a[k] == v })
                        void put(int k, int v) { a.set(k, v) }
                    }''')],
        // xs.set frame: only the assigned index changes; other indices preserved by @Modifies.
        [group: 'P39 idioms', name: 'xs.set(i, v) preserves other indices', ok: true,
         src: tc('''class C {
                        List<Integer> a
                        @Requires({ a != null && 0 <= k && k < a.size() && j != k && 0 <= j && j < a.size() })
                        @Modifies({ this.a })
                        @Ensures({ a[j] == old.a[j] })
                        void put(int k, int v, int j) { a.set(k, v) }
                    }''')],
        // Factory fold: list literal .first() folds to the first arg.
        [group: 'P39 idioms', name: '[a, b, c].first() folds to literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 10 })
                        static int f() { [10, 20, 30].first() }
                    }''')],
        // Factory fold: list literal .last() folds to the last arg.
        [group: 'P39 idioms', name: '[a, b, c].last() folds to literal', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 30 })
                        static int f() { [10, 20, 30].last() }
                    }''')],
    ]
}
