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

/** 'P17 maps' — 11 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G171_p17_maps {

    static final List<Map> CASES = [

        // ---------- Phase 17: finite maps (value array + key-set) ----------
        // put then read: m.put(k, v) makes m[k] == v (value store, read back via array theory).
        [group: 'P17 maps', name: 'put then get value', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Modifies({ this.m })
                        @Ensures({ m[k] == v })
                        void put(int k, int v) { m.put(k, v) }
                    }''')],
        // The subscript spelling m[k] = v is the same value store.
        [group: 'P17 maps', name: 'subscript store then read', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Ensures({ m[k] == v })
                        void set(int k, int v) { m[k] = v }
                    }''')],
        // put adds the key to the domain — m.containsKey(k) holds afterwards.
        [group: 'P17 maps', name: 'put adds the key', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Modifies({ this.m })
                        @Ensures({ m.containsKey(k) })
                        void put(int k, int v) { m.put(k, v) }
                    }''')],
        // Value frame: a put at key k leaves every other key's value unchanged (array theory, j != k).
        [group: 'P17 maps', name: 'put frames other keys', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Requires({ j != k })
                        @Modifies({ this.m })
                        @Ensures({ m[j] == old.m[j] })
                        void put(int k, int v, int j) { m.put(k, v) }
                    }''')],
        // Key-set cardinality law: putting a NEW key grows the size by one.
        [group: 'P17 maps', name: 'put of new key grows size by one', ok: true,
         src: tc('''class C { Map<Integer,Integer> m
                        @Requires({ !m.containsKey(k) })
                        @Modifies({ this.m })
                        @Ensures({ m.size() == old.m.size() + 1 })
                        void put(int k, int v) { m.put(k, v) }
                    }''')],
        // Soundness: without knowing k is a new key, the +1 cannot be claimed (k may already be present).
        [group: 'P17 maps', name: 'put without fresh key refutes +1', expect: 'Cannot prove postcondition',
         src: tc('''class C { Map<Integer,Integer> m
                        @Modifies({ this.m })
                        @Ensures({ m.size() == old.m.size() + 1 })
                        void put(int k, int v) { m.put(k, v) }
                    }''')],
        // Key membership: `k in m` is m.containsKey(k); assumed entails itself.
        [group: 'P17 maps', name: 'key membership assumed entails', ok: true,
         src: tc('class C { @Requires({ k in m }) @Ensures({ m.containsKey(k) }) static int f(Map<Integer,Integer> m, int k) { 0 } }')],
        // The key-set cardinality law wired into a recursive @Decreases measure — DFS-shaped termination
        // over a map's key domain (each call inserts a fresh key, so `n - m.size()` strictly decreases).
        [group: 'P17 maps', name: 'map-size decreases measure', ok: true,
         src: tc('''class C { Map<Integer,Integer> m; int n
                        @Modifies({ this.m })
                        @Decreases({ n - m.size() })
                        void fill(int k) {
                            if (!m.containsKey(k) && m.size() < n) {
                                m.put(k, k)
                                fill(k + 1)
                            }
                        }
                    }''')],
        // Soundness: drop the fresh-key guard and the size need not grow → measure not decreasing → refuted.
        [group: 'P17 maps', name: 'non-fresh put does not decrease measure', expect: 'recursion measure',
         src: tc('''class C { Map<Integer,Integer> m; int n
                        @Modifies({ this.m })
                        @Decreases({ n - m.size() })
                        void fill(int k) {
                            if (m.size() < n) {
                                m.put(k, k)
                                fill(k + 1)
                            }
                        }
                    }''')],
        // An undeclared map put violates a pure (@Modifies({})) frame.
        [group: 'P17 maps', name: 'undeclared map write refuted', expect: 'not in its @Modifies',
         src: tc('''class C { Map<Integer,Integer> m
                        @Modifies({ [] })
                        void touch(int k, int v) { m.put(k, v) }
                    }''')],
        // A map operation needing an unbounded quantifier (containsValue) is a loud skip, not a pass.
        [group: 'P17 maps', name: 'containsValue outside fragment skipped', expect: 'Skipped verification of postcondition',
         src: tc('class C { @Requires({ m.containsValue(v) }) @Ensures({ m.containsValue(v) }) static int f(Map<Integer,Integer> m, int v) { 0 } }')],
    ]
}
