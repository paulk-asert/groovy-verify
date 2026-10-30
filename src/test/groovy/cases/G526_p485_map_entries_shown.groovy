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
 * 'P485 a map's entries shown' — a failing call rendered every map {@code [:]}, whatever the model held, so a precondition
 * over a map's entries ({@code @Requires({ m.get('x') != null })}) withheld the call (Phase 483), and one the failure
 * needed an entry for showed a call that doesn't fail that way ({@code m['x'][0]} as {@code f([:])}). The model's
 * entry-state key-set, values and value-null flags are now read as the literal that builds the map; its size is made
 * the keys' count, and a key-set with every key but a few is cut to the keys the query reads or writes.
 */
class G526_p485_map_entries_shown {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 485: a failing call shows a map argument's entries from the model — `f([x: \"\"], 0)`, `f([x: null])`, `f([3: 6], 0)` — instead of `[:]`, which broke a precondition over them (the call was withheld) or didn't fail the way reported."

    static final List<Map> CASES = [

        // ---------- the entries a precondition states ----------
        [group: "P485 a map's entries shown", name: "a stated key", expect: ['Division by zero', 'fails on: f([x: ""], 0)'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, String> m, int n) { 100.intdiv(n) }
                    }''')],
        [group: "P485 a map's entries shown", name: "… a stated null value", expect: ['Cannot invoke method length() on null object', 'fails on: f([x: null])'],
         src: tc('''class A {
                        @Requires({ m != null && m.containsKey('x') })
                        static int f(Map<String, String> m) { m.get('x').length() }
                    }''')],
        [group: "P485 a map's entries shown", name: "… an Integer key and value", expect: ['Division by zero', 'fails on: f([3: 6], 0)'],
         src: tc('''class A {
                        @Requires({ m != null && m.get(3) != null && m.get(3) == 6 })
                        static int f(Map<Integer, Integer> m, int n) { 100.intdiv(n) }
                    }''')],
        [group: "P485 a map's entries shown", name: "… a negative key", expect: ['Division by zero', 'fails on: f([(-1): 2], 0)'],
         src: tc('''class A {
                        @Requires({ m != null && m.get(-1) == 2 })
                        static int f(Map<Integer, Integer> m, int n) { 100.intdiv(n) }
                    }''')],
        [group: "P485 a map's entries shown", name: "… a key that isn't a name", expect: ['Division by zero', 'fails on: f(["a b": "c"], 0)'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('a b') == 'c' })
                        static int f(Map<String, String> m, int n) { 100.intdiv(n) }
                    }''')],
        [group: "P485 a map's entries shown", name: "… two keys", expect: ['Division by zero', 'fails on: f([', 'x: "a"', 'y: "b"'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') == 'a' && m.get('y') == 'b' })
                        static int f(Map<String, String> m, int n) { 100.intdiv(n) }
                    }''')],
        [group: "P485 a map's entries shown", name: "… and its size", expect: ['Division by zero', 'fails on: f([x: ""], 0)'],
         src: tc('''class A {
                        @Requires({ m != null && m.size() == 1 && m.get('x') != null })
                        static int f(Map<String, String> m, int n) { 100.intdiv(n) }
                    }''')],
        [group: "P485 a map's entries shown", name: "… a key read only as a value", expect: ['Division by zero', 'fails on: f([', 'x: ', 'y: 2'],
         src: tc('''class A {
                        @Requires({ m != null && m.containsKey('x') && m.get('y') == 2 })
                        static int f(Map<String, Integer> m, int n) { 100.intdiv(n) }
                    }''')],
        [group: "P485 a map's entries shown", name: "… a put's size law on it", expect: ['Division by zero', 'fails on: f([', 'x: ""'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, String> m, int n) { m.put('y', 'b'); 100.intdiv(n) }
                    }''')],
        [group: "P485 a map's entries shown", name: "… a size its keys don't make: no call", expect: ['Division by zero', 'a map argument is shown as [:]'], refute: 'fails on:',
         src: tc('''class A {
                        @Requires({ m != null && m.size() == 2 && m.containsKey('x') })
                        static int f(Map<String, String> m, int n) { 100.intdiv(n) }
                    }''')],

        // ---------- the entries a failure needs ----------
        [group: "P485 a map's entries shown", name: "a value the failure reads", expect: ['Cannot invoke method length() on null object', 'fails on: f([x: null])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { m.containsKey('x') ? m.get('x').length() : 0 }
                    }''')],
        [group: "P485 a map's entries shown", name: "… its string's character", expect: ['index may be out of bounds', 'fails on: f([x: ""])'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static String f(Map<String, String> m) { m['x'][0] }
                    }''')],
        [group: "P485 a map's entries shown", name: "a map the failure doesn't read stays empty", expect: ['Division by zero', 'fails on: f([:], 0)'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m, int n) { 100.intdiv(n) }
                    }''')],

        // ---------- a call-site precondition: no placeholder ----------
        [group: "P485 a map's entries shown", name: "no `m = 0` placeholder", expect: ['Cannot prove precondition of g', 'fails on: f([:])'], refute: 'm = 0',
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, String> m) { g(m) }
                        @Requires({ m != null && m.size() > 0 })
                        static int g(Map<String, String> m) { 1 }
                    }''')],
    ]
}
