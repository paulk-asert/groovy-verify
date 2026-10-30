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
 * 'P486 a map's value unboxed' — a map's {@code m.get(k)} / {@code m[k]} / {@code m.x} is null for a missing key or a null
 * put (Phase 483), and where a boxed number's value is unboxed a null throws — measured on Groovy 6.0.0, @TypeChecked:
 * an arithmetic operation's left operand or a negation ({@code NullPointerException}, "Cannot execute null+1"), its right
 * operand ({@code GroovyRuntimeException}, "Ambiguous method overloading"; a {@code %}'s is a
 * {@code NullPointerException}), a primitive's value ({@code GroovyCastException}, "Cannot cast 'null' to class 'int'").
 * Those reads had no obligation. A comparison, an Elvis, a String's concatenation and a boxed value take the null.
 */
class G527_p486_map_value_unboxed {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 486: a map's value unboxed where it's used — an arithmetic operand, a negation, a primitive's value — must not be null: `m.get('x') + 1` on a map without `x` (or with a null there) throws, and is checked against the map's keys and null values."

    static final List<Map> CASES = [

        // ---------- arithmetic ----------
        [group: "P486 a map's value unboxed", name: "a left operand", expect: ["Possible NullPointerException: m.get('x') is null for a missing key or a null value, and a null operand throws", "obligation: m.get('x') != null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { m.get('x') + 1 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… a subscript", expect: ["Possible NullPointerException: m['x'] is null", "obligation: m['x'] != null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { m['x'] * 2 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… a property", expect: ["Possible NullPointerException: m.x is null", "obligation: m.x != null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { m.x - 1 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a right operand", expect: ["Possible GroovyRuntimeException: m.get('x') is null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { 1 + m.get('x') }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… a remainder's", expect: ["Possible NullPointerException: m.get('x') is null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != 0 })
                        static int f(Map<String, Integer> m) { 7 % m.get('x') }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a negation", expect: ["Possible NullPointerException: m.get('x') is null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static long f(Map<String, Long> m) { -m.get('x') }
                    }''')],
        [group: "P486 a map's value unboxed", name: "an intdiv's receiver", expect: ["Possible NullPointerException: m.get('x') is null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { m.get('x').intdiv(2) }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… its argument", expect: ["Possible GroovyRuntimeException: m.get('x') is null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != 0 })
                        static int f(Map<String, Integer> m) { 10.intdiv(m.get('x')) }
                    }''')],

        // ---------- a primitive's value ----------
        [group: "P486 a map's value unboxed", name: "a primitive's result", expect: ["Possible GroovyCastException: m.get('x') is null for a missing key or a null value, and a null can't be cast to int", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { m.get('x') }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… returned", expect: ["Possible GroovyCastException: m['x'] is null", "can't be cast to long", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static long f(Map<String, Long> m) { return m['x'] }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… an if's arm", expect: ["Possible GroovyCastException: m.get('y') is null", 'fails on: f([x: 0], false)'],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, Integer> m, boolean b) { if (b) { m.get('x') } else { m.get('y') } }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… a ternary's arm", expect: ["Possible GroovyCastException: m.get('x') is null", 'fails on: f([:], true)'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m, boolean b) { b ? m.get('x') : 0 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a primitive local's value", expect: ["Possible GroovyCastException: m.get('x') is null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { int v = m.get('x'); v }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… assigned", expect: ["Possible GroovyCastException: m.get('x') is null", 'fails on: f([:])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { int v = 0; v = m.get('x'); v }
                    }''')],

        // ---------- a value the method knows ----------
        [group: "P486 a map's value unboxed", name: "a value stated non-null", ok: true,
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, Integer> m) { int v = m['x']; m.x + v * 2 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a put's value", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { m.put('x', 3); m.get('x') + 1 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a null put", expect: ["Possible NullPointerException: m.get('x') is null", "obligation: m.get('x') != null"],
         src: tc('''class A {
                        @Requires({ m != null && m.get('x') != null })
                        static int f(Map<String, Integer> m) { m.put('x', null); m.get('x') + 1 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a literal's key", ok: true,
         src: tc('''class A {
                        static int f() { Map<String, Integer> m = [x: 1]; m.get('x') + 1 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… a key it hasn't", expect: ["Possible NullPointerException: m.get('y') is null", 'fails on: f()'],
         src: tc('''class A {
                        static int f() { Map<String, Integer> m = [x: 1]; m.get('y') + 1 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a key isn't a non-null value", expect: ["Possible NullPointerException: m.get('x') is null", 'fails on: f([x: null])'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { m.containsKey('x') ? m.get('x') + 1 : 0 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a guard", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { m.get('x') != null ? m.get('x') + 1 : 0 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a comparison a null meets", expect: ["Possible NullPointerException: m[k] is null", 'fails on: bump(State.DONE)'],
         src: tc('''@Invariant({ m[State.IDLE] >= 0 && m[State.RUNNING] >= 0 })
                    class Counters {
                        enum State { IDLE, RUNNING, DONE }
                        Map<State,Integer> m
                        @Requires({ m[k] < 1000 })
                        void bump(State k) { m[k] = m[k] + 1 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… one it doesn't", ok: true,
         src: tc('''class A {
                        @Requires({ m != null && m.x >= 5 && 3 == m.y })
                        static int f(Map<String, Integer> m) { m.x + m.y }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a caught exception", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { try { return m.get('x') + 1 } catch (NullPointerException e) { return 0 } }
                    }''')],
        [group: "P486 a map's value unboxed", name: "… a cast's", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { try { return m.get('x') } catch (ClassCastException e) { return 0 } }
                    }''')],

        // ---------- where a null is harmless ----------
        [group: "P486 a map's value unboxed", name: "an Elvis", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { (m.get('x') ?: 0) + 1 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a comparison", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static boolean f(Map<String, Integer> m) { m.get('x') < 3 }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a String's concatenation", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static String f(Map<String, Integer> m) { 'v' + m.get('x') }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a boxed result", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static Integer f(Map<String, Integer> m) { Integer v = m.get('x'); v }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a Boolean value's", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static boolean f(Map<String, Boolean> m) { boolean b = m.get('x'); b }
                    }''')],
        [group: "P486 a map's value unboxed", name: "a String value's", ok: true,
         src: tc('''class A {
                        @Requires({ m != null })
                        static String f(Map<String, String> m) { m.get('x') + 'a' }
                    }''')],
    ]
}
