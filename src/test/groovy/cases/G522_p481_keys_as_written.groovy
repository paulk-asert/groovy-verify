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
 * 'P481 keys as written' — an implicit check's obligation printed its expression with Groovy's {@code .text}, which
 * drops a string's quotes: a map's {@code m.get('x')} read {@code m.get(x) != 0}, a subscript {@code m['x']} read
 * {@code m[x]}, and an index {@code s.indexOf(':')} read {@code s.indexOf(:)}. They now read as written (Phase 428/441's
 * quoting, which assertions and contracts already had).
 */
class G522_p481_keys_as_written {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 481: an implicit check's obligation shows a string as written — `m.get('x') != 0`, not `m.get(x) != 0` (a divisor, an index, a parse argument, an element and a safe call's text)."

    static final List<Map> CASES = [

        // ---------- a map's key ----------
        [group: "P481 keys as written", name: "a map parameter's get", expect: ["obligation: m.get('x') != 0"], refute: 'm.get(x)',
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { 100.intdiv(m.get('x')) }
                    }''')],
        [group: "P481 keys as written", name: "… its subscript", expect: ["obligation: m['x'] != 0"], refute: 'm[x]',
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { 100.intdiv(m['x']) }
                    }''')],
        [group: "P481 keys as written", name: "… a double-quoted key", expect: ['obligation: m.get("x") != 0'], refute: 'm.get(x)',
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { 100.intdiv(m.get("x")) }
                    }''')],
        [group: "P481 keys as written", name: "… a key with a quote in it", expect: ['obligation: m.get("it\'s") != 0'],
         src: tc('''class A {
                        @Requires({ m != null })
                        static int f(Map<String, Integer> m) { 100.intdiv(m.get("it's")) }
                    }''')],
        [group: "P481 keys as written", name: "a local map's", expect: ["obligation: m.get('x') != 0", 'fails on: f(0)'], refute: 'm.get(x)',
         src: tc('''class A {
                        static int f(int n) {
                            Map<String, Integer> m = [x: 1]
                            m.put('x', n)
                            return 100.intdiv(m.get('x'))
                        }
                    }''')],

        // ---------- the other implicit checks ----------
        [group: "P481 keys as written", name: "an array index", expect: ["obligation: 0 <= s.indexOf(':') && s.indexOf(':') < a."], refute: 'indexOf(:)',
         src: tc('''class A {
                        @Requires({ a != null && s != null })
                        static int f(int[] a, String s) { a[s.indexOf(':')] }
                    }''')],
        [group: "P481 keys as written", name: "a charAt index", expect: ["obligation: 0 <= s.indexOf(':') && s.indexOf(':') < s.length()"], refute: 'indexOf(:)',
         src: tc('''class A {
                        @Requires({ s != null })
                        static char f(String s) { s.charAt(s.indexOf(':')) }
                    }''')],
        [group: "P481 keys as written", name: "a substring's begin", expect: ["obligation: 0 <= s.indexOf(':') && s.indexOf(':') < s.length()"], refute: 'indexOf(:)',
         src: tc('''class A {
                        @Requires({ s != null })
                        static String f(String s) { s.substring(s.indexOf(':')) }
                    }''')],
        [group: "P481 keys as written", name: "an element's dereference", expect: ["obligation: xs[s.indexOf(':')] != null"], refute: 'indexOf(:)',
         src: tc('''class A {
                        @Requires({ xs != null && s != null && 0 <= s.indexOf(':') && s.indexOf(':') < xs.size() })
                        static int f(List<String> xs, String s) { xs[s.indexOf(':')].length() }
                    }''')],
        [group: "P481 keys as written", name: "a safe call's value", expect: ["s?.indexOf(':') is null when s is", 'fails on: f(null)'], refute: 'indexOf(:)',
         src: tc('''class A {
                        static int f(String s) { s?.indexOf(':') + 1 }
                    }''')],
        [group: "P481 keys as written", name: "a parse argument", expect: ["obligation: s.replace('_', '') is a valid integer numeral"], refute: 'replace(_, )',
         src: tc('''class A {
                        @Requires({ s != null })
                        static int f(String s) { Integer.parseInt(s.replace('_', '')) }
                    }''')],
    ]
}
