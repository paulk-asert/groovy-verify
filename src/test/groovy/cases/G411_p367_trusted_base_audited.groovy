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
 * 'P367 the trusted base audited' — the shipped JDK skeletons and the frame inference's method-name tables are
 * trusted, never proved. SpecAuditTest now runs each against the runtime it describes (every skeleton method on
 * edge-heavy inputs its @Requires admits: @ThrowsIf arms in their stated direction, @Ensures on each normal return,
 * the frame against the arguments and receiver; each read name and fresh-result name on sample receivers; each
 * pure static class's statics with mutable arguments). It found three wrong entries, fixed here: the GDK's
 * `map.get(key, default)` writes the map though `get` is a read; `Character.toChars(cp, dst, i)` writes `dst`
 * though Character is a pure static class; and `Collections.frequency(c, o) == c.count(o)` is false when the needle's
 * boxed type differs from the elements' (`equals` against Groovy's `==`) — the skeleton now names exact formals
 * (`Collection<Integer> c, Integer o`), which the registry matches only to actuals of exactly those types.
 */
class G411_p367_trusted_base_audited {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 367 the trusted base audited against the runtime: map.get(key, default) writes its map, Character.toChars writes its array, and Collections.frequency links to count only for exactly matching boxed types — a skeleton formal naming a boxed type or type arguments is matched exactly by the registry.'

    static final List<Map> CASES = [

        // Before: verified — `get` is on the read list, but the GDK's two-argument `map.get(key, default)` puts the default in.
        [group: "P367 the trusted base audited", name: "a helper's map.get(key, default) writes the map",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static int h(Map<Integer, Integer> m) { m.get(5, 0) }
                        @Requires({ m != null && !m.containsKey(5) })
                        @Ensures({ !m.containsKey(5) })
                        static void g(Map<Integer, Integer> m) { h(m) }
                    }''')],

        // Before: verified.
        [group: "P367 the trusted base audited", name: "… and may resize it",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static int h(Map<Integer, Integer> m) { m.get(5, 0) }
                        @Requires({ m != null && m.size() == 0 })
                        @Ensures({ m.size() == 0 })
                        static void g(Map<Integer, Integer> m) { h(m) }
                    }''')],

        [group: "P367 the trusted base audited", name: "… while map.get(key) is still a read", ok: true,
         src: tc('''final class A {
                        @Requires({ m != null })
                        static int h(Map<Integer, Integer> m) { m.get(5) ?: 0 }
                        @Requires({ m != null && m.size() == 0 })
                        @Ensures({ m.size() == 0 })
                        static void g(Map<Integer, Integer> m) { h(m) }
                    }''')],

        // Before: verified — Character is a pure static class, but `toChars(cp, dst, i)` fills `dst`.
        [group: "P367 the trusted base audited", name: "a helper's Character.toChars writes its array",
         expect: "Cannot prove postcondition of g",
         src: tc('''final class A {
                        static void h(char[] b) { Character.toChars(65, b, 0) }
                        @Requires({ a != null && a.length > 0 && a[0] == ('x' as char) })
                        @Ensures({ a[0] == ('x' as char) })
                        static void g(char[] a) { h(a) }
                    }''')],

        // Before: verified — `frequency` counts by `equals`, so frequency([5L], 5) is 0 while [5L].count(5) is 1.
        [group: "P367 the trusted base audited", name: "frequency's link to count needs exactly the needle's type in the list",
         expect: "return expression 'java.util.Collections.frequency(xs, 5)' is outside fragment",
         src: tc('''final class A {
                        @Requires({ xs != null })
                        @Ensures({ result == xs.count(5) })
                        static int g(List<Long> xs) { Collections.frequency(xs, 5) }
                    }''')],

        // Before: verified.
        [group: "P367 the trusted base audited", name: "… either way round",
         expect: "return expression 'java.util.Collections.frequency(xs, o)' is outside fragment",
         src: tc('''final class A {
                        @Requires({ xs != null })
                        @Ensures({ result == xs.count(o) })
                        static int g(List<Integer> xs, long o) { Collections.frequency(xs, o) }
                    }''')],

        [group: "P367 the trusted base audited", name: "… and links when they agree", ok: true,
         src: tc('''final class A {
                        @Requires({ xs != null })
                        @Ensures({ result == xs.count(o) })
                        static int g(List<Long> xs, long o) { Collections.frequency(xs, o) }
                    }''')],
    ]
}
