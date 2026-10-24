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
 * 'P396 null-safe calls' — a call on a null receiver throws only when the method it reaches does: dispatched dynamically
 * (`@TypeChecked`), Groovy runs it on NullObject, whose GDK `collect`, `findAll`, `grep`, `find`, `every`, `any`,
 * `inject`, `iterator`, `equals`, `toString` and `asBoolean` answer (`[]`, null, true/false, the seed) — so
 * `xs.collect { }` on a nullable list drew an NPE warning for a call that returns `[]`. Measured per receiver kind on
 * Groovy 6: a Map's `findAll` throws a cast exception (its result isn't a map), and statically compiled the GDK method
 * is handed null as `self` and throws, but for `toString`/`asBoolean` and an array's or a String's `collect`.
 */
class G439_p396_null_safe_calls {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 396: a call a null receiver answers rather than throws on (a list's collect/findAll/grep/every/any/find/inject, dispatched dynamically; measured per receiver kind and compile mode) carries no NPE obligation."

    static final String NPE = "Possible NullPointerException"

    static final List<Map> CASES = [

        // Before: `Cannot invoke method collect() on null object … fails on: f(null)`, a call that returns 0.
        [group: "P396 null-safe calls", name: "a null list's collect is [] when dispatched dynamically",
         ok: true,
         src: tc('''class A {
                            static int f(List<Integer> xs) {
                                List r = xs.collect { it }
                                return r.size()
                            }
                        }''')],

        [group: "P396 null-safe calls", name: "… as are its findAll, grep, every and any",
         ok: true,
         src: tc('''class A {
                            static boolean f(List<Integer> xs) {
                                List a = xs.findAll { it > 0 }
                                List b = xs.grep(1)
                                return xs.every { it > 0 } || xs.any { it > 0 } || a.size() + b.size() > 0
                            }
                        }''')],

        [group: "P396 null-safe calls", name: "… its find and inject",
         ok: true,
         src: tc('''class A {
                            static int f(List<Integer> xs) {
                                Integer x = xs.find { it > 0 }
                                return xs.inject(0) { int acc, Integer v -> acc + v }
                            }
                        }''')],

        [group: "P396 null-safe calls", name: "… and an array's collect",
         ok: true,
         src: tc('''class A {
                            static int f(int[] a) {
                                List r = a.collect { it }
                                return r.size()
                            }
                        }''')],

        [group: "P396 null-safe calls", name: "a null list's size still throws",
         expect: [NPE, "fails on: f(null)"],
         src: tc('''class A {
                            static int f(List<Integer> xs) {
                                return xs.size()
                            }
                        }''')],

        [group: "P396 null-safe calls", name: "… and its join",
         expect: [NPE, "fails on: f(null)"],
         src: tc('''class A {
                            static String f(List<Integer> xs) {
                                return xs.join(',')
                            }
                        }''')],

        [group: "P396 null-safe calls", name: "a null map's findAll throws (its result isn't a map)",
         expect: [NPE],
         src: tc('''class A {
                            static int f(Map<String, Integer> m) {
                                Map r = m.findAll { k, v -> v > 0 }
                                return 0
                            }
                        }''')],

        [group: "P396 null-safe calls", name: "a user class's own collect is no exemption",
         expect: [NPE],
         src: tc('''class A {
                            static int f(Box b) {
                                return b.collect { it }
                            }
                        }
                        class Box {
                            int collect(Closure c) { 1 }
                        }''')],

        [group: "P396 null-safe calls", name: "statically compiled, a null list's collect throws",
         expect: [NPE, "fails on: f(null)"],
         src: tc('''class A {
                            @groovy.transform.CompileStatic
                            static int f(List<Integer> xs) {
                                List r = xs.collect { it }
                                return r.size()
                            }
                        }''')],

        [group: "P396 null-safe calls", name: "… but its toString doesn't",
         ok: true,
         src: tc('''class A {
                            @groovy.transform.CompileStatic
                            static String f(List<Integer> xs) {
                                return xs.toString()
                            }
                        }''')],
    ]
}
