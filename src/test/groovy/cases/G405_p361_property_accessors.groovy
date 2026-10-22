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
 * 'P361 a property read is its getter' — the verifier modelled `b.n`, for an object parameter `b`, as the field
 * `b$n` (Phase 45). Groovy reads `b.n` through `getN()` for any receiver other than `this` — the class's own getter,
 * or a subclass's — and writes it through `setN`: measured at runtime under @TypeChecked and @CompileStatic, inside
 * the class on a peer, and even for a public field a subclass's getter shadows. So a user getter that writes made
 * `int x = b.n; int y = b.n` differ while the verifier proved `x - y == 0`, and under Phase 360's open world any
 * subclass may add one. A read or helper write is the field now only when the receiver's class is closed (final, an
 * enum, a record, a closed sealed hierarchy) and no class of the hierarchy declares an accessor beyond a generated
 * one or a trivial `return n` / `n = v`; otherwise it is outside the fragment, loudly, with the reason.
 */
class G405_p361_property_accessors {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 361 a property read is its getter: `b.n` on an object parameter is modelled as the field only when b\'s class is closed and declares no getter beyond a generated or trivial one (and a helper\'s `b.n = v` no setter beyond one); otherwise the read is outside the fragment and a helper\'s frame unbounded, loudly, naming the accessor or the open class. Fixed: a user getter that writes, or an open class a subclass may give one, was read as the field, so two reads were proved equal.'

    static final List<Map> CASES = [

        // Before: compiled cleanly — both reads were `b$n`, though each runs getN(), which increments n.
        [group: "P361 a property read is its getter", name: "two reads through a writing getter are not proved equal",
         expect: "Groovy reads 'n' through 'Box.getN(…)', a user getter that isn't the field",
         src: tc('''final class A {
                        @Requires({ b != null })
                        @Ensures({ result == 0 })
                        static int f(Box b) { int x = b.n; int y = b.n; return x - y }
                    }
                    final class Box { int n; int getN() { n = n + 1; return n } }''')],
        // Before: compiled cleanly — the helper's frame was empty, though its read runs a getter that writes.
        [group: "P361 a property read is its getter", name: "a helper reading through a writing getter is unbounded",
         expect: "the read 'b.n': Groovy reads 'n' through 'Box.getN(…)', a user getter that isn't the field",
         src: tc('''final class A {
                        static int peek(Box b) { b == null ? 0 : b.n }
                        @Requires({ b != null && a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(Box b, int[] a) { peek(b) }
                    }
                    final class Box { int n; int getN() { n = n + 1; return n } }''')],
        [group: "P361 a property read is its getter", name: "a trivial user getter is the field", ok: true,
         src: tc('''final class A {
                        @Requires({ b != null && b.n == 3 })
                        @Ensures({ result == 3 })
                        static int f(Box b) { b.n }
                    }
                    final class Box { int n; int getN() { return n } }''')],
        [group: "P361 a property read is its getter", name: "… as is a generated one on a final class", ok: true,
         src: tc('''final class A {
                        @Requires({ b != null && b.n == 3 })
                        @Ensures({ result == 3 })
                        static int f(Box b) { b.n }
                    }
                    final class Box { int n }''')],
        // Before: compiled cleanly — a subclass compiled elsewhere may declare getN().
        [group: "P361 a property read is its getter", name: "an open class's field read is outside the fragment, with the reason",
         expect: "'Box' can be subclassed elsewhere, and Groovy reads 'n' through the getter 'getN', which a subclass may override",
         src: tc('''final class A {
                        @Requires({ b != null && b.n == 3 })
                        @Ensures({ result == 3 })
                        static int f(Box b) { b.n }
                    }
                    class Box { int n }''')],
        // Before: compiled cleanly — Sub's getter runs for a Sub held as a Box.
        [group: "P361 a property read is its getter", name: "a sealed hierarchy whose subclass declares a getter",
         expect: "Groovy reads 'n' through 'Sub.getN(…)', a user getter that isn't the field",
         src: tc('''final class A {
                        @Requires({ b != null && b.n == 3 })
                        @Ensures({ result == 3 })
                        static int f(Box b) { b.n }
                    }
                    sealed class Box { int n }
                    final class Sub extends Box { int getN() { 7 } }''')],
        [group: "P361 a property read is its getter", name: "a helper writing through a user setter is unbounded",
         expect: "the write 'b.n = …': Groovy writes 'n' through 'Box.setN(…)', a user setter that isn't the field",
         src: tc('''final class A {
                        static void put(Box b) { if (b != null) b.n = 5 }
                        @Requires({ b != null && a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(Box b, int[] a) { put(b) }
                    }
                    final class Box { int n; int seen; void setN(int v) { seen = seen + 1; n = v } }''')],
        [group: "P361 a property read is its getter", name: "… and one through a trivial setter is framed by its receiver", ok: true,
         src: tc('''final class A {
                        static void put(Box b) { if (b != null) b.n = 5 }
                        @Requires({ b != null && a != null && a.length > 0 && a[0] == 0 })
                        @Ensures({ a[0] == 0 })
                        static void g(Box b, int[] a) { put(b) }
                    }
                    final class Box { int n; void setN(int v) { n = v } }''')],
    ]
}
