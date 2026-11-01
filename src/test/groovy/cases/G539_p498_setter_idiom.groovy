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
 * 'P498 setter idiom' — a setter, {@code void set(int count) { this.count = count }}, under a class invariant: Phase 497
 * refused it, as the field and its parameter were one name. The class invariant assumed at entry is the one read of
 * the field before the copy, and it now reads the field's entry value as {@code this$count}; from the copy on, field
 * and parameter are one value. So the setter is held to the invariant, under its own {@code @Requires}. A
 * {@code @Requires} that reads {@code this.count}, or an {@code @Ensures} that reads {@code old.count}, is the entry
 * value too, and still refused.
 */
class G539_p498_setter_idiom {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 498: a setter `this.count = count` under a class invariant verifies — the invariant assumed at entry speaks of the field, not the parameter."

    static final List<Map> CASES = [

        // ---------- the setter, held to the invariant ----------
        [group: "P498 setter idiom", name: "a setter under its precondition", ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Requires({ count >= 0 })
                        void set(int count) { this.count = count }
                    }''')],
        [group: "P498 setter idiom", name: "… without it", expect: ['Cannot prove class invariant of set', 'this.count = ', 'fails on: set('],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        void set(int count) { this.count = count }
                    }''')],
        [group: "P498 setter idiom", name: "the entry invariant isn't the parameter's", expect: ['Cannot prove postcondition'],
         src: tc('''@Invariant({ count != 5 })
                    class A {
                        int count
                        @Requires({ count != 7 })
                        @Ensures({ result })
                        boolean set(int count) { this.count = count; count != 5 }
                    }''')],
        [group: "P498 setter idiom", name: "the field is the parameter after", ok: true,
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Requires({ count >= 0 })
                        @Ensures({ this.count == count })
                        void set(int count) { this.count = count }
                    }''')],
        [group: "P498 setter idiom", name: "one field of two", ok: true,
         src: tc('''@Invariant({ lo <= hi })
                    class A {
                        int lo
                        int hi
                        @Requires({ lo <= hi })
                        void setLo(int lo) { this.lo = lo }
                    }''')],
        [group: "P498 setter idiom", name: "… the other's entry value still held", expect: ['Cannot prove class invariant of setLo'],
         src: tc('''@Invariant({ lo <= hi })
                    class A {
                        int lo
                        int hi
                        @Requires({ lo <= 10 })
                        void setLo(int lo) { this.lo = lo }
                    }''')],
        [group: "P498 setter idiom", name: "a boolean field's", ok: true,
         src: tc('''@Invariant({ !locked || n > 0 })
                    class A {
                        boolean locked
                        int n
                        @Requires({ !locked || n > 0 })
                        void setLocked(boolean locked) { this.locked = locked }
                    }''')],
        [group: "P498 setter idiom", name: "… whose entry value the invariant reads as a boolean", ok: true,
         src: tc('''@Invariant({ locked && n > 0 })
                    class A {
                        boolean locked
                        int n
                        @Requires({ locked })
                        void setLocked(boolean locked) { this.locked = locked }
                    }''')],
        [group: "P498 setter idiom", name: "… shown as one", expect: ['Cannot prove class invariant of setLocked', 'this.locked = true'],
         src: tc('''@Invariant({ locked && n > 0 })
                    class A {
                        boolean locked
                        int n
                        void setLocked(boolean locked) { this.locked = locked }
                    }''')],
        [group: "P498 setter idiom", name: "a String field's", ok: true,
         src: tc('''@Invariant({ name != null })
                    class A {
                        String name
                        @Requires({ name != null })
                        void setName(String name) { this.name = name }
                    }''')],
        [group: "P498 setter idiom", name: "… without its precondition", expect: ['Cannot prove class invariant of setName'],
         src: tc('''@Invariant({ name != null })
                    class A {
                        String name
                        void setName(String name) { this.name = name }
                    }''')],

        // ---------- still refused ----------
        [group: "P498 setter idiom", name: "a precondition on the field's entry value", expect: ["field 'count' is shadowed by a parameter of set, and this.count uses the field"],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Requires({ this.count < count })
                        void set(int count) { this.count = count }
                    }''')],
        [group: "P498 setter idiom", name: "… or a postcondition's old value", expect: ["field 'count' is shadowed by a parameter of set, and this.count uses the field"],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        int count
                        @Requires({ count >= 0 })
                        @Ensures({ old.count <= count })
                        void set(int count) { this.count = count }
                    }''')],
        [group: "P498 setter idiom", name: "a parameter of another type", expect: ["field 'count' is shadowed by a parameter of set, and this.count uses the field"],
         src: tc('''@Invariant({ count >= 0 })
                    class A {
                        long count
                        @Requires({ count >= 0 })
                        void set(int count) { this.count = count }
                    }''')],
    ]
}
