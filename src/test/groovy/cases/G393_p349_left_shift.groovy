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
 * 'P349 `<<` writes its receiver' — the commonest reason a frame couldn't be bounded (Phase 348's flag) was `xs << v`:
 * an append on a collection, a shift on an int. "Writes its left operand, unless of immutable type" covers both
 * soundly (the shift writes nothing, so recording it over-approximates), so the write collector now reads `<<` that
 * way while a callee's frame is inferred — a loop's own write set is unchanged. An append also RESIZES, which Phase 229
 * had deliberately ruled out (the registry's mutators preserve size): the collector notes the size-changing writes
 * (`<<`, `add`, `clear`, an unknown method on the receiver — not an element store or an in-place `sort`) and the
 * caller havocs the size oracle of exactly those, with `old.xs.size()` pinned at the call. A registry spec keeps the
 * Phase 229 reading; an array's length never changes.
 */
class G393_p349_left_shift {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 349 `<<` writes its receiver: while a callee frame is inferred, `xs << v` is read as a write to its left operand unless that is of immutable type (a shift on an int writes nothing), so an appending helper has a checked frame instead of a Phase 348 flag. An append resizes: the size-changing writes (`<<`, `add`, `clear`, an unknown method on a collection) are collected beside the frame and the caller havocs the size oracle of exactly those locations, shown `xs.size() (after a call)`; an element store, an in-place sort and a registry spec keep the size (Phase 229), an array length never changes. Fixed (unsound before): a contract-free or declared-frame callee that appended to a List parameter left the caller with its old size.'

    static final List<Map> CASES = [

        // `log << x` used to make the body unbounded (Phase 348 flagged it); it is an append, so it writes `log`.
        [group: 'P349 `<<` writes its receiver', name: 'a list field appended within the frame', ok: true,
         src: tc('''class C {
                        List<Integer> log = []
                        @Modifies({ this.log })
                        void record(int x) { log << x }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: 'a list field appended outside the frame', expect: "Method 'record' writes 'log', which is not in its @Modifies clause []",
         src: tc('''class C {
                        List<Integer> log = []
                        @Modifies({ [] })
                        void record(int x) { log << x }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: 'chained appends', ok: true,
         src: tc('''class C {
                        List<Integer> log = []
                        @Modifies({ this.log })
                        void record(int x) { log << x << x + 1 }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: 'a StringBuilder field appended outside the frame', expect: "Method 'record' writes 'sb', which is not in its @Modifies clause []",
         src: tc('''class C {
                        StringBuilder sb = new StringBuilder()
                        @Modifies({ [] })
                        void record(int x) { sb << x }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: 'an appended Set parameter is a write', expect: "Method 'record' writes 'seen', which is not in its @Modifies clause [count]",
         src: tc('''class C {
                        int count = 0
                        @Requires({ seen != null })
                        @Modifies({ this.count })
                        void record(Set<Integer> seen, int x) { seen << x; count = seen.size() }
                    }''')],
        // On an int `<<` is a shift and writes nothing; the operand's type is immutable, so it isn't recorded.
        [group: 'P349 `<<` writes its receiver', name: 'a shift on an int parameter is not a write', ok: true,
         src: tc('''class C {
                        int count = 0
                        @Modifies({ this.count })
                        void record(int x) { count = x << 1 }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: 'a shift on an int local is not a write', ok: true,
         src: tc('''class C {
                        int count = 0
                        @Modifies({ this.count })
                        void record(int x) { int y = x; count = y << 1 }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: 'a helper appending to a local writes nothing visible', ok: true,
         src: tc('''class C {
                        @Modifies({ [] })
                        static int twice(int x) { List<Integer> l = []; l << x; return x * 2 }
                    }''')],
        // The inferred frame is {xs}: the caller havocs the list and keeps everything else (Phase 347's route). Phase 419 —
        // `xs << v` on a null throws, so the helper needs its list.
        [group: 'P349 `<<` writes its receiver', name: 'a contract-free helper appending to a parameter: the caller frames it', ok: true,
         src: tc('''class C {
                        static int count = 0
                        @Requires({ xs != null })
                        static void push(List<Integer> xs, int v) { xs << v }
                        @Requires({ xs != null && n >= 0 && count == 0 })
                        @Ensures({ count == 0 })
                        static int f(List<Integer> xs, int n) {
                            push(xs, n)
                            return n
                        }
                    }''')],
        // An append resizes: the collector notes the size-changing writes, and the caller havocs the size oracle of
        // exactly those (before this slice the size survived every call — Phase 229's size stability, sound only for the
        // registry's size-preserving mutators).
        [group: 'P349 `<<` writes its receiver', name: '… and the list\'s size is unknown after the call', expect: ["Cannot prove postcondition of f", "xs.size() (after a call) = 1"],
         src: tc('''class C {
                        static void push(List<Integer> xs, int v) { xs << v }
                        @Requires({ xs != null && xs.size() == 0 })
                        @Ensures({ xs.size() == 0 })
                        static int f(List<Integer> xs, int n) {
                            push(xs, n)
                            return n
                        }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: '… and so are its elements', expect: "Cannot prove postcondition of f",
         src: tc('''class C {
                        static void push(List<Integer> xs, int v) { xs << v }
                        @Requires({ xs != null && xs.size() == 1 && xs[0] == 0 })
                        @Ensures({ xs[0] == 0 })
                        static int f(List<Integer> xs, int n) {
                            push(xs, n)
                            return n
                        }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: 'a contract-free `add` resizes too', expect: ["Cannot prove postcondition of f", "xs.size() (after a call) = 1"],
         src: tc('''class C {
                        @Requires({ xs != null })
                        static void push(List<Integer> xs, int v) { xs.add(v) }
                        @Requires({ xs != null && xs.size() == 0 })
                        @Ensures({ xs.size() == 0 })
                        static int f(List<Integer> xs, int n) {
                            push(xs, n)
                            return n
                        }
                    }''')],
        // A declared frame says WHAT is written; whether the body resizes it is still read off the body.
        [group: 'P349 `<<` writes its receiver', name: 'a declared-frame `add` resizes', expect: ["Cannot prove postcondition of f", "xs.size() (after a call) = 0"],
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Modifies({ xs })
                        static void push(List<Integer> xs, int v) { xs.add(v) }
                        @Requires({ xs != null && xs.size() == 1 })
                        @Ensures({ xs.size() == 1 })
                        static int f(List<Integer> xs, int n) {
                            push(xs, n)
                            return n
                        }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: 'a declared-frame element store keeps the size', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Modifies({ xs })
                        static void put0(List<Integer> xs, int v) { xs[0] = v }
                        @Requires({ xs != null && xs.size() == 1 })
                        @Ensures({ xs.size() == 1 })
                        static int f(List<Integer> xs, int n) {
                            put0(xs, n)
                            return n
                        }
                    }''')],
        // A registry spec has no body to read: its mutators are size-preserving by construction, as before.
        [group: 'P349 `<<` writes its receiver', name: 'a registry sort keeps the size (Phase 229)', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() == 2 })
                        @Ensures({ xs.size() == 2 })
                        static int f(List<Integer> xs, int n) {
                            Collections.sort(xs)
                            return n
                        }
                    }''')],
        [group: 'P349 `<<` writes its receiver', name: 'an append in a loop of the helper is a write', expect: "Method 'record' writes 'log', which is not in its @Modifies clause []",
         src: tc('''class C {
                        List<Integer> log = []
                        @Modifies({ [] })
                        void record(int n) { int i = 0; while (i < n) { log << i; i = i + 1 } }
                    }''')],
    ]
}
