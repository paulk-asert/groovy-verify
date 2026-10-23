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
 * 'P386 fresh collection' — a local bound to a GDK collection-producing call (`toList()`, `collect`, `findAll`,
 * `groupBy`, …) is never null: the call returns a collection or throws (checked on the runtime for a null and an
 * empty receiver). Only a decimal or char range's `toList()` and the like reached the deref check — an int range is
 * modelled — and each drew a spurious possible-NPE. STC's resolved target decides, so a user's own `toList()` that
 * returns null still refutes. Two neighbours: a failure resting on a value the obligation replay couldn't model
 * shows no call (it read `fails on: f()`), and an if's branches now merge nullity (`List r = [1, 2]; if (c) r = xs`
 * kept the literal's non-null — unsound).
 */
class G429_p386_fresh_collection {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 386: a local bound to a GDK fresh-collection call (toList, collect, findAll, groupBy, …) is never null; a failure resting on an unmodelled local shows no call; an if's branches merge nullity."

    static final String NPE = "Cannot invoke method size() on null object"
    static final String UNMODELLED = "no failing call: the failure rests on r, a value the verifier doesn't model"

    static final List<Map> CASES = [

        // Before: `Possible NullPointerException … obligation: r != null, fails on: f()`.
        [group: "P386 fresh collection", name: "a decimal range's toList() is never null",
         ok: true,
         src: tc('''class A {
                        static int f() {
                            List r = (4.5..6.5).toList()
                            return r.size()
                        }
                    }''')],

        [group: "P386 fresh collection", name: "… nor a char range's",
         ok: true,
         src: tc('''class A {
                        static int f() {
                            List r = ('a'..'d').toList()
                            return r.size()
                        }
                    }''')],

        [group: "P386 fresh collection", name: "… nor a collect over one",
         ok: true,
         src: tc('''class A {
                        static int f() {
                            List r = (4.5..6.5).collect { it }
                            return r.size()
                        }
                    }''')],

        [group: "P386 fresh collection", name: "a findAll over a non-null parameter is never null",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) {
                            List r = xs.findAll { it > 0 }
                            return r.size()
                        }
                    }''')],

        [group: "P386 fresh collection", name: "… nor a groupBy's map",
         ok: true,
         src: tc('''class A {
                        @Requires({ xs != null })
                        static int f(List<Integer> xs) {
                            Map m = xs.groupBy { it % 2 }
                            return m.size()
                        }
                    }''')],

        // The receiver's own obligation stays: `null.toList()` throws.
        [group: "P386 fresh collection", name: "a nullable receiver keeps its own obligation, the result none",
         expect: ["Cannot invoke method toList() on null object", "fails on: f(null)"], refute: "obligation: r != null",
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            List r = xs.toList()
                            return r.size()
                        }
                    }''')],

        // Teeth: STC's target, not the name — a user's toList() may return null, and does.
        [group: "P386 fresh collection", name: "a user's own toList() can still return null",
         expect: [NPE, "fails on: f(new Box())"],
         src: tc('''class A {
                        @Requires({ b != null })
                        static int f(Box b) {
                            List r = b.toList()
                            return r.size()
                        }
                    }
                    class Box {
                        List toList() { null }
                    }''')],

        // Teeth: `xs?.toList()` is null when xs is.
        [group: "P386 fresh collection", name: "a safe-navigation call can be null",
         expect: [NPE, "obligation: r != null"],
         src: tc('''class A {
                        static int f(List<Integer> xs) {
                            List r = xs?.toList()
                            return r.size()
                        }
                    }''')],

        // Before: `fails on: f()`, a call that passes — the replay left r free, and the model's size is no run's.
        [group: "P386 fresh collection", name: "a failure resting on an unmodelled local shows no call",
         expect: ["Assertion may not hold: (r.size() == 3)", UNMODELLED], refute: "fails on",
         src: tc('''class A {
                        static void f() {
                            List r = (4.5..6.5).toList()
                            assert r.size() == 3
                        }
                    }''')],

        // Before: compiled cleanly (unsound) — the if-merge kept the else branch's nullity, the literal's non-null.
        [group: "P386 fresh collection", name: "a branch's re-assignment merges its nullity",
         expect: [NPE, "fails on: f(null, true)"],
         src: tc('''class A {
                        static int f(List<Integer> xs, boolean c) {
                            List r = [1, 2]
                            if (c) r = xs
                            return r.size()
                        }
                    }''')],

        [group: "P386 fresh collection", name: "… in the else branch too",
         expect: [NPE, "fails on: f(null, false)"],
         src: tc('''class A {
                        static int f(List<Integer> xs, boolean c) {
                            List r = [1, 2]
                            if (c) r = [3] else r = xs
                            return r.size()
                        }
                    }''')],

        [group: "P386 fresh collection", name: "… and two non-null branches stay non-null",
         ok: true,
         src: tc('''class A {
                        static int f(boolean c) {
                            List r = [1, 2]
                            if (c) r = [3] else r = [4, 5, 6]
                            return r.size()
                        }
                    }''')],
    ]
}
