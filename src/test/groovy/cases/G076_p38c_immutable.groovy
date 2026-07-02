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

/** 'P38c immutable' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G076_p38c_immutable {

    static final List<Map> CASES = [

        // ---------- Phase 38c: Set.of dedup check + transparent immutable wrappers ----------
        // Set.of with literal duplicates would throw IllegalArgumentException at runtime. We
        // refuse the fold rather than claim a wrong size. The test verifies the SKIP — without
        // a fold, the contract about size on Set.of(1, 1, 1) doesn't translate, so the
        // verifier emits a "postcondition outside fragment" diagnostic. (We could also refute,
        // but a skip is consistent with "honest unsoundness".)
        [group: 'P38c immutable', name: 'Set.of with literal duplicates skips the fold',
         expect: 'outside fragment',
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Set.of(1, 1, 1).size() }
                    }''')],
        // Sanity: Set.of with literal-distinct args still folds the same as before.
        [group: 'P38c immutable', name: 'Set.of with distinct literals still folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Set.of(1, 2, 3).size() }
                    }''')],
        // Collections.unmodifiableList wraps a list-factory transparently; subsequent .size()
        // / .contains() / [i] operations fold as if the wrapper weren't there.
        [group: 'P38c immutable', name: 'Collections.unmodifiableList wraps factory transparently', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Collections.unmodifiableList(List.of(1, 2, 3)).size() }
                    }''')],
        [group: 'P38c immutable', name: 'unmodifiableList(...).contains folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 1 })
                        static int f() {
                            Collections.unmodifiableList(List.of(10, 20, 30)).contains(20) ? 1 : 0
                        }
                    }''')],
        // Groovy's .asImmutable() is the same idea via the GDK.
        [group: 'P38c immutable', name: '.asImmutable() unwraps for .size()', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { [10, 20, 30].asImmutable().size() }
                    }''')],
        // Set.of wrapped by Collections.unmodifiableSet folds the same way.
        [group: 'P38c immutable', name: 'Collections.unmodifiableSet wraps Set.of', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() { Collections.unmodifiableSet(Set.of(1, 2, 3)).size() }
                    }''')],
        // Bracket access through a wrapper: unwrap, then fold the inner factory's i-th element.
        [group: 'P38c immutable', name: 'wrapped factory bracket-index folds', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 20 })
                        static int f() {
                            Collections.unmodifiableList([10, 20, 30])[1]
                        }
                    }''')],
        // Composes with factory-through-assignment (Phase 38b): wrap a local factory.
        [group: 'P38c immutable', name: 'wrap a local factory through assignment', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 3 })
                        static int f() {
                            List<Integer> xs = List.of(1, 2, 3)
                            xs.asImmutable().size()
                        }
                    }''')],
    ]
}
