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

/** 'P15b ctor-invariant' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G066_p15b_ctor_invariant {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A constructor must establish the class @Invariant (not assume it); a ctor leaving it false refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 15b: class @Invariant on constructors (establishment) ----------
        // Default constructor: int fields default-init to 0, so `count >= 0` holds at exit. The
        // implicit no-arg constructor doesn't appear in declaredConstructors; an explicit empty one
        // does. (A class with no explicit constructor and no body to verify is uninteresting here.)
        [group: 'P15b ctor-invariant', name: 'empty constructor establishes default-Int invariant', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        C() { }
                    }''')],
        // Constructor body assigns an explicit value the invariant requires — verifies.
        [group: 'P15b ctor-invariant', name: 'constructor sets count from non-negative argument', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        @Requires({ initial >= 0 })
                        C(int initial) { count = initial }
                    }''')],
        // Without the @Requires guard, the argument might be negative — the invariant is violated
        // at constructor exit. Refute with the OpenJML-shaped class-invariant message.
        [group: 'P15b ctor-invariant', name: 'constructor with negative initial refuted',
         expect: 'Cannot prove class invariant',
         src: tc('''@groovy.contracts.Invariant({ count >= 0 })
                    class C { int count
                        C(int initial) { count = initial }
                    }''')],
        // Establishment AND maintenance compose: a class with both a constructor and a mutator,
        // both verifying under the same invariant.
        [group: 'P15b ctor-invariant', name: 'constructor + mutator compose', ok: true,
         src: tc('''@groovy.contracts.Invariant({ count >= 0 && count <= max })
                    class C { int count, max
                        @Requires({ m > 0 })
                        C(int m) { max = m }
                        @Requires({ count < max })
                        void inc() { count = count + 1 }
                    }''')],
        // Soundness: a constructor that violates the bound (count = max + 1) is caught.
        [group: 'P15b ctor-invariant', name: 'constructor that overshoots bound refuted',
         expect: 'Cannot prove class invariant',
         src: tc('''@groovy.contracts.Invariant({ count >= 0 && count <= max })
                    class C { int count, max
                        C(int m) { max = m; count = m + 1 }
                    }''')],
    ]
}
