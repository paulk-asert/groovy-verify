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
 * 'P352 an old scalar field has no size' — the Phase 40 entry snapshot pinned `old.f.size()` for every field `old.f`
 * names, scalars included. The pin was harmless to proofs but minted an `f.size` variable, which counterexamples
 * showed as a stray `count.size() = 0` beside an int `count`. The size is now pinned only for a field that can have
 * one (anything but a primitive, a boxed number, a Boolean or a Character).
 */
class G396_p352_old_scalar_size {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 352 an old scalar field has no size: the entry snapshot pins `old.f.size()` only for a field that can have a size, so a counterexample over an int field read as `old.count` no longer shows a stray `count.size() = 0`; a List field keeps its entry size for `old.xs.size()`.'

    static final List<Map> CASES = [

        // Before: the entry snapshot pinned `old.count.size()` for every field `old` names, minting a `count.size` variable
        // that the counterexample showed as `count.size() = 0`.
        [group: 'P352 an old scalar field has no size', name: 'an int field read as old.count shows no count.size()', expect: ["Cannot prove postcondition of f", "counterexample: count = "], refute: 'count.size()',
         src: tc('''class A {
                        int count = 0
                        @Ensures({ count == old.count + 2 })
                        void f() { count = count + 1 }
                    }''')],
        [group: 'P352 an old scalar field has no size', name: 'a boxed Integer field likewise', expect: "Cannot prove postcondition of f", refute: 'hits.size()',
         src: tc('''class A {
                        Integer hits = 0
                        @Ensures({ hits == old.hits + 2 })
                        void f() { hits = hits + 1 }
                    }''')],
        [group: 'P352 an old scalar field has no size', name: 'a field named size likewise', expect: "Cannot prove postcondition of f", refute: 'size.size()',
         src: tc('''class A {
                        int size = 0
                        @Ensures({ size == old.size + 2 })
                        void f() { size = size + 1 }
                    }''')],
        // The Phase 40 snapshot is what makes `old.xs.size()` survive the add: kept for any field that can have a size.
        [group: 'P352 an old scalar field has no size', name: 'a List field keeps its entry size', ok: true,
         src: tc('''class A {
                        List<Integer> xs = []
                        @Requires({ xs != null })
                        @Ensures({ xs.size() == old.xs.size() + 1 })
                        void f() { xs.add(1) }
                    }''')],
        [group: 'P352 an old scalar field has no size', name: '… and a wrong claim about it still refutes', expect: "Cannot prove postcondition of f",
         src: tc('''class A {
                        List<Integer> xs = []
                        @Requires({ xs != null })
                        @Ensures({ xs.size() == old.xs.size() + 2 })
                        void f() { xs.add(1) }
                    }''')],
    ]
}
