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

/** 'P225 collections specs' — 8 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G296_p225_collections_specs {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The java.util.Collections skeleton (static factory/query surface) plus Long.parseLong. Collections#binarySearch(List, key) is the List twin of the Arrays true-precondition (result undefined unless sorted) — its discharge needed new machinery: verifyCallSite now ties list/array ELEMENT CONTENTS across the call boundary (size and nullity oracles were tied; the element array was a fresh unconstrained function, so a caller\'s own sortedness could never reach the formal). The list factories (emptyList, singletonList, nCopies — nullity + size ensures; nCopies also a true-iff @ThrowsIf on negative count) needed a second piece: list-returning registry callees in ASSIGN position route through the RENAME instantiation (result renamed to the caller\'s local, the tuple mechanism generalised, with the local\'s fresh list oracles minted first) so reference-oracle facts land where downstream obligations read them — gated on the CALLEE\'s declared return type, since declaration-typed locals are invisible to the scalar-type map, and accepting the skeleton\'s unresolved simple-name List. Typed lookup gained the Object-formal wildcard (primitives box on the way in; the uniqueness rule still declines ambiguous sets). Deliberately absent, recorded: the mutators (sort/reverse — @Modifies-shaped consumption), max/min/frequency (Collection-typed formal matching), the instance List/Map interfaces (receiver-oracle wiring). Long.parseLong mirrors Integer.parseInt: a one-directional arm whose survival contrapositive proves s != null. Phase 226 adds Collection-typed formal matching: SpecRegistry.formalAccepts (one acceptance rule shared by the typed lookup and the assumption guard — Object wildcard, Collection/List kinds, width-classed equality) plus assumption-side ORACLE ALIASING (a Collection formal bound to a named list actual gets the actual\'s force-minted size/array/nullity oracles, since a scalar handle cannot carry element facts) — so Collections.max/min ship with empty-collection @ThrowsIf iffs and element-dominance ensures (max\'s fact reaches a named element; min\'s over-claim refutes), and frequency ships range facts (its exact result == c.count(o) is STATED but not yet linkable to the caller\'s spelling — the count machinery is name-keyed; recorded).'

    static final List<Map> CASES = [

        // ---------- Phase 225: Collections + parseLong ----------
        [group: 'P225 collections specs', name: 'Collections.binarySearch requires sorted: unsorted call refutes', expect: 'Cannot prove precondition of binarySearch',
         src: tc('''class C {
                        static int find(List<Integer> xs, int key) {
                            return java.util.Collections.binarySearch(xs, key)
                        }
                    }''')],
        [group: 'P225 collections specs', name: 'binarySearch obligation discharged (element contents tied across the boundary)', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.indices.every { it == 0 || xs[it - 1] <= xs[it] } })
                        static int find(List<Integer> xs, int key) {
                            return java.util.Collections.binarySearch(xs, key)
                        }
                    }''')],
        [group: 'P225 collections specs', name: 'emptyList: nullity + size facts land on the local (rename route)', ok: true,
         src: tc('''class C {
                        @Ensures({ result == 0 })
                        static int f() {
                            List l = java.util.Collections.emptyList()
                            return l.size()
                        }
                    }''')],
        [group: 'P225 collections specs', name: 'nCopies: guarded size fact (Object-wildcard typed lookup)', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result == n })
                        static int f(int n) {
                            List l = java.util.Collections.nCopies(n, 'x')
                            return l.size()
                        }
                    }''')],
        [group: 'P225 collections specs', name: 'Long.parseLong survival proves s non-null (signals arm)', ok: true,
         src: tc('''class C {
                        static int f(String s) {
                            long v = Long.parseLong(s)
                            return s.length()
                        }
                    }''')],
        // ---------- Phase 226: Collection-typed formals (max/min/frequency) ----------
        [group: 'P225 collections specs', name: 'Collections.max: the dominance fact reaches a named element', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result >= xs[0] })
                        static int biggest(List<Integer> xs) {
                            return Collections.max(xs)
                        }
                    }''')],
        [group: 'P225 collections specs', name: 'Collections.min over-claim refutes (result < xs[0] fails when xs[0] is the min)', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ xs != null && xs.size() > 0 })
                        @Ensures({ result < xs[0] })
                        static int smallest(List<Integer> xs) {
                            return Collections.min(xs)
                        }
                    }''')],
        [group: 'P225 collections specs', name: 'frequency: range facts consumed (exact-count linkage recorded)', ok: true,
         src: tc('''class C {
                        @Requires({ xs != null })
                        @Ensures({ 0 <= result && result <= xs.size() })
                        static int fives(List<Integer> xs) {
                            return Collections.frequency(xs, 5)
                        }
                    }''')],
    ]
}
