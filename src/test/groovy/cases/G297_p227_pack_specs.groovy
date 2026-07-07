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

/** 'P227 pack specs' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G297_p227_pack_specs {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Pack-declared external specs (Phase 227): EncodingPack.specFqns() lets a pack DECLARE the spec skeletons its jar ships, buying lifecycle coherence (an FQN declared by a discovered-but-disabled pack is never consumed — deselecting a pack via VERIFY_PACKS also deselects its specs), the trusted-inventory lint (each declared skeleton must parse and carry contracts, and no spec resource may be shadowed by a classpath duplicate — first-wins is the rule, a silent second copy is drift), and catalog attribution (packSpecs provenance beside the corpusGroups key). The demonstrator is the jsr385-units pack\'s deliberately THIN contract rim — Quantity.getValue/getUnit and Quantities.getQuantity nullity facts — with the division of labour stated: packs model what contracts CANNOT say (dimension algebra, SI magnitudes, scale — theory), spec skeletons say what they can (nullity, ranges, arms); the incommensurable-to() exception is deliberately unspecced (its condition is a dimension predicate, not a parameter closure — no false iffs). The soundness obligation extends: a pack may only spec what is provably true of the library, rung-monitored like every registry fact.'

    static final List<Map> CASES = [

        // ---------- Phase 227: pack-declared specs (the jsr385-units thin rim) ----------
        [group: 'P227 pack specs', name: 'Quantity.getValue non-null: a pack-declared instance spec consumed', ok: true,
         src: tc('''class C {
                        @Requires({ q != null })
                        @Ensures({ result != null })
                        static Object v(javax.measure.Quantity q) {
                            return q.getValue()
                        }
                    }''')],
        [group: 'P227 pack specs', name: 'Quantities.getQuantity non-null: a pack-declared factory spec consumed', ok: true,
         src: tc('''class C {
                        @Requires({ v != null && u != null })
                        @Ensures({ result != null })
                        static Object make(Number v, javax.measure.Unit u) {
                            return tech.units.indriya.quantity.Quantities.getQuantity(v, u)
                        }
                    }''')],
    ]
}
