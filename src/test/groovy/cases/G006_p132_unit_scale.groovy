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

/** 'P132 unit scale' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G006_p132_unit_scale {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'JSR 385 value/scale: a Quantity built from known units (getQuantity/prefixes/add/to) has its SI magnitude recovered, so getValue() in a named unit verifies exactly and a wrong-unit extraction refutes (the Mars scale bug).'

    static final List<Map> CASES = [

        // ---------- Phase 132: JSR 385 value/scale (C₁ — SI-normalized magnitudes) ----------
        // Mars-in-miniature: 1 km + 50000 cm, read back in metres, is exactly 1500 m (mixed scales, normalized).
        [group: 'P132 unit scale', name: 'mixed-prefix length sum in metres is exact', ok: true,
         src: HDR + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 1500.0 })\n' +
              '          static BigDecimal total() { Quantities.getQuantity(1, KILO(METRE)).add(Quantities.getQuantity(50000, CENTI(METRE))).to(METRE).getValue() as BigDecimal } }'],
        // The actual Mars mix: metric + US-customary. 1 km + 1 mile, normalized to metres, is exactly 2609.344.
        // (USCustomary.MILE's scale is read from the engine's curated table, pinned to the RI by UnitScaleTest.)
        [group: 'P132 unit scale', name: 'kilometre plus mile in metres is exact', ok: true,
         src: HDR + UOM2 + 'import systems.uom.common.USCustomary\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 2609.344 })\n' +
              '          static BigDecimal total() { Quantities.getQuantity(1, KILO(METRE)).add(Quantities.getQuantity(1, USCustomary.MILE)).to(METRE).getValue() as BigDecimal } }'],
        // The SAME sum read back in KILOMETRES is 1.5 — extracting in the right unit verifies.
        [group: 'P132 unit scale', name: 'same sum read in kilometres is 1.5', ok: true,
         src: HDR + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 1.5 })\n' +
              '          static BigDecimal inKm() { Quantities.getQuantity(1, KILO(METRE)).add(Quantities.getQuantity(50000, CENTI(METRE))).to(KILO(METRE)).getValue() as BigDecimal } }'],
        // The Mars bug: reading the metre-magnitude but claiming the kilometre number — 1500 ≠ 1.5 → refutes.
        [group: 'P132 unit scale', name: 'wrong-unit extraction refutes (the scale bug)', expect: 'Cannot prove postcondition',
         src: HDR + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 1500.0 })\n' +
              '          static BigDecimal buggy() { Quantities.getQuantity(1, KILO(METRE)).add(Quantities.getQuantity(50000, CENTI(METRE))).to(KILO(METRE)).getValue() as BigDecimal } }'],
        // Scalar divide on a magnitude: 10 km / 2 = 5000 m.
        [group: 'P132 unit scale', name: 'scalar divide of a length in metres', ok: true,
         src: HDR + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 5000.0 })\n' +
              '          static BigDecimal half() { Quantities.getQuantity(10, KILO(METRE)).divide(2).to(METRE).getValue() as BigDecimal } }'],
    ]
}
