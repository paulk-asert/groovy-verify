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
 * 'P532 metre per second' — Phase 531's last open item. {@code METRE_PER_SECOND} wasn't in the units pack's curated
 * table, so a quantity built in it, or read out in it, skipped. It is now a curated unit (scale 1, dimension Speed
 * {@code [1,0,-1]}, pinned against indriya by UnitScaleTest). A quotient's {@code Quantity<?>} can't be read out with
 * {@code to(METRE_PER_SECOND)} directly (STC rejects the wildcard), so {@code q.asType(Speed)} is modelled too: indriya
 * checks the kind and returns the quantity itself, so magnitude and unit carry through, and a kind mismatch (which
 * throws) skips.
 */
class G573_p532_metre_per_second {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 532: METRE_PER_SECOND is a curated unit (scale 1, Speed), and q.asType(Speed) reads a quotient out in it."

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — units/records: no grid-executable runtime arm'

    static final String G = "P532 metre per second"
    static final String Q = 'Quantities.getQuantity'

    static String uom(String ens, String body) {
        HDR + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
            "class C { @Ensures({ ${ens} })\n static BigDecimal f() { ${body} } }"
    }

    static String uomB(String body) {
        HDR + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
            "class C { @Ensures({ result })\n static boolean f() { ${body} } }"
    }

    /** `(10 m / 2 s).asType(K)` — a Speed-valued quotient seen as kind K. */
    static String speedAs(String k) { "${Q}(10, METRE).divide(${Q}(2, SECOND)).asType(javax.measure.quantity.${k})" }

    static final List<Map> CASES = [
        // ---- METRE_PER_SECOND as a curated unit ----
        [group: G, name: "a speed built in METRE_PER_SECOND reads back its value", ok: true,
         src: uom('result == 5', "${Q}(5, METRE_PER_SECOND).getValue() as BigDecimal")],
        [group: G, name: "a speed's wrong value is refuted", expect: 'Cannot prove postcondition',
         src: uom('result == 6', "${Q}(5, METRE_PER_SECOND).getValue() as BigDecimal")],
        [group: G, name: "10 m / 2 s is 5 m/s", ok: true,
         src: uomB("${Q}(10, METRE).divide(${Q}(2, SECOND)) == ${Q}(5, METRE_PER_SECOND)")],
        [group: G, name: "5 m/s · 2 s is 10 m", ok: true,
         src: uomB("${Q}(5, METRE_PER_SECOND).multiply(${Q}(2, SECOND)) == ${Q}(10, METRE)")],
        [group: G, name: "a prefix scales it: 5 km/s read in m/s is 5000", ok: true,
         src: uom('result == 5000', "${Q}(5, KILO(METRE_PER_SECOND)).to(METRE_PER_SECOND).getValue() as BigDecimal")],
        [group: G, name: "18 km / 2 s is 9 km/s", ok: true,
         src: uomB("${Q}(18, KILO(METRE)).divide(${Q}(2, SECOND)) == ${Q}(9, KILO(METRE_PER_SECOND))")],
        [group: G, name: "18 km / 3 s is 6 km/s: integer values are exact rationals (Phase 533)", ok: true,
         src: uomB("${Q}(18, KILO(METRE)).divide(${Q}(3, SECOND)) == ${Q}(6, KILO(METRE_PER_SECOND))")],
        [group: G, name: "a speed claimed as a length is refuted on dimension", expect: 'Cannot prove postcondition',
         src: uomB("${Q}(1, METRE_PER_SECOND) == ${Q}(1, METRE)")],
        // ---- asType(K): a kind check that returns the quantity itself ----
        [group: G, name: "a quotient read out in m/s through asType(Speed) is 5", ok: true,
         src: uom('result == 5', "${speedAs('Speed')}.to(METRE_PER_SECOND).getValue() as BigDecimal")],
        [group: G, name: "a quotient's asType(Speed) read-out with the wrong value is refuted", expect: 'Cannot prove postcondition',
         src: uom('result == 6', "${speedAs('Speed')}.to(METRE_PER_SECOND).getValue() as BigDecimal")],
        [group: G, name: "asType(Speed) keeps the quantity: it equals 5 m/s", ok: true,
         src: uomB("${speedAs('Speed')} == ${Q}(5, METRE_PER_SECOND)")],
        [group: G, name: "asType keeps the unit: 5 km/s read without to() is 5", ok: true,
         src: uom('result == 5', "${Q}(5, KILO(METRE_PER_SECOND)).asType(javax.measure.quantity.Speed).getValue() as BigDecimal")],
        [group: G, name: "asType keeps the unit: 5 km/s isn't read as 5000", expect: 'Cannot prove postcondition',
         src: uom('result == 5000', "${Q}(5, KILO(METRE_PER_SECOND)).asType(javax.measure.quantity.Speed).getValue() as BigDecimal")],
        [group: G, name: "asType to the wrong kind (it throws) is outside the fragment", expect: 'outside fragment',
         src: uom('result == 5', "${speedAs('Length')}.to(METRE).getValue() as BigDecimal")],
        [group: G, name: "asType to an uncurated kind is outside the fragment", expect: 'outside fragment',
         src: uom('result == 5', "${speedAs('Pressure')}.getValue() as BigDecimal")],
    ]
}
