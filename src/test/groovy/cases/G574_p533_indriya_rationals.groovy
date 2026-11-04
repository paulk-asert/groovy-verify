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
 * 'P533 indriya number system' — the units pack modelled a quantity's value as an exact Real, but indriya 2.2.4 holds
 * it as an Integer, Long, BigInteger, RationalNumber or BigDecimal (measured), and the model was right only for some.
 * Integer-typed values stay exact rationals through every operation, so {@code 10 km / 3 · 3} is exactly 10000 m (it
 * skipped since Phase 531) and now proves. A BigDecimal value is exact until a RationalNumber meets it as 34 digits,
 * including on the SI round trip a non-SI unit's arithmetic takes, so {@code 1.5 m} to miles and back is 1.4999…948;
 * that and four other runtime-false read-outs proved, and now skip. And a bare {@code getValue() == x} on a
 * RationalNumber is {@code equals} (RationalNumber isn't Comparable): {@code 1 cm} in metres {@code == 0.01} is false,
 * and proved; it now skips, while the {@code as BigDecimal} read-out (34 digits) proves.
 */
class G574_p533_indriya_rationals {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 533: indriya's number system — integer-typed quantities are exact rationals (10 km / 3 · 3 is 10000 m), a BigDecimal is exact only where no RationalNumber meets it, and a bare getValue() == x on a RationalNumber is equals."

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — units/records: no grid-executable runtime arm'

    static final String G = "P533 indriya number system"
    static final String Q = 'Quantities.getQuantity'
    static final String MI = 'USCustomary.MILE'
    static final String FT = 'USCustomary.FOOT'
    static final String OUT = 'outside fragment'
    static final String REFUTED = 'Cannot prove postcondition'
    static final String UOMX = 'import systems.uom.common.USCustomary\n'

    static String uom(String ens, String body) {
        HDR + UOM2 + UOMX + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
            "class C { @Ensures({ ${ens} })\n static BigDecimal f() { ${body} } }"
    }

    static String uomB(String body) {
        HDR + UOM2 + UOMX + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
            "class C { @Ensures({ result })\n static boolean f() { ${body} } }"
    }

    static String uomN(String body) {
        HDR + UOM2 + UOMX + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
            "class C { @Ensures({ result })\n static boolean f(int n) { ${body} } }"
    }

    /** `X.getValue() as BigDecimal`, the numeric read-out. */
    static String bd(String q) { "${q}.getValue() as BigDecimal" }

    static final List<Map> CASES = [
        // ---- integer-typed values: exact rationals ----
        [group: G, name: "10 km / 3 · 3 in metres is 10000", ok: true,
         src: uom('result == 10000', bd("${Q}(10, KILO(METRE)).divide(3).multiply(3).to(METRE)"))],
        [group: G, name: "10 km / 3 · 3 in metres isn't 10001", expect: REFUTED,
         src: uom('result == 10001', bd("${Q}(10, KILO(METRE)).divide(3).multiply(3).to(METRE)"))],
        [group: G, name: "1 m / 7 · 7 is 1", ok: true, src: uom('result == 1', bd("${Q}(1, METRE).divide(7).multiply(7)"))],
        [group: G, name: "1 m / 3 + 2 m / 3 is 1", ok: true,
         src: uom('result == 1', bd("${Q}(1, METRE).divide(3).add(${Q}(2, METRE).divide(3))"))],
        [group: G, name: "1 m / 2^49 · 2^49 is 1: an integer value's reciprocal is exact at any width", ok: true,
         src: uom('result == 1', bd("${Q}(1, METRE).divide(562949953421312).multiply(562949953421312)"))],
        [group: G, name: "1 km / 3 s · 3 s in metres is 1000", ok: true,
         src: uom('result == 1000', bd("${Q}(1, KILO(METRE)).divide(${Q}(3, SECOND)).multiply(${Q}(3, SECOND)).asType(javax.measure.quantity.Length).to(METRE)"))],
        [group: G, name: "1 m / 0 is outside the fragment (indriya throws IllegalArgumentException)", expect: OUT,
         src: uom('result == 0', bd("${Q}(1, METRE).divide(0)"))],
        [group: G, name: "1 m / 3 · 3 == 1 m", ok: true, src: uomB("${Q}(1, METRE).divide(3).multiply(3) == ${Q}(1, METRE)")],
        [group: G, name: "10 km / 3 == 10000 m / 3: rationals compare exactly across units", ok: true,
         src: uomB("${Q}(10, KILO(METRE)).divide(3) == ${Q}(10000, METRE).divide(3)")],
        [group: G, name: "1 m / 3 != 2 m / 3", ok: true, src: uomB("${Q}(1, METRE).divide(3) != ${Q}(2, METRE).divide(3)")],
        [group: G, name: "n km / 3 · 3 == n km, for any int n", ok: true,
         src: uomN("${Q}(n, KILO(METRE)).divide(3).multiply(3) == ${Q}(n, KILO(METRE))")],
        [group: G, name: "n km in metres is n · 1000, read bare (an integer)", ok: true,
         src: uomN("${Q}(n, KILO(METRE)).to(METRE).getValue() == n * 1000")],
        // ---- a RationalNumber's read-outs ----
        [group: G, name: "1 m / 3 reads as 34 digits under as BigDecimal", ok: true,
         src: uom('result == 0.3333333333333333333333333333333333', bd("${Q}(1, METRE).divide(3)"))],
        [group: G, name: "1 m / 3 read as BigDecimal isn't a third: · 3 is 0.999…9", expect: REFUTED,
         src: uom('result * 3 == 1', bd("${Q}(1, METRE).divide(3)"))],
        [group: G, name: "2 m / 3 reads rounded half-even at 34 digits: …667", ok: true,
         src: uom('result == 0.6666666666666666666666666666666667', bd("${Q}(2, METRE).divide(3)"))],
        [group: G, name: "1 m / 2^49 (35 digits) reads half-even at 34: …312, not …313", ok: true,
         src: uom('result == 1.776356839400250464677810668945312E-15', bd("${Q}(1, METRE).divide(562949953421312)"))],
        [group: G, name: "-2 m / 3 reads -0.666…667", ok: true,
         src: uom('result == -0.6666666666666666666666666666666667', bd("${Q}(-2, METRE).divide(3)"))],
        [group: G, name: "1 cm in metres reads 0.01 under as BigDecimal", ok: true,
         src: uom('result == 0.01', bd("${Q}(1, CENTI(METRE)).to(METRE)"))],
        [group: G, name: "a bare getValue() == 0.01 on 1 cm in metres is outside the fragment (RationalNumber == is equals)", expect: OUT,
         src: uomB("${Q}(1, CENTI(METRE)).to(METRE).getValue() == 0.01")],
        [group: G, name: "a bare getValue() == 0.25 on 1 m / 4 is outside the fragment", expect: OUT,
         src: uomB("${Q}(1, METRE).divide(4).getValue() == 0.25")],
        [group: G, name: "n km / 3 · 3 in metres, read out, is outside the fragment (a symbolic rational)", expect: OUT,
         src: uomN("(${bd("${Q}(n, KILO(METRE)).divide(3).multiply(3).to(METRE)")}) == n * 1000")],
        // ---- a BigDecimal value: exact unless a RationalNumber meets it ----
        [group: G, name: "1.5 m + 1 cm is 1.51", ok: true, src: uom('result == 1.51', bd("${Q}(1.5, METRE).add(${Q}(1, CENTI(METRE)))"))],
        [group: G, name: "1.5 km + 1 m in metres is 1501", ok: true,
         src: uom('result == 1501', bd("${Q}(1.5, KILO(METRE)).add(${Q}(1, METRE)).to(METRE)"))],
        [group: G, name: "1.5 mile in metres is 2414.016", ok: true, src: uom('result == 2414.016', bd("${Q}(1.5, ${MI}).to(METRE)"))],
        [group: G, name: "1.5 m's bare value is 1.5", ok: true, src: uomB("${Q}(1.5, METRE).getValue() == 1.5")],
        [group: G, name: "1.5 m to miles and back is outside the fragment: 1.4999…948", expect: OUT,
         src: uom('result == 1.5', bd("${Q}(1.5, METRE).to(${MI}).to(METRE)"))],
        [group: G, name: "1.5 m to feet and back is outside the fragment: 1.4999…904", expect: OUT,
         src: uom('result == 1.5', bd("${Q}(1.5, METRE).to(${FT}).to(METRE)"))],
        [group: G, name: "1.5 mile + 1 m in metres is outside the fragment: 2415.0159…916", expect: OUT,
         src: uom('result == 2415.016', bd("${Q}(1.5, ${MI}).add(${Q}(1, METRE)).to(METRE)"))],
        [group: G, name: "1.5 mile · 2 is outside the fragment: 2.9999…", expect: OUT,
         src: uom('result == 3', bd("${Q}(1.5, ${MI}).multiply(2)"))],
        [group: G, name: "1.5 m to miles and back == 1.5 m is outside the fragment", expect: OUT,
         src: uomB("${Q}(1.5, METRE).to(${MI}).to(METRE) == ${Q}(1.5, METRE)")],
        [group: G, name: "1.5 mile == 2414.016 m is outside the fragment (false at runtime: the argument converts to miles)", expect: OUT,
         src: uomB("${Q}(1.5, ${MI}) == ${Q}(2414.016, METRE)")],
        [group: G, name: "2414.016 m == 1.5 mile (the argument converts to metres exactly)", ok: true,
         src: uomB("${Q}(2414.016, METRE) == ${Q}(1.5, ${MI})")],
        [group: G, name: "1 m / 3 == 0.333…3 m is outside the fragment (true at runtime: compared at 34 digits)", expect: OUT,
         src: uomB("!(${Q}(1, METRE).divide(3) == ${Q}(0.3333333333333333333333333333333333, METRE))")],
        [group: G, name: "1.5 km + 0 m's bare value is outside the fragment (a RationalNumber 3/2 at runtime)", expect: OUT,
         src: uomB("${Q}(1.5, KILO(METRE)).add(${Q}(0, METRE)).getValue() == 1.5")],
        [group: G, name: "1.5 km + 0 m reads 1.5 under as BigDecimal", ok: true,
         src: uom('result == 1.5', bd("${Q}(1.5, KILO(METRE)).add(${Q}(0, METRE))"))],
    ]
}
