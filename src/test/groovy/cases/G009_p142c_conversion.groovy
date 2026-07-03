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

/** 'P142c conversion' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G009_p142c_conversion {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'In-record unit conversion: a factory (km) and accessor (inKm) are scale arithmetic on the component, so the round-trip `km(2).inKm() == 2` and record equality `km(1) == metres(1000)` verify, a wrong factor refutes, and a cross-class `Length.km(2)` resolves.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — units/records: no grid-executable runtime arm'

    static final List<Map> CASES = [

        // ---------- Phase 142c: in-record unit conversion (the construct-to-SI side, multiplicative) ----------
        // A `km(v)` factory scales the value to SI (metres). A cross-class `Length.km(2)` resolves and pins the
        // component to 2000 — so a value entered in km is verified in metres.
        [group: 'P142c conversion', name: 'cross-class factory construction (km → metres)', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {\n' +
              '  @Ensures({ result.metres == v * 1000.0 }) static Length km(BigDecimal v) { new Length(v * 1000.0) } }\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 2000.0 }) static BigDecimal m() { Length r = Length.km(2.0); r.metres } }'],
        // A wrong constructed value refutes at the use site (1 km is 1000 m, not 999).
        [group: 'P142c conversion', name: 'wrong converted value refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'record Length(BigDecimal metres) {\n' +
              '  @Ensures({ result.metres == v * 1000.0 }) static Length km(BigDecimal v) { new Length(v * 1000.0) } }\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 999.0 }) static BigDecimal m() { Length r = Length.km(1.0); r.metres } }'],
        // Two constructions of the same physical length are EQUAL (`1 km == 1000 m`) — record equality, the
        // cleanest "same quantity, different unit" check, all multiplicative.
        [group: 'P142c conversion', name: 'two constructions of one length are equal', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {\n' +
              '  @Ensures({ result.metres == v * 1000.0 }) static Length km(BigDecimal v) { new Length(v * 1000.0) } }\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == true }) static boolean eq() { Length a = Length.km(1.0); Length b = new Length(1000.0); a == b } }'],
        // ... and two DIFFERENT physical lengths are NOT equal (1 km ≠ 2000 m) — the equality is a real proof.
        [group: 'P142c conversion', name: 'different lengths are not equal (refutes)', expect: 'Cannot prove postcondition',
         src: HDR + 'record Length(BigDecimal metres) {\n' +
              '  @Ensures({ result.metres == v * 1000.0 }) static Length km(BigDecimal v) { new Length(v * 1000.0) } }\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == true }) static boolean eq() { Length a = Length.km(1.0); Length b = new Length(2000.0); a == b } }'],
    ]
}
