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

/** 'P133 record ctor' — 17 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G007_p133_record_ctor {

    static final List<Map> CASES = [

        // ---------- Phase 133: single-component record modelled as a one-constructor datatype ----------
        // `new R(v).f == v` round-trips by datatype theory — the canonical-constructor gap, closed for records.
        [group: 'P133 record ctor', name: 'construct then read round-trips', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.metres == 1000.0 }) static Length oneKm() { new Length(1000.0) } }'],
        [group: 'P133 record ctor', name: 'wrong component value refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'record Length(BigDecimal metres) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.metres == 999.0 }) static Length oneKm() { new Length(1000.0) } }'],
        [group: 'P133 record ctor', name: 'computed component verifies', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ v != null }) @Ensures({ result.metres == v * 1000.0 }) static Length km(BigDecimal v) { new Length(v * 1000.0) } }'],
        // An instance method on the record — its own contract verifies (`this.metres` reads the component).
        [group: 'P133 record ctor', name: 'instance method contract verifies (this.field)', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {\n' +
              '  @Requires({ o != null }) @Ensures({ result.metres == metres + o.metres }) Length plus(Length o) { new Length(metres + o.metres) } }\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + 'class C { static int z() { 0 } }'],
        // A bespoke units value type: a length built from a km + a metre magnitude, the SI total exact
        // (1 km + 1609.344 m == 2609.344 m). Constructed value, read back through its component.
        [group: 'P133 record ctor', name: 'bespoke units: length total verifies', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ km != null && m != null }) @Ensures({ result.metres == km * 1000.0 + m })\n' +
              '          static Length total(BigDecimal km, BigDecimal m) { new Length(km * 1000.0 + m) } }'],
        // And the bug refutes: a wrong magnitude claim.
        [group: 'P133 record ctor', name: 'bespoke units: wrong magnitude refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'record Length(BigDecimal metres) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Requires({ km != null && m != null }) @Ensures({ result.metres == km * 1000.0 })\n' +
              '          static Length total(BigDecimal km, BigDecimal m) { new Length(km * 1000.0 + m) } }'],
        // Robustness: an arithmetic operator on a record operand skips gracefully (no crash), not a wrong proof.
        [group: 'P133 record ctor', name: 'operator on a record skips (no crash)', expect: 'Skipped verification of postcondition',
         src: HDR + 'record Length(BigDecimal metres) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.metres == 2609.344 }) static Length s() { new Length(1000.0) + new Length(1609.344) } }'],
        // Carrier-typed locals verify end-to-end (Phase 133): construct two lengths, read their components,
        // and the constructed sum's component is exact — a pretty, self-contained units conservation proof.
        [group: 'P133 record ctor', name: 'bespoke units: conservation via locals verifies', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.metres == 2609.344 })\n' +
              '          static Length total() { Length a = new Length(1000.0); Length b = new Length(1609.344); new Length(a.metres + b.metres) } }'],
        // OPERATOR routing (Phase 133): `a + b` over a record with an instance `plus` dispatches to `a.plus(b)`,
        // and the cross-class instance @Ensures is assumed at the call — so the pretty form verifies exactly.
        [group: 'P133 record ctor', name: 'pretty units: operator + verifies', ok: true,
         src: HDR +
              'record Length(BigDecimal metres) {\n' +
              '    @Ensures({ result.metres == metres + o.metres })\n' +
              '    Length plus(Length o) { new Length(metres + o.metres) }\n' +
              '}\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C {\n' +
              '    @Ensures({ result.metres == 2609.344 })\n' +
              '    static Length sum() {\n' +
              '        Length a = new Length(1000.0)\n' +
              '        Length b = new Length(1609.344)\n' +
              '        Length s = a + b\n' +
              '        s\n' +
              '    }\n' +
              '}'],
        // The same with a WRONG total refutes (operator routing is not vacuous).
        [group: 'P133 record ctor', name: 'pretty units: operator + wrong total refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'record Length(BigDecimal metres) {\n' +
              '  @Ensures({ result.metres == metres + o.metres }) Length plus(Length o) { new Length(metres + o.metres) } }\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.metres == 2600.0 }) static Length sum() {\n' +
              '  Length a = new Length(1000.0); Length b = new Length(1609.344); Length s = a + b; s } }'],
        // Soundness: an operator method WITH a @Requires is NOT routed (the operator site has no precondition
        // check), so it stays a loud skip rather than assuming @Ensures with an unchecked guard.
        // A GUARDED operator routes too (Phase 142b): `onMethodSelection` fires for `a + b` and checks plus's
        // @Requires at the site (here `o != null`, discharged because the operand is non-null), so it's sound.
        [group: 'P133 record ctor', name: 'guarded operator routes (precondition discharged)', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {\n' +
              '  @Requires({ o != null }) @Ensures({ result.metres == metres + o.metres }) Length plus(Length o) { new Length(metres + o.metres) } }\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.metres == 2609.344 }) static Length sum() {\n' +
              '  Length a = new Length(1000.0); Length b = new Length(1609.344); Length s = a + b; s } }'],
        // Soundness: a VIOLATED operator precondition refutes (plus's @Ensures holds only under its @Requires; a
        // negative operand breaks the guard, so the proof is rejected rather than assumed).
        [group: 'P133 record ctor', name: 'guarded operator: violated precondition refutes', expect: 'Cannot prove',
         src: HDR + 'record Length(BigDecimal metres) {\n' +
              '  @Requires({ metres >= 0.0 && o.metres >= 0.0 }) @Ensures({ result.metres >= 0.0 }) Length plus(Length o) { new Length(metres + o.metres) } }\n' +
              "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.metres >= 0.0 }) static Length sum() {\n' +
              '  Length a = new Length(-5.0); Length b = new Length(3.0); Length s = a + b; s } }'],
        // TYPE-CHANGING operator (Phase 133): `Length * Length -> Area` — `*` routes to a `multiply` returning a
        // *different* record type, the real dimensional algebra (rung two). Operands built body-local.
        [group: 'P133 record ctor', name: 'type-changing operator: Length * Length = Area', ok: true,
         src: HDR + 'record Area(BigDecimal squareMetres) {}\n' +
              'record Length(BigDecimal metres) {\n' +
              '    @Ensures({ result.squareMetres == metres * o.metres })\n' +
              '    Area multiply(Length o) { new Area(metres * o.metres) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C {\n' +
              '    @Ensures({ result.squareMetres == 6.0 })\n' +
              '    static Area area() {\n' +
              '        Length a = new Length(2.0)\n' +
              '        Length b = new Length(3.0)\n' +
              '        Area s = a * b\n' +
              '        s\n' +
              '    }\n' +
              '}'],
        // ... and a wrong area refutes (the dimensional operator is a real proof, not vacuous).
        [group: 'P133 record ctor', name: 'type-changing operator: wrong area refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'record Area(BigDecimal squareMetres) {}\n' +
              'record Length(BigDecimal metres) {\n' +
              '    @Ensures({ result.squareMetres == metres * o.metres }) Area multiply(Length o) { new Area(metres * o.metres) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.squareMetres == 5.0 })\n' +
              '          static Area area() { Length a = new Length(2.0); Length b = new Length(3.0); Area s = a * b; s } }'],
        // A static factory method's @Ensures is applied at the call (a `Length.km(1)` convenience constructor).
        [group: 'P133 record ctor', name: 'static factory method pins the result', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {\n' +
              '    @Ensures({ result.metres == v * 1000.0 }) static Length km(BigDecimal v) { new Length(v * 1000.0) }\n' +
              '    @Ensures({ result.metres == 1000.0 }) static Length oneKm() { Length r = km(1.0); r }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" + 'class C { static int z() { 0 } }'],
        // A carrier local read back through its component (single binding).
        [group: 'P133 record ctor', name: 'carrier local round-trips', ok: true,
         src: HDR + 'record Length(BigDecimal metres) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.metres == 5.0 }) static Length f() { Length a = new Length(5.0); a } }'],
        // new-is-non-null (Phase 133): a callee `@Requires({ s != null })` discharges when the actual is a
        // statically-non-null expression with no *name* to tie the nullity oracle to (a literal / `new R(…)` /
        // concatenation). Without the fix the formal's nullity is free and this precondition refutes.
        [group: 'P133 record ctor', name: 'non-variable non-null actual satisfies a non-null precondition', ok: true,
         src: HDR + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C {\n' +
              '  @Requires({ s != null }) static int g(String s) { 0 }\n' +
              '  static int f() { g("ab") } }'],
    ]
}
