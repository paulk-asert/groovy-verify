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

/** 'P145 carrier chain' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G014_p145_carrier_chain {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A carrier-returning call is a value in expression position, not only a local-assignment RHS, so a single-expression chain resolves: Quantity.km(1).plus(Quantity.mile(1)) == 2609.344 in metres (receiver and argument are both factory calls), the fluent twin of the JSR 385 example — the guarded .plus precondition still discharges over the real argument (a wrong total refutes the postcondition, a mismatched dimension refutes the guard).'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — units/records: no grid-executable runtime arm'

    static final List<Map> CASES = [

        // ---------- Phase 145: carrier-returning calls as values in expression position (chaining) ----------
        // A carrier-returning call is now a value, not only a local-assignment RHS — so a single-expression
        // CHAIN resolves: `Quantity.km(1).plus(Quantity.mile(1))` (receiver and argument are both factory calls)
        // proves 2609.344 in metres, the fluent twin of the JSR 385 example. carrierValueOf models each nested
        // call into a fresh carrier handle constrained by its @Ensures; the guarded `.plus` precondition still
        // discharges over the real argument (mismatched dimensions refute).
        [group: 'P145 carrier chain', name: 'single-expression chain verifies', ok: true,
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.value == v * 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity mile(BigDecimal v) { new Quantity(v * 1609.344, 1, 0, 0) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.value == 2609.344 }) static Quantity total() {\n' +
              '    Quantity.km(1.0).plus(Quantity.mile(1.0)) } }'],
        [group: 'P145 carrier chain', name: 'chain wrong total refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.value == v * 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity mile(BigDecimal v) { new Quantity(v * 1609.344, 1, 0, 0) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.value == 2600.0 }) static Quantity total() {\n' +
              '    Quantity.km(1.0).plus(Quantity.mile(1.0)) } }'],
        [group: 'P145 carrier chain', name: 'chain mismatched dimension refutes guard', expect: 'Cannot prove precondition',
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.value == v && result.l == 0 && result.m == 1 && result.t == 0 })\n' +
              '    static Quantity gram(BigDecimal v) { new Quantity(v, 0, 1, 0) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.value == 1001.0 }) static Quantity total() {\n' +
              '    Quantity.km(1.0).plus(Quantity.gram(1.0)) } }'],
        [group: 'P145 carrier chain', name: 'chain as local RHS', ok: true,
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.value == v * 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity mile(BigDecimal v) { new Quantity(v * 1609.344, 1, 0, 0) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.value == 2609.344 }) static Quantity total() {\n' +
              '    Quantity s = Quantity.km(1.0).plus(Quantity.mile(1.0)); s } }'],
    ]
}
