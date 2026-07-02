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

/** 'P144 carrier replay' — 3 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G016_p144_carrier_replay {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A carrier-returning contracted call (a factory like Quantity.km(1), or a routed operator) is modelled in the precondition-check\'s prefix replay, not havoced to an Int — so factory-built operands feed a guarded operator (Quantity.km(1) + Quantity.mile(1) == 2609.344 in metres), the dimension guard fires across the replay, and a wrong total refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 144: carrier-returning calls modelled in the precondition-check replay ----------
        // The bespoke equivalent of the JSR 385 `1 km + 1 mile == 2609.344` example: factory-built operands
        // (`Quantity.km(1)` / `Quantity.mile(1)`) feed a GUARDED `+`. The guard `l == o.l` is checked at the
        // `a + b` site, whose precondition-check replays the prefix — so each factory call must be modelled
        // there as a real Quantity (Phase 144), not havoced to an Int (which used to crash `eq(Q, Int)`).
        [group: 'P144 carrier replay', name: 'factory operands feed a guarded operator', ok: true,
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.value == v * 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity mile(BigDecimal v) { new Quantity(v * 1609.344, 1, 0, 0) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C {\n' +
              '    @Ensures({ result.value == 2609.344 })\n' +
              '    static Quantity total() {\n' +
              '        Quantity a = Quantity.km(1.0)\n' +
              '        Quantity b = Quantity.mile(1.0)\n' +
              '        Quantity s = a + b\n' +
              '        s\n' +
              '    }\n' +
              '}'],
        // The total is genuinely computed (not skipped): a wrong total refutes the postcondition.
        [group: 'P144 carrier replay', name: 'factory operands, wrong total refutes', expect: 'Cannot prove postcondition',
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
              '    Quantity a = Quantity.km(1.0); Quantity b = Quantity.mile(1.0); Quantity s = a + b; s } }'],
        // The guard fires across the replay too: factory-built operands of DIFFERENT dimensions
        // (a length + a mass) refute `plus`'s precondition `l == o.l` at the `a + b` site.
        [group: 'P144 carrier replay', name: 'factory operands, mismatched dimension refutes the guard', expect: 'Cannot prove precondition',
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
              '    Quantity a = Quantity.km(1.0); Quantity b = Quantity.gram(1.0); Quantity s = a + b; s } }'],
    ]
}
