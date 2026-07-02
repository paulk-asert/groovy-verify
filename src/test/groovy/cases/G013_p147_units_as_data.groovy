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

/** 'P147 units-as-data' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G013_p147_units_as_data {

    static final List<Map> CASES = [

        // ---------- Phase 147: units-as-data — a Unit(scale, dims) value + a getQuantity factory over it ----------
        // The last structural piece of the literal JSR 385 form, reached with NO new engine code — it composes
        // from the multi-component record (142), carrier-typed-argument chaining (145), and read-out (146): a
        // `Unit(scale, l, m, t)` is itself a record value, `Quantity.of(v, unit)` is a factory reading the unit's
        // fields, and a metric prefix is a `Unit -> Unit` factory. So the full JSR-385-shaped expression
        // `Quantity.of(1, Unit.kilo(Unit.metre())).plus(Quantity.of(1, Unit.mile())).value == 2609.344` verifies
        // end to end — the bespoke twin of `getQuantity(1, KILO(METRE)).add(getQuantity(1, MILE)).to(METRE).getValue()`.
        [group: 'P147 units-as-data', name: 'getQuantity over a Unit value', ok: true,
         src: HDR +
              'record Unit(BigDecimal scale, int l, int m, int t) {\n' +
              '    @Ensures({ result.scale == 1.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Unit metre() { new Unit(1.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.scale == u.scale * 1000.0 && result.l == u.l && result.m == u.m && result.t == u.t })\n' +
              '    static Unit kilo(Unit u) { new Unit(u.scale * 1000.0, u.l, u.m, u.t) }\n' +
              '}\n' +
              'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * u.scale && result.l == u.l && result.m == u.m && result.t == u.t })\n' +
              '    static Quantity of(BigDecimal v, Unit u) { new Quantity(v * u.scale, u.l, u.m, u.t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.value == 1000.0 && result.l == 1 }) static Quantity total() {\n' +
              '    Quantity.of(1.0, Unit.kilo(Unit.metre())) } }'],
        [group: 'P147 units-as-data', name: 'full JSR-385-shaped expression', ok: true,
         src: HDR +
              'record Unit(BigDecimal scale, int l, int m, int t) {\n' +
              '    @Ensures({ result.scale == 1.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Unit metre() { new Unit(1.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.scale == 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Unit mile() { new Unit(1609.344, 1, 0, 0) }\n' +
              '    @Ensures({ result.scale == u.scale * 1000.0 && result.l == u.l && result.m == u.m && result.t == u.t })\n' +
              '    static Unit kilo(Unit u) { new Unit(u.scale * 1000.0, u.l, u.m, u.t) }\n' +
              '}\n' +
              'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * u.scale && result.l == u.l && result.m == u.m && result.t == u.t })\n' +
              '    static Quantity of(BigDecimal v, Unit u) { new Quantity(v * u.scale, u.l, u.m, u.t) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 2609.344 }) static BigDecimal total() {\n' +
              '    Quantity.of(1.0, Unit.kilo(Unit.metre())).plus(Quantity.of(1.0, Unit.mile())).value } }'],
        [group: 'P147 units-as-data', name: 'wrong total refutes', expect: 'Cannot prove postcondition',
         src: HDR +
              'record Unit(BigDecimal scale, int l, int m, int t) {\n' +
              '    @Ensures({ result.scale == 1.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Unit metre() { new Unit(1.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.scale == 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Unit mile() { new Unit(1609.344, 1, 0, 0) }\n' +
              '    @Ensures({ result.scale == u.scale * 1000.0 && result.l == u.l && result.m == u.m && result.t == u.t })\n' +
              '    static Unit kilo(Unit u) { new Unit(u.scale * 1000.0, u.l, u.m, u.t) }\n' +
              '}\n' +
              'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * u.scale && result.l == u.l && result.m == u.m && result.t == u.t })\n' +
              '    static Quantity of(BigDecimal v, Unit u) { new Quantity(v * u.scale, u.l, u.m, u.t) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 2600.0 }) static BigDecimal total() {\n' +
              '    Quantity.of(1.0, Unit.kilo(Unit.metre())).plus(Quantity.of(1.0, Unit.mile())).value } }'],
        [group: 'P147 units-as-data', name: 'dimension guard fires through units', expect: 'Cannot prove precondition',
         src: HDR +
              'record Unit(BigDecimal scale, int l, int m, int t) {\n' +
              '    @Ensures({ result.scale == 1.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Unit metre() { new Unit(1.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.scale == 1.0 && result.l == 0 && result.m == 1 && result.t == 0 })\n' +
              '    static Unit gram() { new Unit(1.0, 0, 1, 0) }\n' +
              '}\n' +
              'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * u.scale && result.l == u.l && result.m == u.m && result.t == u.t })\n' +
              '    static Quantity of(BigDecimal v, Unit u) { new Quantity(v * u.scale, u.l, u.m, u.t) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 2.0 }) static BigDecimal total() {\n' +
              '    Quantity.of(1.0, Unit.metre()).plus(Quantity.of(1.0, Unit.gram())).value } }'],
    ]
}
