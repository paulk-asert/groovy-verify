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

/** 'P146 chain read-out' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G015_p146_chain_read_out {

    static final List<Map> CASES = [

        // ---------- Phase 146: read-out in the same expression (a component read on a chain result) ----------
        // The terminal step of the JSR-385 shape: `Quantity.km(1).plus(Quantity.mile(1)).value` reads the SI
        // magnitude straight off the chain result — proving 2609.344 as a BigDecimal, no intermediate locals.
        // Each maximal carrier call in the expression is hoisted to a temp local bound to its modelled value, so
        // `.value` becomes an ordinary component read; the read-out composes with decimal arithmetic and works as
        // a local RHS too. A wrong magnitude refutes.
        [group: 'P146 chain read-out', name: 'chain read-out .value verifies', ok: true,
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.value == v * 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity mile(BigDecimal v) { new Quantity(v * 1609.344, 1, 0, 0) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 2609.344 }) static BigDecimal total() {\n' +
              '    Quantity.km(1.0).plus(Quantity.mile(1.0)).value } }'],
        [group: 'P146 chain read-out', name: 'chain read-out wrong refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.value == v * 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity mile(BigDecimal v) { new Quantity(v * 1609.344, 1, 0, 0) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 2600.0 }) static BigDecimal total() {\n' +
              '    Quantity.km(1.0).plus(Quantity.mile(1.0)).value } }'],
        [group: 'P146 chain read-out', name: 'read-out with arithmetic', ok: true,
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.value == v * 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity mile(BigDecimal v) { new Quantity(v * 1609.344, 1, 0, 0) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 2610.344 }) static BigDecimal total() {\n' +
              '    Quantity.km(1.0).plus(Quantity.mile(1.0)).value + 1.0 } }'],
        [group: 'P146 chain read-out', name: 'read-out as local RHS', ok: true,
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == v * 1000.0 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity km(BigDecimal v) { new Quantity(v * 1000.0, 1, 0, 0) }\n' +
              '    @Ensures({ result.value == v * 1609.344 && result.l == 1 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity mile(BigDecimal v) { new Quantity(v * 1609.344, 1, 0, 0) }\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result == 2609.344 }) static BigDecimal total() {\n' +
              '    BigDecimal v = Quantity.km(1.0).plus(Quantity.mile(1.0)).value; v } }'],
    ]
}
