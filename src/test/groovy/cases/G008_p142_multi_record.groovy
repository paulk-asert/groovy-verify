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

/** 'P142 multi-record' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G008_p142_multi_record {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A multi-component record is a one-constructor N-field datatype (the TupleN analogue), so `new R(a,b).f` round-trips — enabling a dimension-carrying Quantity(value, L, M, T) whose multiply scales the value and composes the exponent vector, the full dimensional algebra in one type.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — units/records: no grid-executable runtime arm'

    static final List<Map> CASES = [

        // ---------- Phase 142: multi-component record as a one-constructor N-field datatype ----------
        // `new R(a, b).f == a/b` round-trips for a record with several components (the TupleN analogue).
        [group: 'P142 multi-record', name: 'construct then read (two components)', ok: true,
         src: HDR + 'record V(int x, int y) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.x == 2 && result.y == 3 }) static V make() { new V(2, 3) } }'],
        [group: 'P142 multi-record', name: 'wrong component refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'record V(int x, int y) {}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C { @Ensures({ result.x == 2 && result.y == 99 }) static V make() { new V(2, 3) } }'],
        // The dimension-carrying record — ONE type for every unit: a value plus its (L,M,T) exponent vector.
        // `×` scales the value AND adds the exponents, so Length(2 m,[1,0,0]) × Length(3 m,[1,0,0]) is
        // Area(6 m²,[2,0,0]) — the full dimensional algebra in a single record, value and dimension both proved.
        [group: 'P142 multi-record', name: 'dimension-carrying Quantity: value and exponents compose', ok: true,
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == value * o.value && result.l == l + o.l && result.m == m + o.m && result.t == t + o.t })\n' +
              '    Quantity multiply(Quantity o) { new Quantity(value * o.value, l + o.l, m + o.m, t + o.t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C {\n' +
              '    @Ensures({ result.value == 6.0 && result.l == 2 && result.m == 0 && result.t == 0 })\n' +
              '    static Quantity area() {\n' +
              '        Quantity a = new Quantity(2.0, 1, 0, 0)\n' +
              '        Quantity b = new Quantity(3.0, 1, 0, 0)\n' +
              '        Quantity s = a * b\n' +
              '        s\n' +
              '    }\n' +
              '}'],
        // A wrong exponent refutes — the dimension composition is a real proof (L×L is exponent 2, not 1).
        [group: 'P142 multi-record', name: 'dimension-carrying Quantity: wrong exponent refutes', expect: 'Cannot prove postcondition',
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Ensures({ result.value == value * o.value && result.l == l + o.l && result.m == m + o.m && result.t == t + o.t })\n' +
              '    Quantity multiply(Quantity o) { new Quantity(value * o.value, l + o.l, m + o.m, t + o.t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C {\n' +
              '    @Ensures({ result.l == 1 })\n' +
              '    static Quantity area() {\n' +
              '        Quantity a = new Quantity(2.0, 1, 0, 0)\n' +
              '        Quantity b = new Quantity(3.0, 1, 0, 0)\n' +
              '        Quantity s = a * b\n' +
              '        s\n' +
              '    }\n' +
              '}'],
        // The addition half of the algebra (Phase 142b): `+` on Quantity requires *matching* dimensions. A guarded
        // `plus` (@Requires the exponents are equal) routes, the guard is checked at the `a + b` site — so same-
        // dimension addition verifies, and adding a Length to a Mass REFUTES (the units bug the type system can't
        // catch, since every quantity is one `Quantity` type).
        [group: 'P142 multi-record', name: 'dimensional addition: same dimension verifies', ok: true,
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value && result.l == l })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C {\n' +
              '    @Ensures({ result.value == 5.0 && result.l == 1 })\n' +
              '    static Quantity add() {\n' +
              '        Quantity a = new Quantity(2.0, 1, 0, 0)\n' +
              '        Quantity b = new Quantity(3.0, 1, 0, 0)\n' +
              '        Quantity s = a + b\n' +
              '        s\n' +
              '    }\n' +
              '}'],
        [group: 'P142 multi-record', name: 'dimensional addition: mismatched dimensions refute', expect: 'Cannot prove precondition',
         src: HDR + 'record Quantity(BigDecimal value, int l, int m, int t) {\n' +
              '    @Requires({ l == o.l && m == o.m && t == o.t })\n' +
              '    @Ensures({ result.value == value + o.value && result.l == l })\n' +
              '    Quantity plus(Quantity o) { new Quantity(value + o.value, l, m, t) }\n' +
              '}\n' + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              'class C {\n' +
              '    @Ensures({ result.value == 5.0 })\n' +
              '    static Quantity add() {\n' +
              '        Quantity a = new Quantity(2.0, 1, 0, 0)\n' +
              '        Quantity b = new Quantity(3.0, 0, 1, 0)\n' +
              '        Quantity s = a + b\n' +
              '        s\n' +
              '    }\n' +
              '}'],
    ]
}
