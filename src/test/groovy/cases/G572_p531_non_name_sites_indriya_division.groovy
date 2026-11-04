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
 * 'P531 non-name sites and indriya division' — Phase 529's two leftovers. A contract's subscript of a String that
 * isn't a name ({@code t.name[0]}, {@code s.trim()[0]}, {@code (s + t)[0]}, {@code 'abc'[i]}) and its
 * {@code t.name.charAt(0)} proved {@code x == x} on an empty string, and a receiver's array field {@code t.a[0]} on an
 * empty array: each is now a Phase 528 site, owed where checked and assumed where filtering. And the units pack's
 * method {@code q.divide(x)} was exact Real division for any divisor, but indriya divides by multiplying with the
 * reciprocal, which a BigDecimal value meets rounded to 34 digits, and a read-out rounds a non-terminating rational to
 * 34 digits (measured, indriya 2.2.4): it now takes the DSL {@code /}'s guard, a closed terminating divisor whose
 * reciprocal fits 34 digits, so four runtime-false read-outs that proved now skip loudly.
 */
class G572_p531_non_name_sites_indriya_division {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 531: a contract's subscript or charAt of any String (t.name[0], s.trim()[0]) and a receiver's array field (t.a[0]) owe their bounds, and the units pack's q.divide(x) is exact only for a divisor indriya divides exactly."

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — units/records: no grid-executable runtime arm'

    static final String G = "P531 non-name sites and indriya division"
    static final String THROWS = 'may throw rather than hold or fail'
    static final String T = 'final class T { String name; int[] a; T(String n) { name = n } }\n'
    static final String TL = 'final class T { List<Integer> xs; T(List<Integer> x) { xs = x } }\n'

    static String uom(String ens, String body) {
        HDR + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
            "class C { @Ensures({ ${ens} })\n static BigDecimal f() { ${body} } }"
    }

    static String uomB(String body) {
        HDR + UOM2 + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
            "class C { @Ensures({ result })\n static boolean f() { ${body} } }"
    }

    static final List<Map> CASES = [
        // ---- a String receiver that isn't a name ----
        [group: G, name: "a postcondition's t.name[0] on a maybe-empty name is refused", expect: [THROWS, '-t.name.length() <= 0'],
         src: tc("class C { @Requires({ t != null && t.name != null }) @Ensures({ t.name[0] == t.name[0] }) static int f(T t) { 1 } }\n" + T)],
        [group: G, name: "a postcondition's s.trim()[0] is refused", expect: [THROWS, 's.trim().length()'],
         src: tc("class C { @Requires({ s != null }) @Ensures({ s.trim()[0] == s.trim()[0] }) static int f(String s) { 1 } }")],
        [group: G, name: "a postcondition's (s + t)[0] is refused", expect: [THROWS, '(s + t).length()'],
         src: tc("class C { @Requires({ s != null && t != null }) @Ensures({ (s + t)[0] == (s + t)[0] }) static int f(String s, String t) { 1 } }")],
        [group: G, name: "a literal's subscript owes its bounds: 'abc'[i]", expect: [THROWS, 'i <'],
         src: tc("class C { @Ensures({ 'abc'[i] == 'abc'[i] }) static int f(int i) { 1 } }")],
        [group: G, name: "a postcondition's t.name.charAt(0) is refused", expect: [THROWS, '0 <= 0 && 0 < t.name.length()'],
         src: tc("class C { @Requires({ t != null && t.name != null }) @Ensures({ t.name.charAt(0) == t.name.charAt(0) }) static int f(T t) { 1 } }\n" + T)],
        [group: G, name: "a non-empty t.name's subscript is defined", ok: true,
         src: tc("class C { @Requires({ t != null && t.name != null && t.name.length() > 0 }) @Ensures({ t.name[0] == t.name[0] }) static int f(T t) { 1 } }\n" + T)],
        [group: G, name: "a literal's subscript in range is defined", ok: true,
         src: tc("class C { @Requires({ i >= -3 && i < 3 }) @Ensures({ 'abc'[i] == 'abc'[i] }) static int f(int i) { 1 } }")],
        [group: G, name: "a precondition's s.trim().charAt(0) filters: the trimmed string is non-empty", ok: true,
         src: tc("class C { @Requires({ s != null && s.trim().charAt(0) == ('x' as char) }) @Ensures({ result > 0 }) static int f(String s) { s.trim().length() } }")],
        // ---- a receiver's array field ----
        [group: G, name: "a postcondition's t.a[0] on a maybe-empty array field is refused", expect: [THROWS, '0 < t.a.length'],
         src: tc("class C { @Requires({ t != null && t.a != null }) @Ensures({ t.a[0] == t.a[0] }) static int f(T t) { 1 } }\n" + T)],
        [group: G, name: "a precondition's t.a[0] filters: the array field is non-empty", ok: true,
         src: tc("class C { @Requires({ t != null && t.a != null && t.a[0] > 0 }) @Ensures({ result > 0 }) static int f(T t) { t.a.length } }\n" + T)],
        // ---- not a String: a list's subscript reads null past its end and owes nothing ----
        [group: G, name: "a receiver list's t.xs[0] owes nothing (it reads null past the end)", ok: true,
         src: tc("class C { @Requires({ t != null && t.xs != null }) @Ensures({ t.xs[0] == t.xs[0] }) static int f(T t) { 1 } }\n" + TL)],
        [group: G, name: "a list literal's subscript owes nothing", ok: true,
         src: tc("class C { @Ensures({ [1, 2, 3][1] == 2 }) static int f() { 1 } }")],
        // ---- indriya's division ----
        [group: G, name: "q.divide(3) read in metres is outside the fragment: indriya reads 1 / 3 as 34 digits", expect: 'outside fragment',
         src: uom('result * 3 == 1', 'Quantities.getQuantity(1, METRE).divide(3).to(METRE).getValue() as BigDecimal')],
        [group: G, name: "a BigDecimal value's q.divide(3).multiply(3) is outside the fragment: 1.4999…85 at runtime", expect: 'outside fragment',
         src: uom('result == 1.5', 'Quantities.getQuantity(1.5, METRE).divide(3).multiply(3).to(METRE).getValue() as BigDecimal')],
        [group: G, name: "a BigDecimal value's q.divide(3) is outside the fragment: 0.4999…95 at runtime", expect: 'outside fragment',
         src: uom('result == 0.5', 'Quantities.getQuantity(1.5, METRE).divide(3).to(METRE).getValue() as BigDecimal')],
        [group: G, name: "a quantity divisor of 3 s is outside the fragment too: 1.5 m / 3 s · 3 s isn't 1.5 m at runtime", expect: 'outside fragment',
         src: uomB('Quantities.getQuantity(1.5, METRE).divide(Quantities.getQuantity(3, SECOND)).multiply(Quantities.getQuantity(3, SECOND)) == Quantities.getQuantity(1.5, METRE)')],
        [group: G, name: "a reciprocal past 34 digits is outside the fragment: 1.5 m / 2^49 · 2^49 is 1.4999…96", expect: 'outside fragment',
         src: uom('result == 1.5', 'Quantities.getQuantity(1.5, METRE).divide(562949953421312).multiply(562949953421312).to(METRE).getValue() as BigDecimal')],
        [group: G, name: "a reciprocal of 34 digits is exact: 1.5 m / 2^48 · 2^48 is 1.5", ok: true,
         src: uom('result == 1.5', 'Quantities.getQuantity(1.5, METRE).divide(281474976710656).multiply(281474976710656).to(METRE).getValue() as BigDecimal')],
        [group: G, name: "a terminating divisor stays exact: 10 km / 4 is 2500 m", ok: true,
         src: uom('result == 2500', 'Quantities.getQuantity(10, KILO(METRE)).divide(4).to(METRE).getValue() as BigDecimal')],
        [group: G, name: "a terminating quantity divisor stays exact: 1.5 m / 2 s · 2 s is 1.5 m", ok: true,
         src: uomB('Quantities.getQuantity(1.5, METRE).divide(Quantities.getQuantity(2, SECOND)).multiply(Quantities.getQuantity(2, SECOND)) == Quantities.getQuantity(1.5, METRE)')],
        [group: G, name: "a terminating divisor's wrong value is refuted", expect: 'Cannot prove postcondition',
         src: uom('result == 2400', 'Quantities.getQuantity(10, KILO(METRE)).divide(4).to(METRE).getValue() as BigDecimal')],
    ]
}
