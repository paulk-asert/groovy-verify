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
 * 'P529 string subscript and rounded division' — two shapes that were outside the fragment in a contract and a body
 * alike. A String's subscript {@code s[i]} is the one-character String at {@code i}, counting from the end for a negative
 * {@code i} (it was read as an unrelated Int array's element sharing the name, so {@code s[0] == 'a'} couldn't
 * translate and {@code s[0] == s[0]} proved by identity on an empty string); in a contract its bounds, and
 * {@code s.charAt(i)}'s, are Phase 528 sites. Groovy's {@code /} with a non-terminating or symbolic divisor is the
 * rounded quotient: within {@code 0.5e-10 * (|q| + 1)} of the exact one, of its sign or zero, exact for an integer
 * quotient and never across an integer for integral operands, exact for a numeral divisor's quotient of at most 10
 * places (measured from {@code BigDecimalMath.divideImpl}, Groovy 6.0.0).
 */
class G570_p529_contract_string_index_division {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = "Phase 529: a String's subscript is its one-character String (a contract's s[i] and s.charAt(i) owe their bounds), and Groovy's / with a non-terminating or symbolic divisor is the rounded quotient, not a skip."

    static final String G = "P529 string subscript and rounded division"
    static final String THROWS = 'may throw rather than hold or fail'

    static final List<Map> CASES = [
        // ---- a String's subscript ----
        [group: G, name: "a body's s[0] compared with a literal", ok: true,
         src: tc("class C { @Requires({ s != null && s.startsWith('a') }) @Ensures({ result }) static boolean f(String s) { s[0] == 'a' } }")],
        [group: G, name: "a precondition's s[0] == 'a' makes the string non-empty", ok: true,
         src: tc("class C { @Requires({ s != null && s[0] == 'a' }) @Ensures({ result > 0 }) static int f(String s) { s.length() } }")],
        [group: G, name: "a precondition's s[0] == 'a' is the string's first character", ok: true,
         src: tc("class C { @Requires({ s != null && s[0] == 'a' }) @Ensures({ result }) static boolean f(String s) { s.startsWith('a') } }")],
        [group: G, name: "s[-1] is the last character: a contract's s[-1] is the body's s[s.length() - 1]", ok: true,
         src: tc("class C { @Requires({ s != null && s.length() > 0 }) @Ensures({ result == s[-1] }) static String f(String s) { s[s.length() - 1] } }")],
        [group: G, name: "the wrong character is refuted", expect: 'Cannot prove postcondition',
         src: tc("class C { @Requires({ s == 'ab' }) @Ensures({ result == 'a' }) static String f(String s) { s[1] } }")],
        [group: G, name: "a postcondition's s[0] on a maybe-empty string: the contract throws",
         expect: [THROWS, 'StringIndexOutOfBoundsException', '-s.length() <= 0 && 0 < s.length()', 'fails on: f("")'],
         src: tc("class C { @Requires({ s != null }) @Ensures({ s[0] == s[0] }) static int f(String s) { 1 } }")],
        [group: G, name: "a precondition's charAt(0) makes the string non-empty", ok: true,
         src: tc("class C { @Requires({ s != null && s.charAt(0) == ('a' as char) }) @Ensures({ result > 0 }) static int f(String s) { s.length() } }")],
        [group: G, name: "charAt doesn't count from the end: a postcondition's charAt(-1) is refused", expect: [THROWS, 'outside [0, s.length())'],
         src: tc("class C { @Requires({ s != null && s.length() > 0 }) @Ensures({ s.charAt(-1) == s.charAt(-1) }) static int f(String s) { 1 } }")],
        // ---- Groovy's rounded division ----
        [group: G, name: "a body's 10 / n is positive for a positive n", ok: true,
         src: tc('class C { @Requires({ n > 0 }) @Ensures({ result > 0 }) static BigDecimal f(int n) { 10 / n } }')],
        [group: G, name: "a body's 1 / 3 is positive", ok: true,
         src: tc('class C { @Ensures({ result > 0 }) static BigDecimal f() { 1 / 3 } }')],
        [group: G, name: "a precondition's 10 / n > 1 bounds n below 10 (an integer quotient is exact)", ok: true,
         src: tc('class C { @Requires({ n > 0 && 10 / n > 1 }) @Ensures({ result < 10 }) static int f(int n) { n } }')],
        [group: G, name: "an average stays in bounds", ok: true,
         src: tc('class C { @Requires({ n > 0 && s >= 0 && s <= 100 * n }) @Ensures({ result >= 0 && result <= 100 }) static BigDecimal f(int s, int n) { s / n } }')],
        [group: G, name: "one division of the same values is one value", ok: true,
         src: tc('class C { @Requires({ b != 0 }) @Ensures({ result == a / b }) static BigDecimal f(int a, int b) { a / b } }')],
        [group: G, name: "an integer quotient is exact: 10 / n is 2 at n == 5", ok: true,
         src: tc('class C { @Requires({ n == 5 }) @Ensures({ result == 2 }) static BigDecimal f(int n) { 10 / n } }')],
        [group: G, name: "a numeral divisor's short quotient is exact: x / 3 is 2 at x == 6", ok: true,
         src: tc('class C { @Requires({ x == 6 }) @Ensures({ result == 2 }) static BigDecimal f(int x) { x / 3 } }')],
        [group: G, name: "a numeral divisor's short decimal quotient is exact: 1.5 / 3 is 0.5", ok: true,
         src: tc('class C { @Requires({ x == 1.5 }) @Ensures({ result == 0.5 }) static BigDecimal f(BigDecimal x) { x / 3 } }')],
        [group: G, name: "a quotient keeps its sign: a non-negative over a positive is non-negative", ok: true,
         src: tc('class C { @Requires({ d > 0 && x >= 0 }) @Ensures({ x / d >= 0 }) static int f(BigDecimal x, BigDecimal d) { 1 } }')],
        [group: G, name: "a division assigned to a local is the rounded quotient", ok: true,
         src: tc('class C { @Requires({ n > 0 }) @Ensures({ result > 0 }) static BigDecimal f(int n) { BigDecimal y = 10 / n; y } }')],
        [group: G, name: "(1 / 3) * 3 == 1 is refuted (Groovy gives 0.9999999999)", expect: 'Cannot prove postcondition',
         src: tc('class C { @Ensures({ result }) static boolean f() { (1 / 3) * 3 == 1 } }')],
        [group: G, name: "a positive decimal quotient can round to zero: x / d > 0 is refuted", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ d > 0 && x > 0 }) @Ensures({ x / d > 0 }) static int f(BigDecimal x, BigDecimal d) { 1 } }')],
        [group: G, name: "a contract's / by a maybe-zero divisor owes it (Phase 528's site, now translated)", expect: [THROWS, 'n != 0'],
         src: tc('class C { @Ensures({ 10 / n == 10 / n }) static int f(int n) { 1 } }')],
        [group: G, name: "a body's / by a maybe-zero divisor is still its obligation", expect: 'ArithmeticException',
         src: tc('class C { static BigDecimal f(int n) { 10 / n } }')],
        // boundary: a symbolic divisor's exact non-integer quotient isn't derivable (over-strict, never unsound)
        [group: G, name: "boundary: 10 / n == 2.5 at n == 4 isn't derivable for a symbolic divisor", expect: 'Cannot prove postcondition',
         src: tc('class C { @Requires({ n == 4 }) @Ensures({ result == 2.5 }) static BigDecimal f(int n) { 10 / n } }')],
    ]
}
