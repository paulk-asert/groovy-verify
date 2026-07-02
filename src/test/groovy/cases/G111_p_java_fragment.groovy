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

/** 'P-java-fragment' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G111_p_java_fragment {

    static final List<Map> CASES = [
        // Verifying a Java algorithm as Groovy. Java is largely a syntactic subset of Groovy, so a typical
        // integer/array algorithm — semicolons, C-style `for`, typed locals, `return`, `new int[]{…}` — parses
        // and verifies unchanged once the `@TypeChecked(extensions)` + contract annotations are added. The two
        // gotchas below are the developer's tells, and both are caught at COMPILE time (never a silent miscompile).
        // The honest counterpoint: the verifier only ever applies GROOVY semantics — it has no model of Java
        // *intent*, so a divergence that Groovy's own typing tolerates is proved (its Groovy meaning), not flagged.
        // `==` is Groovy value-equality (`.equals`): two equal Strings verify `result == true` SILENTLY, where a
        // Java author meaning reference-equality would have meant something else. The lesson is to read it as Groovy.
        [group: 'P-java-fragment', name: 'object == is Groovy value-equality, proved silently (not Java ==)', ok: true,
         src: tc('class C { @Requires({ a == "x" && b == "x" }) @Ensures({ result == true }) static boolean eq(String a, String b) { return a == b; } }')],
        [group: 'P-java-fragment', name: 'java-style max algorithm verifies', ok: true,
         src: tc('''class C {
             @Requires({ a != null && a.length > 0 })
             @Ensures({ result >= a[0] })
             static int max(int[] a) {
                 int m = a[0];
                 @Invariant({ m >= a[0] && i >= 1 && i <= a.length })
                 @Decreases({ a.length - i })
                 for (int i = 1; i < a.length; i++) {
                     if (a[i] > m) {
                         m = a[i];
                     }
                 }
                 return m;
             }
         }''')],
        // Gotcha 1 — Groovy `/` is BigDecimal ("true") division, not Java integer division; feeding it to an int
        // (assign / return / index) is a hard @TypeChecked error, so the fix (`.intdiv(2)`) is forced, not guessed.
        [group: 'P-java-fragment', name: 'integer division slash is a BigDecimal type error (use intdiv)', expect: 'BigDecimal',
         src: tc('class C { @Ensures({ result == x.intdiv(2) }) static int half(int x) { return x / 2; } }')],
        // Gotcha 2 — the Java array initializer `new int[]{…}` works; the *brace-only* form `{…}` is a Groovy
        // closure, so it doesn't parse — use `[…]` (a Groovy list coerces to the array) or `new int[]{…}`.
        [group: 'P-java-fragment', name: 'java array initializer new int[]{} verifies', ok: true,
         src: tc('class C { @Ensures({ result == 10 }) static int first() { int[] a = new int[]{10, 20, 30}; return a[0]; } }')],
        [group: 'P-java-fragment', name: 'bare brace array initializer does not parse (use a list)', expect: 'Unexpected input',
         src: tc('class C { static int first() { int[] a = {10, 20, 30}; return a[0]; } }')],
    ]
}
