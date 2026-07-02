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

/** 'PL-truth' — 10 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G246_pl_truth {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Groovy truth in @Ensures({ result }): a non-empty String is truthy (verifies), empty is falsy (refutes).'

    static final List<Map> CASES = [

        // ----- Groovy truth in contract/assert position (non-boolean coerced as Groovy does) -----
        // An empty String is Groovy-false, so `@Ensures({ result })` returning "" must REFUTE (previously crashed).
        [group: 'PL-truth', name: 'truth: @Ensures({ result }) returning empty String refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C { @Ensures({ result }) static String h() { '' } }''')],
        // …returning a non-empty String verifies (Groovy-true).
        [group: 'PL-truth', name: 'truth: @Ensures({ result }) returning non-empty String verifies', ok: true,
         src: tc('''class C { @Ensures({ result }) static String h() { 'x' } }''')],
        // A bare-String assertion is Groovy truth: provable only when non-null ∧ non-empty.
        [group: 'PL-truth', name: 'truth: assert over a parameter String is unprovable (refuted)', expect: 'Assertion may not hold',
         src: tc('''class C { static void f(String s) { assert s } }''')],
        [group: 'PL-truth', name: 'truth: assert non-empty String literal verifies', ok: true,
         src: tc('''class C { static void f() { assert 'hi' } }''')],
        [group: 'PL-truth', name: 'truth: assert empty String literal refuted', expect: 'Assertion may not hold',
         src: tc('''class C { static void f() { assert '' } }''')],
        // Integral Groovy truth: assert x  ≡  x != 0.
        [group: 'PL-truth', name: 'truth: assert non-zero int literal verifies', ok: true,
         src: tc('''class C { static void f() { assert 7 } }''')],
        [group: 'PL-truth', name: 'truth: assert zero int literal refuted', expect: 'Assertion may not hold',
         src: tc('''class C { static void f() { assert 0 } }''')],
        // A bare-list precondition (`@Requires({ xs })`) is Groovy truth (non-null ∧ non-empty): it is *assumed*,
        // so a body relying on xs being non-empty verifies — and is no longer silently dropped.
        [group: 'PL-truth', name: 'truth: @Requires({ xs }) assumes the list is non-empty', ok: true,
         src: tc('''class C {
                        @Requires({ xs })
                        @Ensures({ result >= 1 })
                        static int sizeOf(List xs) { xs.size() }
                    }''')],
        // Soundness: without the truthy precondition, the list may be null/empty — here the very first failure is
        // the null dereference `xs.size()`, which `@Requires({ xs })` (non-null ∧ non-empty) is exactly what rules out.
        [group: 'PL-truth', name: 'truth: without @Requires the list may be null (deref refused)', expect: 'NullPointerException',
         src: tc('''class C {
                        @Ensures({ result >= 1 })
                        static int sizeOf(List xs) { xs.size() }
                    }''')],

        // A truthiness we don't model (a decimal's Groovy truth) is *loudly skipped* — no crash, no silent drop.
        [group: 'PL-truth', name: 'truth: unmodelled truthiness (double) skips loudly', expect: 'Skipped assertion safety check',
         src: tc('''class C { static void f(double d) { assert d } }''')],
    ]
}
