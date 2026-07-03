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

/** 'P209 metaprogramming' — 6 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G284_p209_metaprogramming {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Runtime metaprogramming, statically modelled (the MetaProgrammingPack, experimental): a statically-visible ExpandoMetaClass registration in the same class (Integer.metaClass.getFizzBuzz = {...} or an operator method Integer.metaClass.multiply = { String s -> ... }) is (a) TYPED by the pack\'s STC-companion half — the registration write, delegate arithmetic inside the closure, and the use sites all resolve under @TypeChecked — and (b) MODELLED by inlining the registered closure at each use site (delegate -> receiver, param -> argument) in the String sort, with out-of-sort arms (the getter\'s bare delegate) as a sound opaque per-receiver value. The blog\'s emoji-FizzBuzz metaclass examples verify against exact specs. Teeth: a wrong spec refutes; a claim resting on the opaque arm refuses to prove; without a visible registration the code stays a compile error — the gate is evidence-backed, not a dynamic-Groovy on-switch.'

    static final List<Map> CASES = [

        // ---------- Phase 209: the blog's metaclass FizzBuzz, proved ----------
        // Operator overload by metaclass: Integer.multiply(String) selects the emoji exactly when the
        // remainder is zero. Spec note: `n % 3 == 0 && n % 5 == 0` rather than `n % 15 == 0` — the
        // divisibility equivalence 15|n <=> (3|n && 5|n) entangled with the seq goal is a solver timeout.
        [group: 'P209 metaprogramming', name: 'metaclass multiply: emoji selection proves', ok: true,
         src: tc('''class C {
                       static {
                           Integer.metaClass.multiply = { String s -> delegate == 0 ? s : '' }
                       }
                       @Ensures({ result == (n % 3 == 0 && n % 5 == 0 ? '🥤🐝' : n % 3 == 0 ? '🥤' : n % 5 == 0 ? '🐝' : '') })
                       static String emoji(int n) { (n % 3) * '🥤' + (n % 5) * '🐝' }
                   }''')],
        [group: 'P209 metaprogramming', name: 'metaclass multiply: swapped emojis refute', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       static {
                           Integer.metaClass.multiply = { String s -> delegate == 0 ? s : '' }
                       }
                       @Ensures({ result == (n % 3 == 0 && n % 5 == 0 ? '🥤🐝' : n % 3 == 0 ? '🐝' : n % 5 == 0 ? '🥤' : '') })
                       static String emoji(int n) { (n % 3) * '🥤' + (n % 5) * '🐝' }
                   }''')],
        // The metaclass property: every Integer answers for itself. The bare-`delegate` arm is modelled
        // as an opaque value, so the spec is scoped to the String branches by the precondition.
        [group: 'P209 metaprogramming', name: 'metaclass getter: the numbers answer for themselves', ok: true,
         src: tc('''class C {
                       static {
                           Integer.metaClass.getFizzBuzz = { ->
                               (delegate % 15 == 0) ? '🥤🐝' :
                               (delegate % 3  == 0) ? '🥤'   :
                               (delegate % 5  == 0) ? '🐝'   : delegate
                           }
                       }
                       @Requires({ n % 3 == 0 || n % 5 == 0 })
                       @Ensures({ result == (n % 3 == 0 && n % 5 == 0 ? '🥤🐝' : n % 3 == 0 ? '🥤' : '🐝') })
                       static String fizz(int n) { n.fizzBuzz as String }
                   }''')],
        // Soundness of the opaque arm: WITHOUT the precondition, the claim rests on the bare-`delegate`
        // branch (e.g. n == 1), which is uninterpreted — it must refuse to prove, not vacuously pass.
        [group: 'P209 metaprogramming', name: 'claim resting on the opaque delegate arm refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                       static {
                           Integer.metaClass.getFizzBuzz = { ->
                               (delegate % 15 == 0) ? '🥤🐝' :
                               (delegate % 3  == 0) ? '🥤'   :
                               (delegate % 5  == 0) ? '🐝'   : delegate
                           }
                       }
                       @Requires({ n % 5 == 0 || n == 1 })
                       @Ensures({ result == (n % 3 == 0 && n % 5 == 0 ? '🥤🐝' : '🐝') })
                       static String fizz(int n) { n.fizzBuzz as String }
                   }''')],
        // The gate stays shut: no visible registration -> the dynamic reference is still a compile error.
        [group: 'P209 metaprogramming', name: 'unregistered dynamic property stays a compile error', expect: 'No such property: fizzBuzz',
         src: tc('''class C {
                       static Object fizz(int n) { n.fizzBuzz }
                   }''')],
        // Same-class visibility rule: a registration in ANOTHER class does not bless this one (v1).
        [group: 'P209 metaprogramming', name: 'cross-class registration does not bless (v1 rule)', expect: 'No such property: fizzBuzz',
         src: tc('''class C {
                       static Object fizz(int n) { n.fizzBuzz }
                   }
                   @groovy.transform.CompileDynamic
                   class D {
                       static {
                           Integer.metaClass.getFizzBuzz = { -> (delegate % 3 == 0) ? '🥤' : '' }
                       }
                   }''')],
    ]
}
