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

/** 'P-inheritance' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G065_p_inheritance {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'A super.m() call assumes the parent\'s postcondition and must satisfy the parent\'s precondition.'

    static final List<Map> CASES = [
        // ---------- Inheritance: cross-method reasoning along the `extends` axis ----------
        // A `super.f(x)` call is treated like any contracted call: the parent's @Ensures is *assumed* for the
        // result and the parent's @Requires is *discharged* at the call site. So a child can build on the
        // parent's proven postcondition to establish a strengthened one of its own.
        [group: 'P-inheritance', name: 'super call assumes parent postcondition', ok: true,
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Base {
    @Requires({ x >= 0 })
    @Ensures({ result == x * 2 })
    int f(int x) { x + x }
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class Derived extends Base {
    @Requires({ x >= 0 })
    @Ensures({ result == x * 2 + 1 })
    int g(int x) { super.f(x) + 1 }
}
"""],
        // The parent's precondition is a real obligation at the `super` call: a child that calls `super.f(x)`
        // without establishing `x >= 0` is refuted with a counterexample.
        [group: 'P-inheritance', name: 'super call must satisfy parent precondition', ok: false, expect: 'Cannot prove precondition',
         src: HDR + """
@TypeChecked(extensions = 'verification.VerifyChecker')
class Base {
    @Requires({ x >= 0 })
    @Ensures({ result == x * 2 })
    int f(int x) { x + x }
}
@TypeChecked(extensions = 'verification.VerifyChecker')
class Derived extends Base {
    int g(int x) { super.f(x) + 1 }
}
"""],
    ]
}
