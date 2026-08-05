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
package smoke

import groovy.transform.TypeChecked
import groovy.contracts.Requires

/**
 * The must-verify half of the consumer smoke: two representative obligations that make Z3 actually
 * run during this compile — a {@code @Requires}-discharged divide and an early-exit-guarded deref
 * (Phase 233). If the extension fails to engage, load, or solve on the JDK 17 toolchain, this
 * compile fails and CI goes red.
 */
@TypeChecked(extensions = 'verification.VerifyChecker')
class Good {
    @Requires({ b != 0 })
    static int div(int a, int b) { a.intdiv(b) }

    static int guarded(String s) {
        if (s == null) return 0
        return s.length()
    }
}
