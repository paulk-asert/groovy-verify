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

import groovy.contracts.ThrowsIf
import groovy.transform.TypeChecked

/**
 * The trusted-ledger part of the consumer smoke (compiled by {@code compileTrustedGroovy}): a
 * specification-only {@code @ThrowsIf} ({@code woven = false, direct = false}) is assumed without proof,
 * so it lands in the trusted-spec ledger. With {@code -PverifyTrust=report} CI asserts the compile prints
 * {@code trusted: [in-place @ThrowsIf] smoke.Trusted#parse …} and succeeds; with {@code -PverifyTrust=deny}
 * it asserts the compile fails AT the {@code @ThrowsIf} line (the site-anchored error). Without the
 * property this compiles cleanly, like any consumer code that relies on a documented third-party throw.
 */
@TypeChecked(extensions = 'verification.VerifyChecker')
class Trusted {
    @ThrowsIf(value = { s == null }, exception = NullPointerException, woven = false, direct = false)
    static Object parse(Object s) { helper(s) }

    static Object helper(Object s) { s }
}
