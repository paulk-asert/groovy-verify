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

/**
 * The must-REFUTE half of the consumer smoke (compiled by {@code compileBadGroovy}, which CI
 * asserts fails): an unconstrained parameter deref, the checker's bread-and-butter refutation.
 * Expected diagnostic: {@code Possible NullPointerException} with the {@code oops(null)}
 * counterexample. This is what proves the extension ENGAGED — a smoke that only checked "the good
 * case compiled" would also pass with the checker silently inert.
 */
@TypeChecked(extensions = 'verification.VerifyChecker')
class Bad {
    static int oops(String s) { s.length() }
}
