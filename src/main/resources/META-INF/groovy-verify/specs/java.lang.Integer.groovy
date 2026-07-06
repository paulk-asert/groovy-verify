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

// External-specification skeleton (Phase 217): trusted contracts for java.lang.Integer.
// (Integer.parseInt is deliberately absent: @ThrowsIf is an IFF contract, and parseInt's exact
// throw condition — malformed OR out of int range — is outside the fragment; a one-directional
// signals-style mode is recorded future work.)
package java.lang

import groovy.contracts.Ensures
import groovy.transform.Pure

class Integer {

    @Pure
    @Ensures({ (a > 0 ==> result == 1) && (a == 0 ==> result == 0) && (a < 0 ==> result == -1) })
    static int signum(int a) {}
}
