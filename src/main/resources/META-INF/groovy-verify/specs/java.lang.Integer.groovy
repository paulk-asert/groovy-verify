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

// External-specification skeleton (Phase 217/222): trusted contracts for java.lang.Integer.
// parseInt ships as a ONE-DIRECTIONAL arm (exhaustive = false, Phase 222): `s == null` is a
// sufficient throw condition but not the whole story (malformed / out-of-range also throw, and
// those conditions are outside the fragment) — so the arm makes no exhaustiveness claim. What
// callers get is the normal-return contrapositive: parseInt(s) surviving proves s != null.
package java.lang

import groovy.contracts.Ensures
import groovy.contracts.Requires
import groovy.transform.Pure
import groovy.contracts.ThrowsIf

class Integer {

    @Pure
    @Ensures({ (a > 0 ==> result == 1) && (a == 0 ==> result == 0) && (a < 0 ==> result == -1) })
    static int signum(int a) {}

    // Exact (the implementation returns precisely -1/0/1), which comparator reasoning leans on.
    @Pure
    @Ensures({ (x < y ==> result == -1) && (x == y ==> result == 0) && (x > y ==> result == 1) })
    static int compare(int x, int y) {}

    @Pure
    @ThrowsIf(value = { s == null }, exception = NumberFormatException, woven = false, direct = false, exhaustive = false)
    static int parseInt(String s) {}
}
