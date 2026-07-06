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

// External-specification skeleton: trusted contracts for java.lang.Long — the mechanical mirror of
// the Integer/Math int surface, via Long's own single-overload statics. (Math's long OVERLOADS also
// ship now — Phase 219's typed lookup disambiguation made same-arity overload pairs safe.)
package java.lang

import groovy.contracts.Ensures
import groovy.transform.Pure

class Long {

    @Pure
    @Ensures({ (a >= b ==> result == a) && (a < b ==> result == b) })
    static long max(long a, long b) {}

    @Pure
    @Ensures({ (a <= b ==> result == a) && (a > b ==> result == b) })
    static long min(long a, long b) {}

    @Pure
    @Ensures({ (x < y ==> result == -1) && (x == y ==> result == 0) && (x > y ==> result == 1) })
    static int compare(long x, long y) {}

    @Pure
    @Ensures({ (a > 0 ==> result == 1) && (a == 0 ==> result == 0) && (a < 0 ==> result == -1) })
    static int signum(long a) {}

    // The runtime WRAPS on overflow, so the math-int equality only holds in range — the same
    // guarded-ensures discipline as Math.addExact (an unguarded `result == a + b` would be a
    // false spec at the edges, and trusted-but-false is the one thing the registry must not ship).
    @Pure
    @Ensures({ (a + b <= Long.MAX_VALUE && a + b >= Long.MIN_VALUE) ==> result == a + b })
    static long sum(long a, long b) {}
}
