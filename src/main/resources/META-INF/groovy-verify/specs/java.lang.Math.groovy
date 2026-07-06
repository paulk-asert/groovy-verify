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

// External-specification skeleton (Phase 215): trusted contracts for java.lang.Math, consumed by
// groovy-verify's SpecRegistry. Parsed AST-only — never compiled, never executed. The JML analogue:
//   public normal_behavior requires a > Integer.MIN_VALUE; assignable \nothing;
//   ensures (a >= 0 ==> \result == a) && (a < 0 ==> \result == -a);
package java.lang

import groovy.contracts.Ensures
import groovy.contracts.Requires
import groovy.transform.Pure
import verification.ThrowsIf

class Math {

    // TOTAL spec (adopted from the OpenJML Specs corpus reading): no precondition — the wrap
    // behaviour at the one unrepresentable point is stated, not excluded. The classic abs bug
    // (`abs(x) >= 0` is FALSE at MIN_VALUE) refutes through this ensures.
    @Pure
    @Ensures({ (a >= 0 ==> result == a) &&
               (a < 0 && a != Integer.MIN_VALUE ==> result == -a) &&
               (a == Integer.MIN_VALUE ==> result == Integer.MIN_VALUE) })
    static int abs(int a) {}

    // The EXCEPTIONAL-contract sibling: same mathematical intent, the edge handled by a throw —
    // a true iff, the @ThrowsIf style (contrast the total spec above and binarySearch's true
    // @Requires in java.util.Arrays: the JDK's three contract styles on display).
    @Pure
    @ThrowsIf(value = { a == Integer.MIN_VALUE }, exception = ArithmeticException, trusted = true)
    @Ensures({ a != Integer.MIN_VALUE ==> ((a >= 0 ==> result == a) && (a < 0 ==> result == -a)) })
    static int absExact(int a) {}

    // Throws EXACTLY at the one unrepresentable point — a true iff, unlike most JDK exceptional
    // behaviour (trusted: the JDK's body is not ours to prove; the rung can still observe it).
    @Pure
    @ThrowsIf(value = { a == Integer.MIN_VALUE }, exception = ArithmeticException, trusted = true)
    @Ensures({ a != Integer.MIN_VALUE ==> result == -a })
    static int negateExact(int a) {}

    // Defined behaviour on a zero divisor is the throw itself (not a precondition) — another true iff.
    @Pure
    @ThrowsIf(value = { b == 0 }, exception = ArithmeticException, trusted = true)
    static int floorDiv(int a, int b) {}
}
