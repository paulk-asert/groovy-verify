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

// External-specification skeleton (Phase 218b): trusted contracts for java.util.Arrays.
// binarySearch carries the JDK's rarest contract style — a TRUE precondition: the javadoc says the
// result is UNDEFINED (not an exception!) if the array is not sorted. That is exactly what
// @Requires means, and the reversal-immune sortedness idiom spells it.
package java.util

import groovy.contracts.Requires

class Arrays {

    @Requires({ a != null && a.indices.every { it == 0 || a[it - 1] <= a[it] } })
    static int binarySearch(int[] a, int key) {}
}
