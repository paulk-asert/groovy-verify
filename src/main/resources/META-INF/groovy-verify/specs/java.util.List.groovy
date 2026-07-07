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

// External-specification skeleton (Phase 230): trusted contracts for java.util.List — deliberately
// ONLY what the native list oracles do not already model exactly (size/get/getAt bounds/contains/
// isEmpty are native and better than any trusted spec; java.util.Map needs no skeleton at all —
// membership, cardinality and getOrDefault are native, and the keySet()/values() projections are
// outside the fragment). indexOf carries the receiver-STATE ensures shape, the String twin:
// `size()` is substituted onto the actual receiver at each consumption site.
package java.util

import groovy.contracts.Ensures
import groovy.transform.Pure

class List {

    @Pure
    @Ensures({ result >= -1 && result < size() })
    int indexOf(Object o) {}

    @Pure
    @Ensures({ result >= -1 && result < size() })
    int lastIndexOf(Object o) {}
}
