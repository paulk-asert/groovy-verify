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

// External-specification skeleton (Phase 221): trusted contracts for java.lang.String — deliberately
// ONLY what the native seq theory does not already model exactly (length/charAt/substring/startsWith
// etc. are native and better than any trusted spec). indexOf carries the receiver-STATE ensures shape:
// `length()` is substituted onto the actual receiver at each consumption site.
package java.lang

import groovy.contracts.Ensures
import groovy.transform.Pure

class String {

    @Pure
    @Ensures({ result >= -1 && result < length() })
    int indexOf(int ch) {}

    @Pure
    @Ensures({ result >= -1 && result < length() })
    int lastIndexOf(int ch) {}
}
