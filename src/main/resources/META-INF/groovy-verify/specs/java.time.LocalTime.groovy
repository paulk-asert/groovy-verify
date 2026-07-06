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

// External-specification skeleton (Phase 220): trusted contracts for java.time.LocalTime —
// receiver-independent range facts on immutable value getters.
package java.time

import groovy.contracts.Ensures
import groovy.transform.Pure

class LocalTime {

    @Pure
    @Ensures({ 0 <= result && result <= 23 })
    int getHour() {}

    @Pure
    @Ensures({ 0 <= result && result <= 59 })
    int getMinute() {}

    @Pure
    @Ensures({ 0 <= result && result <= 59 })
    int getSecond() {}
}
