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
// External-specification skeleton (Phase 546, shipped by PekkoPack): ActorSystem.create(guardian, name) returns the
// system it starts, never null; an invalid name throws instead (held against Pekko 2.0.0 by SpecAuditTest). Starting a
// system changes nothing the caller reads. Thin by design: the overloads taking a setup, config or props aren't here.
package org.apache.pekko.actor.typed

import groovy.contracts.Ensures
import groovy.transform.Pure

class ActorSystem {
    @Pure
    @Ensures({ result != null })
    static Object create(Object guardian, String name) {}
}
