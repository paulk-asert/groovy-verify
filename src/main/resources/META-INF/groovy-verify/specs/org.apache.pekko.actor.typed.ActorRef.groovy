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
// External-specification skeleton (Phase 538, shipped by PekkoPack): a tell queues the message and changes nothing the
// sender reads — a tell to self is handled after the current handler returns, never inside it — and a null message
// throws at the call (measured on Pekko 2.0.0: org.apache.pekko.actor.InvalidMessageException, PekkoSemanticsTest).
package org.apache.pekko.actor.typed

import groovy.contracts.ThrowsIf
import groovy.transform.Pure

class ActorRef {
    @Pure
    @ThrowsIf(value = { msg == null }, exception = RuntimeException, woven = false, direct = false)
    void tell(Object msg) {}
}
