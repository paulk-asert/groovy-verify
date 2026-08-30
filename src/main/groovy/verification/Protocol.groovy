/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
package verification

import java.lang.annotation.Documented
import java.lang.annotation.ElementType
import java.lang.annotation.Retention
import java.lang.annotation.RetentionPolicy
import java.lang.annotation.Target

/**
 * Phase 263/269 — a SESSION TYPE for a method's channel network: a global protocol that the checker
 * projects onto each role and checks every process's control flow against. The primary surface is a
 * CLOSURE — plain Groovy, parsed by Groovy itself (labels are message names, {@code >>} points from
 * sender to receiver, command chains carry the combinators):
 * <pre>
 * {@literal @}Protocol({
 *     loop {
 *         request: client >> server      // a message is the channel it travels on
 *         reply:   server >> client
 *     }
 * })
 * </pre>
 * Items: {@code label: from >> to}, {@code loop { … }}, {@code choice(at: role) { … } or { … }} (every
 * branch of a choice at {@code role} begins with a message from {@code role}), {@code choice { … } or
 * { … }} (a MIXED choice — Phase 267's coherence check decides), and {@code par { … } and { … }}
 * (independent sub-sessions, channels disjoint). The closure is harvested and rendered to protocol text
 * before static type checking (its names are protocol vocabulary, not variables); the Scribble-flavoured
 * TEXT form remains as {@code text = '''…'''} with {@code ->} arrows and {@code choice at role}. Roles are
 * bound to processes (the main body, each {@code async} arm) by the channel ends they use.
 * Verification-time only.
 */
@Retention(RetentionPolicy.SOURCE)
@Target([ElementType.METHOD])
@Documented
@interface Protocol {
    /** The protocol as a Groovy closure (the primary form). */
    Class value() default Void
    /** The protocol as text (the Phase 263 form), for tools that carry protocols as strings. */
    String text() default ''
}
