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
 * Phase 284 — a DECLARED shared send end: JCSP's {@code any2one}, many writers and one reader.
 *
 * <p>By default a channel is point-to-point — one live process per end — and a second sender is refused
 * (Phase 241), because the FIFO per-element model rests on that discipline: the k-th send is the k-th
 * receive. Sharing is opt-in and must be WRITTEN, never inferred from the code: inferring it would turn
 * the main value of the linearity rule — catching sharing nobody intended — into a silent weakening.
 *
 * <p>What the declaration costs: the channel leaves the positional model, loudly. Nothing is claimed about
 * which element a given receive returns, or the order elements arrive in. What it keeps: the element
 * CONTRACT (Phase 242) still holds, because every sender must satisfy it; and deadlock-freedom still holds,
 * with a receive waiting on the disjunction of the sends rather than on one particular send.
 */
@Retention(RetentionPolicy.SOURCE)
@Target([ElementType.LOCAL_VARIABLE, ElementType.FIELD, ElementType.PARAMETER])
@Documented
@interface SharedSend {
}
