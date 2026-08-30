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
 * Phase 266 — a MULTI-HOP service bound: once an element is next in line at every hop, it travels from
 * channel {@code from} to channel {@code to} within {@code value} service steps. Each hop is a process
 * that consumes the one channel and produces the next: a plain stage forwards its head element in ONE
 * iteration; a held {@code fair()} ALT takes a ready branch within k selects (its branch count, Phase
 * 265's arithmetic); a guarded reply leaves on its own branch's reply channel at the same cost. The
 * checker sums the hops along every path and certifies {@code value >=} the worst; an unbounded hop
 * (priority, a fresh {@code fair()}, {@code random()}, the racing select) refutes with its own reason.
 * The bound is the SERVICE bound — head-of-line latency; queueing behind earlier elements is not claimed.
 */
@Retention(RetentionPolicy.SOURCE)
@Target([ElementType.METHOD])
@Documented
@interface DeliveredWithin {
    int value()
    String from()
    String to()
}
