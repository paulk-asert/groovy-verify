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

import groovy.concurrent.AsyncChannel

/**
 * Phase 259 — verification GHOSTS on channels, as Groovy extension methods so a spec closure type-checks.
 *
 * {@code c.taken} names the elements the enclosing loop has TAKEN from channel {@code c} so far — the
 * loop's taken-ghost of Phase 258 ({@code c$taken}): what a consumer loop has received from a stream it
 * reads from a cycle partner, or what an ALT loop has dequeued from one of its branches. It is a list a
 * loop {@code @Invariant} may quantify over ({@code Forall.range(0, i, { int k -> c.taken[k] == 2 * k + 1 })})
 * — the fact a request–reply or token-ring closed form needs and no local carries. It exists at
 * verification time only: the checker rewrites it to the ghost, and executing it is an error.
 */
class ChannelGhosts {
    static <T> List<T> getTaken(AsyncChannel<T> self) {
        throw new UnsupportedOperationException(
            "'taken' is a verification ghost — the elements the enclosing loop has taken from the channel — " +
            'for @Invariant closures the checker discharges at compile time; it has no runtime value')
    }
}
