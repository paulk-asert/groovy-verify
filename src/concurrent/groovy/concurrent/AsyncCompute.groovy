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
package concurrent

import groovy.transform.CompileStatic
import groovy.transform.stc.POJO

/**
 * Groovy 6 async/await, the *safe* (pure-value) pattern groovy-verify proves sequentially — here run for real so
 * Lincheck can exercise the structural half the proof <i>assumes</i> (rung 3 of {@code examples/concurrency/README.md}).
 * Each {@code async { … }} closure returns a value and touches no shared state, so the result is deterministic
 * regardless of how the tasks are scheduled — which is exactly what the stress test below confirms on real threads.
 */
@CompileStatic
@POJO
class AsyncCompute {

    /** The bmc4j {@code compute}: await one task, then combine. Proven `(x+1)*2` (P153 'await an async value'). */
    static int compute(int x) {
        def fa = async { x + 1 }
        int a = await fa
        return a * 2
    }

    /** Fan out three independent tasks over the inputs, gather with {@code all}, combine — proven
     *  `(a+1)+(b+1)+(c+1)` (P153 'fan out, delay, gather, combine'). The three tasks run in parallel for real here. */
    static int safeGather(int a, int b, int c) {
        def t1 = async { a + 1 }
        def t2 = async { b + 1 }
        def t3 = async { c + 1 }
        def r = await(t1, t2, t3)
        return ((int) r[0]) + ((int) r[1]) + ((int) r[2])
    }
}
