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
 * The §VII leak as a real interleaving bug — the publish-before-write inversion of {@link SpscBuffer}.
 * The runtime analogue of the {@code BufferLeak.cfg} TLA+ variant and of the checker's refutation at
 * {@code tail++}: it advances {@code tail} (pulls the slot into the consumable region) BEFORE the value
 * is written, so a consumer can read the slot in that window and observe an un-finalized value. Lincheck
 * finds the exact interleaving and reports it as a linearizability violation; jcstress observes it empirically —
 * the un-written {@code 0} surfaces across millions of stress runs (see {@code SpscBufferJCStress}). {@code @CompileStatic}
 * for the same reason as {@link SpscBuffer} — clean, dispatch-free bytecode for Lincheck and jcstress to run.
 */
@CompileStatic
@POJO
class SpscBufferLeaky {
    private final int[] items
    private final int capacity
    private volatile int head = 0
    private volatile int tail = 0

    SpscBufferLeaky(int capacity) {
        this.capacity = capacity
        this.items = new int[capacity]
    }

    boolean offer(int x) {
        int t = tail
        if (t - head == capacity) return false      // full
        tail = t + 1                                // BUG: publish the slot BEFORE writing it…
        items[t % capacity] = x                     // …a consumer can read the slot in this window
        true
    }

    Integer poll() {
        int h = head
        if (tail - h == 0) return null
        int v = items[h % capacity]
        head = h + 1
        v
    }
}
