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
package cases

import static cases.CaseDsl.*

/** 'P-call-frame' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G035_p_call_frame {

    static final List<Map> CASES = [
        // P-rg-guarantee: with fix (b), the per-segment GUARANTEE assertion — a two-state assert over a mutated
        // Int field (`int t = tail; …; assert <relate t and tail>`) — is really discharged, standalone and after
        // a rely-step call; violations refute (sound, not vacuous). This is the assert the sidebar marks `gCons`.
        // P-call-frame: the value-flow pass now gives a standalone @Modifies/@Ensures *call* the same caller-side
        // framing the postcondition path has — it havocs the callee's frame and assumes its @Ensures (was a silent
        // no-op). Havoc: a rely that does NOT pin head leaves it unknown after the call, so `a == b` can't prove.
        [group: 'P-call-frame', name: 'modifies call havocs an un-pinned field', expect: 'Assertion may not hold',
         src: tc('''class Buffer {
                       int head
                       int tail
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ old.tail <= tail })
                       void relyConsumer() {}
                       void step() { int a = head; relyConsumer(); int b = head; assert a == b }
                   }''')],
        // The rely's @Ensures is assumed: head < tail is re-established across the rely-step (head pinned, tail grew).
        [group: 'P-call-frame', name: 'rely ensures re-establishes obligation', ok: true,
         src: tc('''class Buffer {
                       int head
                       int tail
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ head == old.head && old.tail <= tail })
                       void relyConsumer() {}
                       @Requires({ head < tail })
                       void step() { relyConsumer(); assert head < tail }
                   }''')],
        // Soundness: drop the head-preserving conjunct from the rely → head < tail no longer survives → refutes.
        [group: 'P-call-frame', name: 'weak rely no longer re-establishes obligation', expect: 'Assertion may not hold',
         src: tc('''class Buffer {
                       int head
                       int tail
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ old.tail <= tail })
                       void relyConsumer() {}
                       @Requires({ head < tail })
                       void step() { relyConsumer(); assert head < tail }
                   }''')],
        // Capstone: a full hand-instrumented consumer segment now checks end-to-end in one pass — the rely-step
        // havocs+assumes (head < tail survives), the field write `head++` is SSA-versioned, and BOTH the
        // in-segment obligation (head <= tail) and the guarantee (tail unchanged) are discharged.
        [group: 'P-call-frame', name: 'full rely/guarantee consumer segment checks', ok: true,
         src: tc('''class Buffer {
                       int head
                       int tail
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ head == old.head && old.tail <= tail })
                       void relyConsumer() {}
                       @Requires({ head < tail })
                       @Modifies({ [this.head, this.tail] })
                       void step() {
                           relyConsumer()
                           int t = tail
                           head = head + 1
                           assert head <= tail
                           assert tail == t
                       }
                   }''')],
    ]
}
