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

/** 'P-rely-step' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G037_p_rely_step {

    static final List<Map> CASES = [
        // A rely-step is just a *framed assume*: havoc the shared frame (@Modifies), then assume a two-state
        // relation between old and new (@Ensures over `old`). So Phase 13's caller-side framing already lets us
        // model the rely/guarantee interleaving step in stock vocabulary — no `havoc`/`assume` primitive needed.
        // The empty body checks out precisely because a rely is reflexive (nothing changed ⊨ the relation).
        // This is the omitted-interleaving half of the README rely/guarantee sidebar, made concrete.
        [group: 'P-rely-step', name: 'rely-step (@Modifies+@Ensures) survives interleaving', ok: true,
         src: tc('''class Buffer {
                       int head
                       int tail
                       @Modifies({ [this.head, this.tail] })               // the havoc frame
                       @Ensures({ head == old.head && old.tail <= tail })  // the assumed rely (old ↦ at the call)
                       void relyConsumer() {}                              // models the environment, not real code

                       @Requires({ head < tail })
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ head < tail })                          // the read stays in-range across the step
                       void step() { relyConsumer() }
                   }''')],
        // Drop the load-bearing `head == old.head` conjunct: the producer could now move the read pointer past
        // tail, so `head < tail` no longer survives the rely-step — exactly the refutation the sidebar describes.
        [group: 'P-rely-step', name: 'weakened rely no longer protects the read', expect: 'Cannot prove postcondition',
         src: tc('''class Buffer {
                       int head
                       int tail
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ old.tail <= tail })                     // weakened: read pointer no longer pinned
                       void relyConsumer() {}

                       @Requires({ head < tail })
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ head < tail })
                       void step() { relyConsumer() }
                   }''')],
    ]
}
