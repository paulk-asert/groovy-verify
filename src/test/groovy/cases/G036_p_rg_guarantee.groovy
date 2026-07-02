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

/** 'P-rg-guarantee' — 4 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G036_p_rg_guarantee {

    static final List<Map> CASES = [
        [group: 'P-rg-guarantee', name: 'standalone guarantee proves', ok: true,
         src: tc('''class Buffer {
                       int head
                       int tail
                       void step() { int t = tail; head = head + 1; assert tail == t }
                   }''')],
        [group: 'P-rg-guarantee', name: 'standalone guarantee violation refutes', expect: 'Assertion may not hold',
         src: tc('''class Buffer {
                       int head
                       int tail
                       void step() { int t = tail; tail = tail + 1; assert tail == t }
                   }''')],
        [group: 'P-rg-guarantee', name: 'guarantee after rely-call', ok: true,
         src: tc('''class Buffer {
                       int head
                       int tail
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ head == old.head && old.tail <= tail })
                       void relyConsumer() {}
                       void step() { relyConsumer(); int t = tail; head = head + 1; assert tail == t }
                   }''')],
        [group: 'P-rg-guarantee', name: 'guarantee after rely-call VIOLATION refutes (sound, not vacuous)', expect: 'Assertion may not hold',
         src: tc('''class Buffer {
                       int head
                       int tail
                       @Modifies({ [this.head, this.tail] })
                       @Ensures({ head == old.head && old.tail <= tail })
                       void relyConsumer() {}
                       void step() { relyConsumer(); int t = tail; tail = tail + 1; assert tail == t }
                   }''')],
    ]
}
