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

/** 'README counter' — 1 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G169_readme_counter {

    static final List<Map> CASES = [

        // README Counter example — confirm the constructor-refute diagnostic shape used in docs.
        [group: 'README counter', name: 'Counter without @Requires refutes at construction',
         expect: 'Cannot prove class invariant',
         src: tc('''@groovy.contracts.Invariant({ count >= 0 && count <= max })
                    class Counter {
                        int count, max
                        Counter(int m) { max = m }
                        @Requires({ count < max })
                        void increment() { count = count + 1 }
                    }''')],
    ]
}
