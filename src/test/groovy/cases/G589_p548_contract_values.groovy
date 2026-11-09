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

/**
 * 'P548 contract values' — Phase 548: a call's value its contract bounds but doesn't pin is no run's. With
 * `@Ensures({ result >= -5 })` on `idx`, `a[idx(o)]` read `fails on: run()`, though idx returns 0: the model picked
 * 806878739. The value is now an unknown (Phase 472's taint), kept only where the failure reads it, through the obligation
 * or a path condition (Phase 473's dependence test, the callee's contract asserted as a fact of every run). A failure that
 * doesn't read it keeps its call, as does a contract or a body that pins the value.
 */
class G589_p548_contract_values {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 548: a failure that reads a call\'s value its contract bounds but doesn\'t pin names no failing call; one that doesn\'t read it, or a pinned value, keeps its call.'

    static final String G = 'P548 contract values'

    static String r(String body) { tc("class R {\n${body}\n}") }

    static final String OOB = 'Possible IndexOutOfBoundsException'
    static final String BOUNDED = 'no failing call: the failure rests on what idx(…) returns, which the verifier knows only from its @Ensures, so no run is known to fail — strengthen the contract if the claim should follow from it'

    static final List<Map> CASES = [
        // Before: `counterexample: k = 806878739, …` and `fails on: run()`; idx returns 0.
        [group: G, name: 'an index a contract bounds but doesn\'t pin names no call', expect: [OOB, BOUNDED], refute: 'fails on',
         src: r('''    @Ensures({ result >= -5 })
    static int idx(Object o) { 0 }
    static int run() {
        int[] a = new int[3]
        int k = idx(new Object())
        a[k]
    }''')],
        [group: G, name: '… nor a path condition that reads it', expect: [OOB, BOUNDED], refute: 'fails on',
         src: r('''    @Ensures({ result >= -5 })
    static int idx(Object o) { 0 }
    static int run() {
        int[] a = new int[3]
        int k = idx(new Object())
        if (k > 100) return a[5]
        0
    }''')],
        [group: G, name: 'a failure that doesn\'t read the value keeps its call', expect: [OOB, 'fails on: run()'],
         src: r('''    @Ensures({ result >= -5 })
    static int idx(Object o) { 0 }
    static int run() {
        int[] a = new int[3]
        int k = idx(new Object())
        a[5]
    }''')],
        [group: G, name: 'a contract that pins the value keeps its call: every run gets it', expect: [OOB, 'fails on: run()'],
         src: r('''    @Ensures({ result == 7 })
    static int idx(Object o) { 7 }
    static int run() {
        int[] a = new int[3]
        int k = idx(new Object())
        a[k]
    }''')],
        [group: G, name: 'the bound the note asks for proves it', ok: true,
         src: r('''    @Ensures({ 0 <= result && result < 3 })
    static int idx(Object o) { 0 }
    static int run() {
        int[] a = new int[3]
        int k = idx(new Object())
        a[k]
    }''')],
    ]
}
