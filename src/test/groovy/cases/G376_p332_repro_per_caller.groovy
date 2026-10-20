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
 * 'P332 a repro per caller' — the VC cache handed every identical VC the same CheckResult, which callers render in
 * place: shown() swaps the raw counterexample for its display form (keys read `.length`, the `?null` flags dropped)
 * and sets the failing call. A second identical VC, in the same method or another, rebuilt its repro from that
 * display map, so every array parameter came out as `new int[0]`. The cache now keeps a pristine verdict and hands
 * each caller its own copy (Z3Session.check).
 */
class G376_p332_repro_per_caller {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Phase 332 a repro per caller: two identical VCs, the read and the write of a[k], or the same obligation in two methods, each get a failing call built from the raw model, so an array parameter keeps its modelled size (f(new int[3], 3), not f(new int[0], 3)); and an array or list the model sizes past 1000 gets no failing call at all (Phase 331).'

    static final List<Map> CASES = [

        [group: 'P332 a repro per caller', name: 'the read and the write of one element share a VC but not a repro',
         expect: 'fails on: f(new int[3], 3)', refute: 'new int[0]',
         src: tc('''class C {
                        @Requires({ a != null && a.length == 3 && k >= 3 })
                        static void f(int[] a, int k) { a[k] = a[k] + 1 }
                    }''')],
        [group: 'P332 a repro per caller', name: 'two methods with the same obligation each get their own repro',
         expect: ['fails on: f(new int[3], 3)', 'fails on: g(new int[3], 3)'], refute: 'new int[0]',
         src: tc('''class C {
                        @Requires({ a != null && a.length == 3 && k >= 3 })
                        static int f(int[] a, int k) { a[k] }
                        @Requires({ a != null && a.length == 3 && k >= 3 })
                        static int g(int[] a, int k) { a[k] }
                    }''')],
        // Phase 331 — no repro for an array the model sizes past 1000 (rendering it element by element exhausted the heap).
        [group: 'P332 a repro per caller', name: 'an array sized past the repro cap gets no failing call',
         expect: 'a.length = 5000', refute: 'fails on:',
         src: tc('''class C {
                        @Requires({ a != null && a.length == 5000 && k >= 5000 })
                        static int f(int[] a, int k) { a[k] }
                    }''')],
    ]
}
