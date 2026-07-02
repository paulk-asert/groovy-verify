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

/** 'P-monadauto' — 2 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G220_p_monadauto {

    static final List<Map> CASES = [

        // Phase 136/137 (auto-synthesis) — @Monadic alone now carries the proof: all four laws (the three identity
        // laws plus associativity) are derived from the annotation and discharged, with NO hand-written lemmas.
        [group: 'P-monadauto', name: '@Monadic carrier: all laws auto-prove (no lemmas)', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Res {
                        final Object v
                        Res(Object v) { this.v = v }
                        @Requires({ f != null }) Res chain(java.util.function.Function f) { (Res) f.apply(v) }
                        @Requires({ f != null }) Res transform(java.util.function.Function f) { new Res(f.apply(v)) } }''')],
        // A @Monadic carrier outside the modellable shape (here, bind/map swapped — non-Identity) is left to the
        // annotation's own assertion: no synthesis, no false vouch, no noise (Maybe/Either/Stream land here too).
        [group: 'P-monadauto', name: '@Monadic carrier outside the modellable shape is left alone', ok: true,
         src: tc('''@groovy.transform.Monadic(bind = 'chain', map = 'transform')
                    class Bad {
                        final Object v
                        Bad(Object v) { this.v = v }
                        @Requires({ f != null }) Bad chain(java.util.function.Function f) { new Bad(f.apply(v)) }
                        @Requires({ f != null }) Bad transform(java.util.function.Function f) { (Bad) f.apply(v) } }''')],
    ]
}
