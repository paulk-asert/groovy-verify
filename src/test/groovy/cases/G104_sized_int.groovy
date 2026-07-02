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

/** 'sized int[]' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G104_sized_int {

    static final List<Map> CASES = [

        // ---------- Sized array allocation `new int[n]` (fresh, zero-filled) ----------
        // A `new int[n]` (ArrayExpression with a dimension size, no initializer) is a fresh array of length
        // n that Java zero-fills. Modelled through the size/array oracles: sizeOf == n, non-null, const-0
        // contents — so a length spec proves, an unwritten element reads 0, and a body store threads from
        // there. (Distinct from the fixed-arity `new int[]{…}` literal above, which is a factory.)
        [group: 'sized int[]', name: 'new int[n] return: result.length == n', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.length == n })
                        static int[] make(int n) { new int[n] }
                    }''')],
        [group: 'sized int[]', name: 'new int[n] zero-filled: unwritten element is 0', ok: true,
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        @Ensures({ result[0] == 0 })
                        static int[] make(int n) { new int[n] }
                    }''')],
        [group: 'sized int[]', name: 'build local: new int[1], store, return', ok: true,
         src: tc('''class C {
                        @Ensures({ result.length == 1 && result[0] == x })
                        static int[] singleton(int x) {
                            int[] r = new int[1]
                            r[0] = x
                            r
                        }
                    }''')],
        // Wrong length refutes — the size oracle pins n, not n+1.
        [group: 'sized int[]', name: 'new int[n]: wrong length refutes', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        @Requires({ n >= 0 })
                        @Ensures({ result.length == n + 1 })
                        static int[] make(int n) { new int[n] }
                    }''')],
        // Soundness anchor: a body store past the (symbolic) length refutes — the size oracle bounds stores.
        [group: 'sized int[]', name: 'new int[n] store out of bounds refutes', expect: 'IndexOutOfBounds',
         src: tc('''class C {
                        @Requires({ n >= 1 })
                        static int[] make(int n, int x) {
                            int[] r = new int[n]
                            r[5] = x
                            r
                        }
                    }''')],
    ]
}
