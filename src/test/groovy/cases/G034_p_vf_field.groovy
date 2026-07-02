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

/** 'P-vf-field' — 7 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G034_p_vf_field {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Field self-increment / const-write in a body, tracked in SSA, checked against an assert (true proves, false refutes).'

    static final List<Map> CASES = [
        // Value-flow SSA versioning of an Int field/param write (fix b). A *bare* write to a field/param reuses
        // that name's entry symbol; as a plain `name == rhs` binding `tail = tail + 1` threads the self-
        // contradictory `tail == tail + 1` (UNSAT) so every downstream obligation discharged *vacuously and
        // silently*. Now the write is replayed as an SSA *versioning* step (fresh symbol for the post-write value),
        // so obligations are really discharged: a false assert REFUTES (not a silent pass, not a loud skip)…
        [group: 'P-vf-field', name: 'field self-increment then false assert refutes', expect: 'Assertion may not hold',
         src: tc('''class Buffer {
                       int tail
                       @Requires({ tail == 0 })
                       void m() { tail = tail + 1; assert tail == 0 }
                   }''')],
        // …and the corresponding TRUE assert PROVES — real discharge, not a skip (tail becomes 1).
        [group: 'P-vf-field', name: 'field self-increment then true assert proves', ok: true,
         src: tc('''class Buffer {
                       int tail
                       @Requires({ tail == 0 })
                       void m() { tail = tail + 1; assert tail == 1 }
                   }''')],
        // Const-write: tail becomes 5, so `tail == 99` refutes (was the vacuous `tail==0 ∧ tail==5` silent pass).
        [group: 'P-vf-field', name: 'field const-write false assert refutes', expect: 'Assertion may not hold',
         src: tc('''class Buffer {
                       int tail
                       @Requires({ tail == 0 })
                       void m() { tail = 5; assert tail == 99 }
                   }''')],
        // Parameter write is versioned the same way: x becomes 5, so `x == 999` refutes, `x == 5` proves.
        [group: 'P-vf-field', name: 'param reassignment false assert refutes', expect: 'Assertion may not hold',
         src: tc('''class C {
                       @Requires({ x == 0 })
                       static void m(int x) { x = 5; assert x == 999 }
                   }''')],
        [group: 'P-vf-field', name: 'param reassignment true assert proves', ok: true,
         src: tc('''class C {
                       @Requires({ x == 0 })
                       static void m(int x) { x = 5; assert x == 5 }
                   }''')],
        // Boundary: a NON-Int field write isn't versioned — it stays a loud "outside the value-flow fragment"
        // skip (sound, honest) rather than risking a sort-mismatched fresh symbol.
        [group: 'P-vf-field', name: 'non-Int field write stays a loud skip', expect: 'Skipped assertion safety check',
         src: tc('''class Buffer {
                       String tag
                       @Requires({ tag == 'a' })
                       void m() { tag = 'b'; assert tag == 'a' }
                   }''')],
        // Surgical: a LOCAL single-assignment is still on the value-flow path — the assert is really discharged.
        [group: 'P-vf-field', name: 'local single-assignment assert still proven (not over-skipped)', ok: true,
         src: tc('''class C {
                       static void m() { int x = 1; assert x == 1 }
                   }''')],
    ]
}
