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

/** 'P233 early exit' — 12 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G299_p233_early_exit {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'Early-exit guard narrowing: after `if (bad) return/throw`, the fall-through carries the guard\'s negation, so the idiomatic guard-then-use shape proves for null, bounds and divide alike.'

    static final List<Map> CASES = [

        // ===== Phase 233 — early-exit narrowing. Before this, path facts came only from the branches of an
        // `if`: the statements AFTER it were walked with the pre-`if` context, so the single most idiomatic
        // guard shape in Groovy refuted while its if/else twin verified. `alwaysExits` now decides whether an
        // arm can fall through; when one can't, reaching the continuation means the other arm was taken, so
        // that arm's guard is a true fact there. Sound: the exiting arm's writes are dead on this path.
        [group: 'P233 early exit', name: 'null guard: early return narrows the fall-through', ok: true,
         src: tc('''class C {
                        static int f(String s) {
                            if (s == null) return 0      // the exit makes `s != null` a fact below
                            return s.length()
                        } }''')],
        [group: 'P233 early exit', name: 'null guard: early throw narrows the same way', ok: true,
         src: tc('''class C {
                        static int f(String s) {
                            if (s == null) throw new IllegalArgumentException('s')
                            return s.length()
                        } }''')],
        // The if/else twin was ALWAYS provable — it is the control that shows the gap was the fall-through,
        // not the reasoning. Both spellings mean the same thing; now both verify.
        [group: 'P233 early exit', name: 'the if/else twin verifies too (the control)', ok: true,
         src: tc('''class C {
                        static int f(String s) {
                            if (s == null) { return 0 } else { return s.length() }
                        } }''')],
        [group: 'P233 early exit', name: 'bounds: early return discharges the index obligation', ok: true,
         src: tc('''class C {
                        static int g(int[] a, int i) {
                            if (a == null || i < 0 || i >= a.length) return -1
                            return a[i]
                        } }''')],
        [group: 'P233 early exit', name: 'divide: early return discharges the divisor obligation', ok: true,
         src: tc('''class C {
                        static int h(int a, int b) {
                            if (b == 0) return 0
                            return a.intdiv(b)
                        } }''')],
        [group: 'P233 early exit', name: 'stacked guards each narrow in turn', ok: true,
         src: tc('''class C {
                        static int g(int[] a, int i) {
                            if (a == null) return -1
                            if (i < 0) return -1
                            if (i >= a.length) return -1
                            return a[i]
                        } }''')],
        // Symmetric: when the ELSE arm is the one that can't fall through, the continuation carries the
        // POSITIVE guard instead.
        [group: 'P233 early exit', name: 'else-arm exits: the continuation carries the positive guard', ok: true,
         src: tc('''class C {
                        static int f(String s) {
                            if (s != null) { } else { return 0 }
                            return s.length()
                        } }''')],
        [group: 'P233 early exit', name: 'narrowed fact survives an intervening binding', ok: true,
         src: tc('''class C {
                        static int g(int[] a, int i) {
                            if (a == null || i < 0 || i >= a.length) return -1
                            int j = i
                            return a[j]
                        } }''')],

        // ----- Teeth. Narrowing ADDS a fact, so the risk is that it adds one that isn't true. Each of these
        // must still refute; together they pin that the fact is the right guard, on the right variable, in
        // the right polarity, and only when the arm genuinely exits.
        [group: 'P233 early exit', name: 'teeth: the guard is on a different variable', ok: false, expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static int f(String s, String t) {
                            if (s == null) return 0
                            return t.length()
                        } }''')],
        [group: 'P233 early exit', name: 'teeth: a half guard leaves the upper bound open', ok: false, expect: 'Possible IndexOutOfBoundsException',
         src: tc('''class C {
                        static int g(int[] a, int i) {
                            if (a == null || i < 0) return -1
                            return a[i]
                        } }''')],
        // The arm falls through, so there is no early exit and nothing to learn — narrowing must NOT fire.
        [group: 'P233 early exit', name: 'teeth: a non-exiting arm yields no narrowing', ok: false, expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static int f(String s) {
                            if (s == null) { int z = 1 }
                            return s.length()
                        } }''')],
        [group: 'P233 early exit', name: 'teeth: the guard negated the wrong way still refutes', ok: false, expect: 'Possible NullPointerException',
         src: tc('''class C {
                        static int f(String s) {
                            if (s != null) return 0
                            return s.length()
                        } }''')],
    ]
}
