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

/** 'P200 two-arg trace' — 5 case(s). Split per-group from the original VerifyHarness tables; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G275_p200_two_arg_trace {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'The 2-ary apply: BiFunction<Integer,Integer,Integer>.apply(a, b) — and its cs(i, r) SAM shorthand in contracts — models as a two-argument UF apply2$<name>, making the time-by-process trace state of a symbolic-N system expressible (the Phase-173 move one arity up). The payoff is the full-system frame lemma: recursion over a window whose per-step hypothesis is a NESTED every (all N processes framed at each step) concludes any single cell is unchanged end-to-end; a hole in the frame refutes, a wrong-cell claim refutes.'

    /** Runtime-rung tier (declared, not inferred — Phase 196): why this group's contracts aren't grid-run. */
    static final String RUNG_TIER = 'C — abstract-carrier laws: higher-order/monadic shapes beyond the grid'

    static final String BIFN = 'import java.util.function.BiFunction\n'

    static final List<Map> CASES = [

        // ---------- Phase 200: the 2-ary apply — time-by-process trace state cs(i, r) ----------
        // Congruence: two reads of the same cell are the same term (the UF foundation, 2-ary).
        [group: 'P200 two-arg trace', name: 'two-argument apply congruence', ok: true,
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class TwoArgBasic {
                        @Requires({ csT != null && csT.apply(i, r) == 1 })
                        @Ensures({ csT.apply(i, r) == 1 })
                        static void probe(BiFunction<Integer,Integer,Integer> csT, int i, int r) {}
                    }'''],
        // The SAM call-operator shorthand in a contract: cs(i, r) normalises to cs.apply(i, r).
        [group: 'P200 two-arg trace', name: 'cs(i, r) shorthand normalises in contracts', ok: true,
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class TwoArgSugar {
                        @Requires({ cs != null && cs(i, r) == 2 })
                        @Ensures({ cs.apply(i, r) == 2 })
                        static void probe(BiFunction<Integer,Integer,Integer> cs, int i, int r) {}
                    }'''],
        // THE PAYOFF — the full-system frame lemma (GetNextStep over the whole state): recursion over the
        // time window, each step's hypothesis a NESTED every (all N processes unchanged at step i);
        // conclusion: any single cell (p's state) is unchanged end-to-end. This is the shape the
        // step-implication-as-theorem construction reads its holder facts through.
        [group: 'P200 two-arg trace', name: 'full-system frame lemma over cs(i, r)', ok: true,
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class SystemFrame {
                        @Requires({ cs != null && n <= u && 0 <= p && p < N &&
                            (n..<u).every { int i -> (0..<N).every { int r -> cs.apply(i + 1, r) == cs.apply(i, r) } } })
                        @Ensures({ cs.apply(u, p) == cs.apply(n, p) })
                        @Decreases({ u - n })
                        static void frameAll(BiFunction<Integer,Integer,Integer> cs, int N, int n, int u, int p) {
                            if (n < u) frameAll(cs, N, n + 1, u, p)
                        }
                    }'''],
        // Teeth: a hole in the frame — the per-step hypothesis only covers processes below p — and the
        // end-to-end conclusion for p refutes.
        [group: 'P200 two-arg trace', name: 'frame with a hole refutes', expect: 'Cannot prove postcondition',
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class SystemFrameHole {
                        @Requires({ cs != null && n <= u && 0 <= p && p < N &&
                            (n..<u).every { int i -> (0..<p).every { int r -> cs.apply(i + 1, r) == cs.apply(i, r) } } })
                        @Ensures({ cs.apply(u, p) == cs.apply(n, p) })
                        @Decreases({ u - n })
                        static void frameAll(BiFunction<Integer,Integer,Integer> cs, int N, int n, int u, int p) {
                            if (n < u) frameAll(cs, N, n + 1, u, p)
                        }
                    }'''],
        // Teeth: congruence is not confusion — different cells are independent, so claiming another
        // cell's value from one cell's fact refutes.
        [group: 'P200 two-arg trace', name: 'distinct cells stay independent', expect: 'Cannot prove postcondition',
         src: HDR + BIFN + "@TypeChecked(extensions = 'verification.VerifyChecker')\n" +
              '''class TwoArgDistinct {
                        @Requires({ csT != null && csT.apply(0, 0) == 1 })
                        @Ensures({ csT.apply(0, 1) == 1 })
                        static void probe(BiFunction<Integer,Integer,Integer> csT) {}
                    }'''],
    ]
}
