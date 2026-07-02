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

/** 'P28 enum.values' — enum.values().length/.size() count folding across bodies and contracts; the
 *  shared import header and @TypeChecked wrappers (HDR, tc, …) come from {@link CaseDsl}. */
class G170_p28_enum_values {

    /** The one-line capability description for this group — harvested into catalog.json (see Harvester). */
    static final String DESCRIPTION = 'enum.values().length / .size() folds to the enum\'s value count — in bodies (encoder translate-time fold, both resolved and snapshot-unresolved receiver shapes) and in every contract position (method @Requires/@Ensures, loop @Invariant, class @Invariant — pre-folded by ContractNormalizer, Phase 183); a wrong count refutes.'

    static final List<Map> CASES = [

        // ---------- Phase 28: enum.values().length folds to a ground int ----------
        // Body context (post-resolution ClassExpression): the method returns the count, the
        // @Ensures matches the folded literal.
        [group: 'P28 enum.values', name: 'body returns Color.values().length, verifies', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Ensures({ result == 3 })
                        static int numColors() { Color.values().length }
                    }''')],
        // Soundness: wrong expected count refutes.
        [group: 'P28 enum.values', name: 'wrong count refuted',
         expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Ensures({ result == 4 })
                        static int numColors() { Color.values().length }
                    }''')],
        // .size() form folds the same way as .length — in both body and contract positions.
        [group: 'P28 enum.values', name: 'size() form folds in body', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Ensures({ result == 3 })
                        static int numColors() { Color.values().size() }
                    }''')],
        [group: 'P28 enum.values', name: 'size() form folds in contract', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ k < Color.values().size() })
                        @Ensures({ k <= 2 })
                        static int safe(int k) { k }
                    }''')],
        // Contract-side use (re-parsed VariableExpression receiver). Looks the enum up by name in
        // the enumDomainSizes map populated by VerifyChecker, folds to 3.
        [group: 'P28 enum.values', name: '@Requires uses folded count', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ k < Color.values().length })
                        @Ensures({ k <= 2 })
                        static int safe(int k) { k }
                    }''')],
        // Bounded iteration over the enum domain: the upper bound folds to a literal, so the
        // every-quantifier's range is concrete.
        [group: 'P28 enum.values', name: 'bounded iteration over enum domain', ok: true,
         src: tc('''class C {
                        enum Color { RED, BLUE, GREEN }
                        @Requires({ (0..<Color.values().length).every { it >= 0 } })
                        @Ensures({ result == 3 })
                        static int numColors() { Color.values().length }
                    }''')],
        // ---------- Phase 183: the fold as a ContractNormalizer rewrite, pinned in every contract position ----------
        // The re-parsed (VariableExpression-receiver) shape is now folded by ContractNormalizer before the encoder
        // sees it; the encoder keeps only the resolved (ClassExpression) shape for method bodies. These pin the two
        // positions that previously leaned on the encoder's unresolved branch: a LOOP @Invariant (normalised at
        // CONVERSION inside the transform's loop capture) and a CLASS @Invariant (normalised at classInvariantTexts).
        [group: 'P28 enum.values', name: 'values().length folds in a loop @Invariant', ok: true,
         src: tc('''class C {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ n >= 0 })
                        @Ensures({ result == State.values().length * n })
                        static int g(int n) {
                            int i = 0
                            int acc = 0
                            @Invariant({ 0 <= i && i <= n && acc == State.values().length * i })
                            @Decreases({ n - i })
                            while (i < n) { acc = acc + State.values().length; i = i + 1 }
                            return acc
                        }
                    }''')],
        // Teeth: the same loop claiming one more refutes — possible only if the invariant's count genuinely folded.
        [group: 'P28 enum.values', name: 'loop-@Invariant fold refutes a wrong claim', expect: 'Cannot prove postcondition',
         src: tc('''class C {
                        enum State { IDLE, RUNNING, DONE }
                        @Requires({ n >= 0 })
                        @Ensures({ result == State.values().length * n + 1 })
                        static int g(int n) {
                            int i = 0
                            int acc = 0
                            @Invariant({ 0 <= i && i <= n && acc == State.values().length * i })
                            @Decreases({ n - i })
                            while (i < n) { acc = acc + State.values().length; i = i + 1 }
                            return acc
                        }
                    }''')],
        // Class @Invariant position: the slot stays inside the enum's domain; the guarded mutator preserves it.
        [group: 'P28 enum.values', name: 'values().length folds in a class @Invariant', ok: true,
         src: tc('''@Invariant({ 0 <= slot && slot < State.values().length })
                    class Holder {
                        enum State { IDLE, RUNNING, DONE }
                        int slot
                        void set(int s) { if (0 <= s && s < State.values().length) slot = s }
                    }''')],
        // Teeth: drop the upper guard and the class invariant refutes (an unfolded count would loud-skip instead).
        [group: 'P28 enum.values', name: 'class-@Invariant fold refutes an unguarded mutator', expect: 'Cannot prove class invariant',
         src: tc('''@Invariant({ 0 <= slot && slot < State.values().length })
                    class Holder {
                        enum State { IDLE, RUNNING, DONE }
                        int slot
                        void set(int s) { if (0 <= s) slot = s }
                    }''')],
    ]
}
